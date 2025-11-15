%% @hidden
-module(typerefl_trans).

-include("typerefl_int.hrl").

-compile({parse_transform, erlang_qq}).

%%-define(debug, true).

-ifdef(debug).
-define(log(A, B), io:format(user, A "~n", B)).
-else.
-define(log(A, B), ok).
-endif.

-export([parse_transform/2]).

-type local_tref() :: {Name :: atom(), Arity :: arity()}.

-type ast() :: term().

-record(typedef,
        { name    :: atom()
        , params  :: [atom()]
        , body    :: ast()
        , line    :: integer()
        }).

-type typedef() :: #typedef{}.

-type reflected_type() :: #typedef{}.

-record(s,
        { module                    :: atom()
        , local_types         = #{} :: #{local_tref() => typedef()}
        , reflected_types     = #{} :: #{local_tref() => reflected_type()}
        , custom_verif        = #{} :: #{local_tref() => ast()}
        , custom_from_string  = #{} :: #{local_tref() => ast()}
        , custom_pretty_print = #{} :: #{local_tref() => ast()}
        , type_surrogates     = #{} :: #{mfa() => {module(), atom()}}
        }).

-define(typerefl_module, typerefl).
-define(lazy_self_var, __TypeReflSelf).

-include_lib("erlang_qq/include/erlang_qq.hrl").

parse_transform(Forms0, Options) ->
  %%?log("Dump of the module AST:~n~p~n", [Forms0]),
  %% Collect module attributes:
  Ignored = ignored(Forms0),
  Typedefs0 = find_local_typedefs(Forms0),
  Typedefs = maps:without(Ignored, Typedefs0),
  TypesToReflect = types_to_reflect(Forms0),
  ?log("Types to reflect: ~p", [TypesToReflect]),
  Module = hd([M || {attribute, _, module, M} <- Forms0]),
  State0 = #s{ module      = Module
             , local_types = Typedefs
             },
  State1 = scan_custom_attributes(State0, Forms0),
  %% Perform type reflection:
  State = lists:foldl(fun refl_type/2, State1, TypesToReflect),
  %% export_type and export definitions are the same.
  Exports = TypesToReflect,
  Forms1 = add_attributes(Forms0, [ {export, Exports}
                                  , {export_type, Exports}
                                  ]),
  ReifiedTypes = maps:fold(fun(_, V, Acc) ->
                               maybe_add_doc(make_reflection_function(Module, State, V)) ++ Acc
                           end,
                           [],
                           State#s.reflected_types),
  ?log("Reified types:~n~p", [ReifiedTypes]),
  %% Append type reflections to the module definition:
  Forms2 = Forms1 ++ ReifiedTypes,
  Forms = case lists:member(warn_unused_import, Options) of
            true  -> remove_unused_imports(Forms2);
            false -> Forms2
          end,
  organize_attributes(Forms).

%% typerefl.hrl imports some functions, this part of the parse
%% transform removes the unused ones
remove_unused_imports([{attribute, Line, import, {?typerefl_module, Imports0}}|Rest]) ->
  Imports = maps:from_list([{I, 0} || I <- Imports0]),
  UsageCount = mark_used_imports(Imports, Rest),
  UsedImports = [Key || {Key, Val} <- maps:to_list(UsageCount), Val > 0],
  [{attribute, Line, import, {?typerefl_module, UsedImports}}
  |Rest];
remove_unused_imports([A|Rest]) ->
  [A|remove_unused_imports(Rest)];
remove_unused_imports([]) ->
  [].

mark_used_imports(Imports, Forms) ->
  lists:foldl(fun scan_forms/2, Imports, Forms).

scan_forms({function, _L, _F, _A, Clauses}, Map) ->
    lists:foldl(fun deep_scan/2, Map, Clauses);
scan_forms(_, Map) ->
    Map.

deep_scan({'fun', _L, {function, Name, Arity}}, Map) ->
    maybe_update_count({Name, Arity}, Map);
deep_scan({call, _L1, Call, Args}, Map0) ->
    case Call of
        {atom, _L2, Name} ->
            Map = maybe_update_count({Name, length(Args)}, Map0),
            deep_scan(Args, Map);
        _ ->
            deep_scan([Call | Args], Map0)
    end;
deep_scan(Other, Map) when is_list(Other) ->
    lists:foldl(fun deep_scan/2, Map, Other);
deep_scan(Other, Map) when is_tuple(Other) ->
    deep_scan(tuple_to_list(Other), Map);
deep_scan(_Other, Map) ->
    Map.

maybe_update_count(Key, Map) ->
  case Map of
    #{Key := Val} ->
      Map#{Key => Val + 1};
    _ ->
      Map
  end.

%% Remove all typerefl attributes, because they may appear in places
%% where erlang compiler doesn't expect them.
organize_attributes(Forms) ->
  lists:filter(fun({attribute, _Line, Attr, _Params}) when
                     Attr =:= reflect_type;
                     Attr =:= typerefl_verify;
                     Attr =:= typerefl_pretty_print;
                     Attr =:= typerefl_from_string;
                     Attr =:= typerefl_surrogate -> false;
                  (_) -> true
               end, Forms).

%% Reflect a local type
-spec refl_type(local_tref(), #s{}) -> #s{}.
refl_type(TRef, State0) ->
  #s{ reflected_types = RTypes0
    , local_types = LocalTypes
    } = State0,
  ?log("Reflecting type: ~p", [TRef]),
  %% Dirty hack to avoid infinite loops: prematurely mark current type
  %% as existent:
  State1 = State0#s{ reflected_types = RTypes0 #{TRef => in_progress}
                   },
  TypeDef = maps:get(TRef, LocalTypes),
  {ReflBody, State2} = do_refl_type(TRef, State1, TypeDef#typedef.body),
  RTypes1 = State2#s.reflected_types,
  Reflection = TypeDef#typedef{body = ReflBody},
  State2#s{reflected_types = RTypes1 #{TRef => Reflection}}.

%% Traverse AST of a type definition and produce a reflection
-spec do_refl_type(local_tref(), #s{}, ast()) -> {ast(), #s{}}.
do_refl_type(_, State, AST = {var, _Line, _Var}) ->
  {AST, State};
do_refl_type(_, State, AST = ?INT(_)) ->
  {AST, State};
do_refl_type(_, State, AST = ?ATOM(_)) ->
  {AST, State};
do_refl_type(_, State, {type, Line, map, any}) -> %% Maps are special
  {?rcall(?typerefl_module, map, []), State};
do_refl_type(Self, State0, {type, Line, map, Args}) -> %% Maps are special
  %% Separate diffetent kinds of map fields:
  Fuzzy0 = [{Key, Val} || {type, _, map_field_assoc, [Key, Val]} <- Args],
  Strict0 = [{Key, Val} || {type, _, map_field_exact, [Key, Val]} <- Args],
  %% Reflect nested fuzzy types:
  {Fuzzy1, State1} = lists:mapfoldl( fun({K0, V0}, S0) ->
                                         {K, S1} = do_refl_type(Self, S0, K0),
                                         {V, S} = do_refl_type(Self, S1, V0),
                                         {{K, V}, S}
                                     end
                                   , State0
                                   , Fuzzy0),
  %% Reflect nested strict types:
  {Strict1, State} = lists:mapfoldl( fun({K, V0}, S0) ->
                                         {V, S} = do_refl_type(Self, S0, V0),
                                         {{K, V}, S}
                                     end
                                   , State1
                                   , Strict0),
  %% Create field spec AST:
  Fuzzy = [?tuple([?atom(fuzzy), K, V]) || {K, V} <- Fuzzy1],
  Strict = [?tuple([?atom(strict), K, V]) || {K, V} <- Strict1],
  ?log("~p: Fuzzy fields: ~p", [Self, Fuzzy]),
  ?log("~p: Strict fields: ~p", [Self, Strict]),
  ArgAST = mk_literal_list(Line, Fuzzy ++ Strict),
  %% Create `typerefl:map/1' call and return:
  {?rcall(?typerefl_module, map, [ArgAST]), State};
do_refl_type(Self, State, {Qualifier, Line, Name, Args})
       when Qualifier =:= type; Qualifier =:= user_type ->
  do_refl_type_call(Self, State, Line, {Name, Args});
do_refl_type(Self, State, {remote_type, Line, CallSpec}) ->
  [?ATOM(Module), ?ATOM(Name), Args] = CallSpec,
  do_refl_type_call(Self, State, Line, {Module, Name, Args}).

do_refl_type_call(Parent, State, Line, {Function, Args}) ->
  do_refl_type_call(Parent, State, Line, {State#s.module, Function, Args});
do_refl_type_call(Parent, State0, Line, {Module, Function, Args0}) ->
  ?log("Reflecting type call: ~p", [{Module, Function, Args0}]),
  Local = Module =:= State0#s.module,
  State1 = if Local ->
               %% Another local type is refered here, it should be
               %% reflected too:
               TypeArity = case Args0 of
                             any ->
                               0;
                             L when is_list(L) ->
                               length(Args0)
                           end,
               maybe_refl_type({Function, TypeArity}, State0);
              true ->
               State0
           end,
  %% Type arguments are nested ASTs, traverse them:
  {Args, State} = transform_type_args(Parent, Line, State1, Function, Args0),
  AST = maybe_lazy_call(Parent, State, Line, {Module, Function, Args}),
  {AST, State}.

maybe_lazy_call(Parent, State = #s{type_surrogates = Surrogates}, Line, {Module0, Function0, Args}) ->
  %% Check if we need to substitute this type with a surrogate
  Arity = length(Args),
  {Module, Function} = maps:get({Module0, Function0, Arity}, Surrogates, {Module0, Function0}),
  do_maybe_lazy_call(Parent, State, Line, {Module, Function, Args}).

do_maybe_lazy_call({Name, Arity}, #s{module = Module}, _Line, {Module, Name, Args})
  when length(Args) =:= Arity ->
  %% We are refering to self, this call should be lazy:
  '$$'(?lazy_self_var);
do_maybe_lazy_call(_, #s{module = Module}, Line, {Module, Name, Args}) ->
  %% Local type:
  ?lcall(Name, Args);
do_maybe_lazy_call(_, _, Line, {Module, Name, Args}) ->
  %% Remote type:
  ?rcall(Module, Name, Args).

ignored(Forms) ->
  DeepDefs = [Defs || {attribute, _, typerefl_ignore, Defs} <- Forms],
  lists:usort(lists:append(DeepDefs)).

scan_custom_attributes(State, []) ->
  State;
scan_custom_attributes(State0, [{attribute, _, Attribute, {Type, Module, Function}}|Forms]) ->
  #s{ custom_verif = CustomVerif
    , custom_from_string = CustomFromString
    , custom_pretty_print = CustomPrettyPrint
    , type_surrogates = Surrogates
    } = State0,
  State = case Attribute of
            typerefl_verify ->
              State0#s{custom_verif = CustomVerif #{Type => {Module, Function}}};
            typerefl_from_string ->
              State0#s{custom_from_string = CustomFromString #{Type => {Module, Function}}};
            typerefl_pretty_print ->
              State0#s{custom_pretty_print = CustomPrettyPrint #{Type => {Module, Function}}};
            typerefl_surrogate ->
              State0#s{type_surrogates = Surrogates #{Type => {Module, Function}}};
            _ ->
              State0
          end,
  scan_custom_attributes(State, Forms);
scan_custom_attributes(State, [_|Forms]) ->
  scan_custom_attributes(State, Forms).

%% Collect all type definitions in the module
-spec find_local_typedefs(ast()) -> #{local_tref() => #typedef{}}.
find_local_typedefs(Forms) ->
  ExtractTypeVarName = fun({var, _Line, Name}) ->
                           Name
                       end,
  maps:from_list([begin
                    Params = lists:map(ExtractTypeVarName, Params0),
                    Key = {Name, length(Params)},
                    Val = #typedef{ body = AST
                                  , params = Params
                                  , name = Name
                                  , line = Line
                                  },
                    {Key, Val}
                  end
                  || {attribute, Line, type, {Name, AST, Params0}} <- Forms
                 ]).

%% Collect type definitions that should be reflected and exported:
%%
%% ```-reflect_type([foo/1, bar/2]).'''
-spec types_to_reflect(ast()) -> [{atom(), arity()}].
types_to_reflect(Forms) ->
  [ {Name, Arity}
  || {attribute, _, reflect_type, Types} <- Forms
   , {Name, Arity} <- Types
  ].

%% Check if the type has been already reflected, and reflect it
%% otherwise
-spec maybe_refl_type(local_tref(), #s{}) -> #s{}.
maybe_refl_type( TRef
               , State0 = #s{ reflected_types = RT
                            , local_types = LT
                            }
               ) ->
  case {maps:is_key(TRef, LT), maps:is_key(TRef, RT)} of
    {true, false} ->
      ?log("Reflecting a new type: ~p", [TRef]),
      refl_type(TRef, State0);
    _ ->
      State0
  end.

%% Make a function defenition that is a reflection of the type in the
%% term universe
-spec make_reflection_function(module(), #s{}, reflected_type()) -> ast().
make_reflection_function( Module
                        , State
                        , #typedef{ body = __AST
                                  , params = Vars0
                                  , name = Name
                                  , line = Line
                                  }) ->
  Arity = length(Vars0),
  Vars = [{var, Line, Var} || Var <- Vars0],
  NameStr = io_lib:format("~p:~p", [Module, Name]),
  Name__AST = {string, Line, lists:flatten(NameStr)},
  Self__AST = {'fun', Line, {function, Name, Arity}},
  {function, Line, Name, Arity,
   [{clause, Line, Vars, []
    , ['$$'(begin
              %% This variable is not unused, it can be referred to in __AST
              ?lazy_self_var = ?typerefl_module:make_lazy( Name__AST
                                                         , Self__AST
                                                         , '$'(mk_literal_list(Line, Vars))
                                                         ),
              ?typerefl_module:alias( Name__AST
                                    , __AST
                                    , '$'(make_additional_attrs_ast({Name, Arity}, Line, State))
                                    , '$'(mk_literal_list(Line, Vars))
                                    )
            end)]
    }
   ]}.

%% Insert attributes after `module'
add_attributes(Forms0, Attributes0) ->
  Pred = fun({attribute, _, module, _}) -> false;
            (_) -> true
         end,
  {Before, [Module|Rest]} = lists:splitwith(Pred, Forms0),
  Attributes = [{attribute, 0, K, V} || {K, V} <- Attributes0],
  Before ++ [Module|Attributes] ++ Rest.

-spec transform_type_args(local_tref(), integer(), #s{}, atom(), [ast()] | any) -> {ast(), #s{}}.
transform_type_args(_, _, State, _, any) ->
  {[], State};
transform_type_args(Parent, Line, State0, Name, Args0) ->
  {Args1, State} = lists:mapfoldl( fun(I, S) -> do_refl_type(Parent, S, I) end
                                 , State0
                                 , Args0
                                 ),
  %% Tuples, unions and maps have special representiation in Erlang
  %% AST: they are "function calls" with single argument, which is a
  %% list:
  Args = case lists:member(Name, [tuple, union]) of
           true ->
             [mk_literal_list(Line, Args1)];
           false ->
             Args1
         end,
  {Args, State}.

mk_literal_list(Line, _, []) ->
  {nil, Line};
mk_literal_list(Line, Fun, [Val|Tail]) ->
  {cons, Line, Fun(Val), mk_literal_list(Line, Fun, Tail)}.

mk_literal_list(Line, List) ->
  mk_literal_list(Line, fun(A) -> A end, List).

make_additional_attrs_ast(Name, Line, State) ->
  ?map(maybe_add_custom_attr(Name, Line, check, State#s.custom_verif) ++
         maybe_add_custom_attr(Name, Line, pretty_print, State#s.custom_pretty_print) ++
         maybe_add_custom_attr(Name, Line, from_string, State#s.custom_from_string)).

maybe_add_custom_attr(Name, Line, Key, Map) ->
  case Map of
    #{Name := {Module, Function}} ->
      [?ass(?atom(Key), ?rfun_ref(Module, Function, 1))];
    _ ->
      []
  end.

-if(?OTP_RELEASE >= 27).
maybe_add_doc(Body) ->
  [{attribute, 0, doc, false}, Body].
-else.
maybe_add_doc(Body) ->
  [Body].
-endif.
