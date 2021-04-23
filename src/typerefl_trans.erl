%% @hidden
-module(typerefl_trans).

-include("typerefl_int.hrl").

%-define(debug, true).

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
        }).

-define(typerefl_module, typerefl).
-define(lazy_self_var, {var, Line, '__TypeReflSelf'}).
-define(type_vars_var, {var, Line, '__TypeReflTypeVars'}).

%% Naming convention: uppercase macros are for matching, lower-case
%% are for generation (they contain Line as a free variable)

-define(INT(Line, Val),
        {integer, Line, Val}).

-define(INT(Val), ?INT(_, Val)).

-define(int(Val),
        {integer, Line, Val}).

-define(ATOM(Line, Atom),
        {atom, Line, Atom}).

-define(ATOM(Atom), ?ATOM(_, Atom)).

-define(atom(Atom),
        {atom, Line, Atom}).

-define(LCALL(Line, Name, Args),
        {call, Line, ?ATOM(Name), Args}).

-define(tuple(Elems),
        {tuple, Line, Elems}).

-define(cons(A, B),
        {cons, Line, A, B}).

-define(nil,
        {nil, Line}).

-define(map(Elems),
        {map, Line, Elems}).

-define(ass(Key, Value),
        {map_field_assoc, Line, Key, Value}).

-define(lcall(Name, Args),
        {call, Line, ?atom(Name), Args}).

-define(RCALL(Line, Module, Function, Args),
        {call, Line
        , {remote, _, ?ATOM(Module), ?ATOM(Function)}
        , Args
        }).

-define(rcall(Module, Function, Args),
        {call, Line
        , {remote, Line, ?atom(Module), ?atom(Function)}
        , Args
        }).

-define(TYPE_ID(Name, Arity),
        {op, _, '/', ?ATOM(Name), {integer, _, Arity}}).

-define(type_id(Name, Arity),
        {op, Line, '/', ?ATOM(Name), {integer, _, Arity}}).

-define(one_clause_fun(Args, Body),
        {'fun', Line,
         {clauses, [{clause, Line, Args, [], Body}
                   ]}}).

-define(rfun_ref(MODULE, NAME, ARITY),
        {'fun', Line,
         {function, ?atom(MODULE), ?atom(NAME), {integer, Line, ARITY}}}).

parse_transform(Forms0, _Options) ->
  %%?log("Dump of the module AST: ~p", [Forms0]),
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
  ReifiedTypes = maps:map(fun(_, V) ->
                              make_reflection_function(Module, State, V)
                          end,
                          State#s.reflected_types),
  ?log("Reified types:~n~p", [ReifiedTypes]),
  %% Append type reflections to the module definition:
  Forms1 ++ [I || {_, I} <- maps:to_list(ReifiedTypes)].

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

maybe_lazy_call({Name, Arity}, #s{module = Module}, Line, {Module, Name, Args})
  when length(Args) =:= Arity ->
  %% We are refering to self, this call should be lazy:
  ?lazy_self_var;
maybe_lazy_call(_, #s{module = Module}, Line, {Module, Name, Args}) ->
  %% Local type:
  ?lcall(Name, Args);
maybe_lazy_call(_, _, Line, {Module, Name, Args}) ->
  %% Remote type:
  ?rcall(Module, Name, Args).

ignored(Forms) ->
  DeepDefs = [Defs || {attribute, _, typerefl_ignore, Defs} <- Forms],
  lists:usort(lists:append(DeepDefs)).

scan_custom_attributes(State, []) ->
  State;
scan_custom_attributes(State0, [{attribute, _, Attrubute, {Type, Module, Function}}|Forms]) ->
  #s{ custom_verif = CustomVerif
    , custom_from_string = CustomFromString
    , custom_pretty_print = CustomPrettyPrint
    } = State0,
  State = case Attrubute of
            typerefl_verify ->
              State0#s{custom_verif = CustomVerif #{Type => {Module, Function}}};
            typerefl_from_string ->
              State0#s{custom_from_string = CustomFromString #{Type => {Module, Function}}};
            typerefl_pretty_print ->
              State0#s{custom_pretty_print = CustomPrettyPrint #{Type => {Module, Function}}};
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
                        , #typedef{ body = AST
                                  , params = Vars0
                                  , name = Name
                                  , line = Line
                                  }) ->
  Arity = length(Vars0),
  Vars = [{var, Line, Var} || Var <- Vars0],
  NameStr = io_lib:format("~p:~p", [Module, Name]),
  NameAST = {string, Line, lists:flatten(NameStr)},
  SelfAST = {'fun', Line, {function, Name, Arity}},
  LazySelfAST = ?rcall(?typerefl_module, make_lazy,
                       [ NameAST
                       , SelfAST
                       , ?type_vars_var
                       ]),
  AdditionalAttrsAST = make_additional_attrs_ast({Name, Arity}, Line, State),
  {function, Line, Name, Arity,
   [{clause, Line, Vars, []
    , [ {match, Line, ?type_vars_var, mk_literal_list(Line, Vars)}
      , {match, Line, ?lazy_self_var, LazySelfAST}
      , ?rcall(?typerefl_module, alias,
               [ NameAST
               , AST
               , AdditionalAttrsAST
               , ?type_vars_var
               ])
      ]}
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
