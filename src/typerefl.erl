-module(typerefl).

-include("typerefl_int.hrl").

%% API
-export([typecheck/2, print/1]).

%% Type reflections (Copy verbatim to types.hrl)
-export([ any/0, atom/0, binary/0, boolean/0, float/0, function/0
        , integer/0, list/0, list/1, map/0, nonempty_list/1, number/0
        , pid/0, port/0, reference/0, term/0, tuple/0, byte/0
        , char/0, arity/0, module/0, non_neg_integer/0
        , string/0, nil/0, map/1, maybe_improper_list/0
        , maybe_improper_list/2, nonempty_maybe_improper_list/0
        , nonempty_maybe_improper_list/2, nonempty_string/0
        , iolist/0, iodata/0
        ]).

%% Internal
-export([fix_t/4, make_lazy/3, alias/2]).

%% Special types that should not be imported:
-export([node/0, union/2, union/1, tuple/1, range/2]).

-export_type([type/0, check_result/0, result/0, typename/0]).

%%====================================================================
%% Types
%%====================================================================

-type typename() :: iodata().

-type check_result() :: boolean()
                      | {false, [{typename(), term()} | typename()]}.

-type result() :: true
                | {false, [{typename(), term()} | typename()]}.

-type ccont() :: fun((term()) -> check_result()).

-type thunk(Val) :: fun(() -> Val).

-define(is_thunk(A), is_function(A, 0)).

-define(prim(Name, Check),
        {?type_refl, #{ check => fun erlang:Check/1
                      , name => ??Name "()"
                      }}).

-type prim_type() :: {?type_refl, #{ check := ccont()
                                   , name := typename()
                                   , definition => iolist()
                                   }}.

-type type_intern() :: prim_type()
                     | thunk(type()).

-type type() :: type_intern()
              | atom()
              | tuple()
              | [type(), ...]
              | []
              | #{type() => type()}.

-type map_field_spec() :: {fuzzy, type(), type()}
                        | {strict, term(), type()}.

%%====================================================================
%% API functions
%%====================================================================

alias(Name, Type) ->
  {?type_refl, Map} = Type,
  {?type_refl, Map#{name => Name}}.

-spec typecheck(type() | tuple() | [type(), ...], term()) ->
                   ok | {error, string()}.
typecheck(Type, Term) ->
  case check(Type, Term) of
    true ->
      ok;
    {false, Stack0} ->
      %% TODO: do something with stack
      Result = io_lib:format( "Expected: ~s~nGot: ~p~n"
                            , [name(Type), Term]
                            ),
      {error, lists:flatten(Result)}
  end.

-spec print(type() | tuple() | [type(), ...]) -> iolist().
print(Type) ->
  case defn(Type) of
    [] ->
      name(Type);
    Defn ->
      io_lib:format( "~s when~n  ~s."
                   , [name(Type), string:join(lists:usort(Defn), ",~n  ")])
  end.

%%====================================================================
%% Type reflections
%%====================================================================

%% @doc Reflection of `any()' type
-spec any() -> type().
any() ->
    term().

%% @doc Reflection of `atom()' type
-spec atom() -> type().
atom() ->
  ?prim(atom, is_atom).

%% @doc Reflection of `binary()' type
-spec binary() -> type().
binary() ->
  ?prim(binary, is_binary).

%% @doc Reflection of `boolean()' type
-spec boolean() -> type().
boolean() ->
  ?prim(boolean, is_boolean).

%% @doc Reflection of `float()' type
-spec float() -> type().
float() ->
  ?prim(float, is_float).

%% @doc Reflection of `function()' type
-spec function() -> type().
function() ->
  ?prim(function, is_function).

%% @doc Reflection of `integer()' type
-spec integer() -> type().
integer() ->
  ?prim(integer, is_integer).

%% @doc Reflection of `list()' type
-spec list() -> type().
list() ->
  list(term()).

%% @doc Reflection of `map()' type
-spec map() -> type().
map() ->
  ?prim(map, is_map).

%% @doc Reflection of `number()' type
-spec number() -> type().
number() ->
  ?prim(number, is_number).

%% @doc Reflection of `pid()' type
-spec pid() -> type().
pid() ->
  ?prim(pid, is_pid).

%% @doc Reflection of `port()' type
-spec port() -> type().
port() ->
  ?prim(port, is_port).

%% @doc Reflection of `reference()' type
-spec reference() -> type().
reference() ->
  ?prim(reference, is_reference).

%% @doc Reflection of `term()' type
-spec term() -> type().
term() ->
  {?type_refl, #{ check => fun(_) -> true end
                , name => "term()"
                }}.

%% @doc Reflection of `tuple()' type
-spec tuple() -> type().
tuple() ->
  ?prim(tuple, is_tuple).

%% @doc Reflection of `A | B' type
-spec union(type(), type()) -> type().
union(A, B) ->
  {?type_refl, #{ check => or_else(check(A), check(B))
                , name => [name(A), " | ", name(B)]
                %, definition => defn(A) ++ defn(B) TODO
                }}.

-spec union([type(), ...]) -> type().
union([H|Rest]) ->
  lists:foldl(fun union/2, H, Rest).

%% @doc Reflection of `{A, B, ...}' type
-spec tuple([type()]) -> type().
tuple(Args) ->
  {?type_refl, #{ check => validate_tuple(Args)
                , name => ["{", string:join([name(I) || I <- Args], ", "), "}"]
                , definition => lists:append([defn(I) || I <- Args])
                }}.

%% @doc Reflection of `[A]' type
-spec list(type()) -> type().
list(A) ->
  {?type_refl, #{ check => validate_list(A, nil(), true)
                , name => ["[", name(A), "]"]
                }}.

%% @doc Reflection of `[A,...]' type
-spec nonempty_list(type()) -> type().
nonempty_list(A) ->
  {?type_refl, #{ check => validate_list(A, nil(), false)
                , name => ["[", name(A), ",...]"]
                }}.

-spec maybe_improper_list(type(), type()) -> type().
maybe_improper_list(A, B) ->
  {?type_refl, #{ check => validate_list(A, B, true)
                , name => io_lib:format("maybe_improper_list(~s, ~s)", [name(A), name(B)])
                }}.

-spec maybe_improper_list() -> type().
maybe_improper_list() ->
  maybe_improper_list(term(), term()).

-spec nonempty_maybe_improper_list(type(), type()) -> type().
nonempty_maybe_improper_list(A, B) ->
  {?type_refl, #{ check => validate_list(A, B, false)
                , name => io_lib:format("nonempty_maybe_improper_list(~s, ~s)", [name(A), name(B)])
                }}.

-spec nonempty_maybe_improper_list() -> type().
nonempty_maybe_improper_list() ->
  nonempty_maybe_improper_list(term(), term()).

-spec range(integer() | '-inf', integer() | inf) -> type().
range(Min, Max) ->
  {?type_refl, #{ check => fun(I) when is_integer(I) ->
                               I =< Max andalso (Min =:= '-inf' orelse I >= Min);
                              (_) ->
                               false
                           end
                , name => io_lib:format("~p..~p", [Min, Max])
                }}.

-spec char() -> type().
char() ->
  alias("char()", range(0, 16#10ffff)).

-spec arity() -> type().
arity() ->
  alias("arity()", range(0, 255)).

-spec byte() -> type().
byte() ->
  range(0, 255).

-spec module() -> type().
module() ->
  ?prim(module, is_atom).

-spec non_neg_integer() -> type().
non_neg_integer() ->
  alias("non_neg_integer()", range(0, inf)).

-spec node() -> type().
node() ->
  ?prim(node, is_atom).

-spec string() -> type().
string() ->
  alias("string()", list(char())).

-spec nonempty_string() -> type().
nonempty_string() ->
  alias("nonempty_string()", nonempty_list(char())).

-spec nil() -> type().
nil() ->
  {?type_refl, #{ check => fun(T) -> T =:= [] end
                , name => "[]"
                }}.

-spec map([map_field_spec()]) -> type().
map(FieldSpecs) ->
  Fuzzy = [{K, V} || {fuzzy, K, V} <- FieldSpecs],
  Strict = [{K, V} || {strict, K, V} <- FieldSpecs],
  StrictFieldNames = [io_lib:format("~p := ~s", [K, name(V)]) || {K, V} <- Strict],
  FuzzyFieldNames = [io_lib:format("~s => ~s", [name(K), name(V)]) || {K, V} <- Fuzzy],
  {?type_refl, #{ check => fun(Term) ->
                              validate_map(Fuzzy, Strict, Term)
                          end
                , name => ["#{", intercalate(StrictFieldNames ++ FuzzyFieldNames, ", "), "}"]
                }}.

-spec iolist() -> type().
iolist() ->
  Self = make_lazy("iolist()", fun iolist/0, []),
  Elem = union([byte(), binary(), Self]),
  Tail = union(binary(), nil()),
  alias("iolist()", maybe_improper_list(Elem, Tail)).

-spec iodata() -> type().
iodata() ->
  union(iolist(), binary()).

%%====================================================================
%% Internal functions
%%====================================================================

%% @private Get type name
-spec name(type()) -> iolist().
name(A) when is_atom(A) ->
  atom_to_list(A);
name({?type_refl, #{name := Name}}) ->
  Name;
name(#lazy_type{name = Name}) ->
  Name;
name(T) ->
  name(desugar(T)).

%% @private Get type definition (relevant for user-defined types)
-spec defn(type()) -> iolist().
defn({?type_refl, Map}) ->
  maps:get(definition, Map, []);
defn(#lazy_type{name = Name}) ->
  Name;
defn(A) when is_atom(A) ->
  [];
defn(Type) ->
  defn(desugar(Type)).

%% @private Run the continuation and extend the result if needed
-spec check(type(), term()) -> result().
check(Type, Term) when is_atom(Type) ->
  case Term of
    Type -> true;
    _    -> {false, [{Type, Term}]}
  end;
check(Type = {?type_refl, #{check := Check}}, Term) ->
  case Check(Term) of
    true           -> true;
    {false, Stack} -> {false, [name(Type) | Stack]};
    false          -> {false, [{name(Type), Term}]}
  end;
check(Type, Term) ->
  check(desugar(Type), Term).

%% @private CPS version of `check/2' function
-spec check(type()) -> ccont().
check(Type) ->
  fun(Term) ->
      check(Type, Term)
  end.

%% @private Version of check that @throws `{false, Stack}'
-spec check_(type(), term()) -> true.
check_(Type, Term) ->
  case check(Type, Term) of
    true -> true;
    Err = {false, _} -> throw(Err)
  end.

-spec validate_tuple([type()]) -> ccont().
validate_tuple(Args) ->
  fun(Term0) when is_tuple(Term0) ->
      try
        Term = tuple_to_list(Term0),
        length(Term) =:= length(Args) orelse throw(badtuple),
        [check_(T, V) || {T, V} <- lists:zip(Args, Term)],
        true
      catch
        {false, Stack} ->
          {false, Stack};
        badtuple ->
          false
      end;
     (_) ->
      false
  end.

-spec validate_list(type(), type(), boolean()) -> ccont().
validate_list(ElemT, TailT, CanBeEmpty) ->
  Go = fun Go([H|T]) ->
           check_(ElemT, H),
           Go(T);
          Go(T) ->
           check_(TailT, T)
       end,
  fun(L) ->
      try
        is_list(L) orelse throw(badlist),
        CanBeEmpty orelse L =/= [] orelse throw(badlist),
        Go(L)
      catch
        Err = {false, _Stack} -> Err;
        badlist -> false
      end
  end.

-spec validate_map( [{type(), type()}]
                  , [{term(), type()}]
                  , term()
                  ) -> true | {false, _}.
validate_map(Fuzzy, Strict, Term) ->
    try
        is_map(Term) orelse throw(badmap),
        %% Validate strict fields:
        [case Term of
           #{Key := Val} ->
             check_(ValT, Val);
           _ ->
             throw({missing_key, Key})
         end
         || {Key, ValT} <- Strict],
        %% Validate fuzzy fields via ugly O(n * m) algorithm:
        StrictKeys = [K || {K, _} <- Strict],
        Term1 = maps:without(StrictKeys, Term),
        [try
           [case check(KeyT, Key) of
              true ->
                case check(ValT, Val) of
                  true -> throw(success);
                  _ -> nok
                end;
              _ ->
                nok
            end
            || {KeyT, ValT} <- Fuzzy],
           throw(badmap)
         catch
           success -> ok
         end
         || {Key, Val} <- maps:to_list(Term1)],
        true
    catch
      Err = {false, _Stack} ->
        Err;
      {missing_key, _} ->
        false; %% TODO: make better error stack
      badmap ->
        false
    end.

%% @private CPS version of orelse operator
-spec or_else(F, F) -> F when F :: ccont().
or_else(A, B) ->
  fun(Term) ->
      case A(Term) of
        true -> true;
        _    -> case B(Term) of
                  true -> true;
                  _    -> false
                end
      end
  end.

%% @private Transforms tuples to `tuple/1' calls and so on. Forces
%% lazy evaluation.
-spec desugar(tuple() | [type(), ...] | [] | #{type() => type()}) -> type().
desugar(T = {?type_refl, _}) ->
  T;
desugar(#lazy_type{thunk = Type}) ->
  desugar(Type());
desugar(T) when is_tuple(T) ->
  tuple(tuple_to_list(T));
desugar([T]) ->
  list(T);
desugar([]) ->
  nil();
desugar(T) when is_map(T) ->
  map([{fuzzy, K, V} || {K, V} <- maps:to_list(T)]).

%% @private Bastardized fixed-point combinator-ish function that we
%% use to implement lazy recursion
-spec fix_t(typename(), fun(), fun((#lazy_type{}) -> type()), [term()]) -> type().
fix_t(Name, F, G, Args) ->
  H = make_lazy(Name, F, Args),
  G(H).

%% @private
-spec make_lazy(iolist(), fun(), [term()]) -> type().
make_lazy(Name, Fun, Args) ->
  #lazy_type{ name = Name
            , thunk = fun() -> apply(Fun, Args) end
            }.

intercalate([], _) ->
  [];
intercalate([A], _) ->
  [A];
intercalate([A|T], S) ->
  [A, S | intercalate(T, S)].

%% @private CPS version of andalso operator
%% -spec and_also(F, F) -> F when F :: ccont().
%% and_also(A, B) ->
%%   fun(Term) ->
%%       case A(Term) of
%%         true -> B(Term);
%%         Ret  -> Ret
%%       end
%%   end.
