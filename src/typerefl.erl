-module(typerefl).

%% API
-export([typecheck/2, print/1]).

%% Type reflections
-export([ any/0, atom/0, binary/0, boolean/0, float/0, function/0
        , integer/0, list/0, list/1, map/0, nonempty_list/1, number/0
        , pid/0, port/0, reference/0, term/0, tuple/0, tuple/1, union/2
        ]).

-export_type([type/0, check_result/0, result/0, typename/0]).

%%====================================================================
%% Types
%%====================================================================

-type typename() :: iolist().

-type check_result() :: boolean()
                      | {false, [{typename(), term()} | typename()]}.

-type result() :: true
                | {false, [{typename(), term()} | typename()]}.

-type ccont() :: fun((term()) -> check_result()).

-record(type,
        { check           :: fun((term()) -> check_result())
        , name            :: typename()
        %% Additional data that should be printed for this type:
        , definition = [] :: [iolist()]
        }).

-define(prim(Name, Check),
        #type{ check = fun erlang:Check/1
             , name = ??Name "()"
             }).

-type type() :: #type{} | atom().

%%====================================================================
%% API functions
%%====================================================================

-spec typecheck(type() | tuple() | [type(), ...], term()) ->
                   ok | {error, string()}.
typecheck(Type0, Term) ->
  Type = desugar(Type0),
  case check(Type, Term) of
    true ->
      ok;
    {false, Stack0} ->
      %% TODO: do something with stack
      Result = io_lib:format( "Type error in ~p"
                            , [name(Type), Term]
                            ),
      {error, lists:flatten(Result)}
  end.

-spec print(type() | tuple() | [type(), ...]) -> iolist().
print(Type0) ->
  Type = desugar(Type0),
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
  ?prim(list, is_list).

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
  #type{ check = fun(_) -> true end
       , name = "term()"
       }.

%% @doc Reflection of `tuple()' type
-spec tuple() -> type().
tuple() ->
  ?prim(tuple, is_tuple).

%% @doc Reflection of `A | B' type
-spec union(type(), type()) -> type().
union(A, B) ->
  #type{ check = or_else(check(A), check(B))
       , name = [name(A), " | ", name(B)]
       , definition = defn(A) ++ defn(B)
       }.

%% @doc Reflection of `{A, B, ...}' type
-spec tuple([type()]) -> type().
tuple(Args) ->
  #type{ check = validate_tuple(Args)
       , name = ["{", string:join([name(I) || I <- Args], ", "), "}"]
       , definition = lists:append([defn(I) || I <- Args])
       }.

%% @doc Reflection of `[A]' type
-spec list(type()) -> type().
list(A) ->
  #type{ check = validate_list(A, 0)
       , name = ["[", name(A), "]"]
       }.

%% @doc Reflection of `[A,...]' type
-spec nonempty_list(type()) -> type().
nonempty_list(A) ->
  #type{ check = validate_list(A, 1)
       , name = ["[", name(A), ",...]"]
       }.

%%====================================================================
%% Internal functions
%%====================================================================

%% @private Get type name
-spec name(type()) -> iolist().
name(A) when is_atom(A) ->
  atom_to_list(A);
name(#type{name = Name}) ->
  Name.

%% @private Get type definition (relevant for user-defined types)
-spec defn(type()) -> iolist().
defn(#type{definition = Ret}) ->
  Ret;
defn(_) ->
  [].

%% @private Run the continuation and extend the result if needed
-spec check(type(), term()) -> result().
check(Type, Term) when is_atom(Type) ->
  case Term of
    Type -> true;
    _    -> {false, [{Type, Term}]}
  end;
check(Type = #type{check = Check}, Term) ->
  case Check(Term) of
    true           -> true;
    {false, Stack} -> {false, [name(Type) | Stack]};
    false          -> {false, [{name(Type), Term}]}
  end.

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

-spec validate_list(type(), integer()) -> ccont().
validate_list(T, LMin) ->
  fun(L) when is_list(L), length(L) >= LMin ->
      try
        [check_(T, I) || I <- L],
        true
      catch
        Err = {false, _Stack} -> Err
      end;
     (L) ->
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

%% @private Transforms tuples to `tuple/1' calls and so on.
-spec desugar(type() | tuple() | [type(), ...]) -> type().
desugar(T) when is_atom(T) ->
  T;
desugar(T = #type{}) ->
  T;
desugar(T) when is_tuple(T) ->
  tuple(tuple_to_list(T));
desugar([T]) ->
  list(T).

%% @private CPS version of andalso operator
%% -spec and_also(F, F) -> F when F :: ccont().
%% and_also(A, B) ->
%%   fun(Term) ->
%%       case A(Term) of
%%         true -> B(Term);
%%         Ret  -> Ret
%%       end
%%   end.
