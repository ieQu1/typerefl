-module(typerefl).

-compile(export_all).

%%====================================================================
%% Types
%%====================================================================

-type typename() :: iolist().

-type check_result() :: boolean()
                      | {false, [{typename(), term()} | typename()]}.

-record(type,
        { check           :: fun((term()) -> boolean())
        , name            :: typename()
        %% Additional data that should be printed for this type:
        , definition = [] :: [iolist()]
        }).

-define(check(A), (A#type.check)).
-define(defn(A), (A#type.definition)).

-define(orelse(A, B), orelse(fun() -> A end, fun() -> B end)).
-define(andalso(A, B), andalso(fun() -> A end, fun() -> B end)).

-type type() :: #type{} | atom().

-type check_result() :: boolean().

-spec check(type(), term()) -> check_result().
check(Type, Term) when is_atom(Type) ->
    case Term of
        Type -> true;
        _    -> {error, [{Type, Term}]}
    end;
check(Type, Term) ->
    case ?check(Type)(Term) of
        true           -> true;
        {false, Stack} -> {false, [?name(Type) | Stack]};
        false          -> {false, [{?name(Type), Term}]}
    end.

-spec print(type()) -> iolist().
print(Type) ->
    case ?defn(Type) of
        [] ->
            name(Type);
        Defn ->
            io_lib:format( "~s when~n  ~s."
                         , [name(Type), string:join(lists:usort(Defn), ",~n  ")])
    end.

%%====================================================================
%% Internal functions
%%====================================================================

-spec name(type()) -> iolist().
name(A) when is_atom(A) ->
    atom_to_list(A);
name(#type{name = Name}) ->
    Name.

-spec orelse(fun(() -> R), fun(()-> R)) -> R when R :: check_result().
orelse(A, B) ->
    case A() of
        true -> true;
        _    -> case B() of
                    true -> true;
                    _    -> false
                end
    end.

-spec andalso(fun(() -> R), fun(()-> R)) -> R when R :: check_result().
andalso(A, B) ->
    case A() of
        true -> B();
        Ret  -> Ret
    end.

%%====================================================================
%% Types
%%====================================================================

-spec atom() -> type().
atom() ->
    #type{ check = fun erlang:is_atom/1
         , name = "atom()"
         }.

-spec term() -> type().
term() ->
    #type{ check = fun(_) -> true end
         , name = "term()"
         }.

-spec any() -> type().
any() ->
    term().

-spec union(type(), type()) -> type().
union(A, B) ->
    #type{ check = fun(Term) ->
                           ?orelse(check(A, Term), check(B, Term))
                   end
         , name = [name(A), " | ", name(B)]
         , definition = ?defn(A) ++ ?defn(B)
         }.

-spec tuple([type()]) -> type().
tuple(Args) ->
    #type{ check = fun(Term0) when is_tuple(Term0) ->
                           Term = tuple_to_list(Term0),
                           Term = [todo]
                   end
         , name = ["{", string:join([name(I) || I <- Args], ", "), "}"]
         , definition = lists:append([?defn(I) || I <- Args])
         }.

list(A) ->
    #type{ check = fun(L) when is_list(L) ->
                           Ret = [1 || I <- L, not ?check(A)(I)],
                           Ret =:= [];
                      (L) ->
                           false
                   end
         , name = ["[", name(A), "]"]
         }.
