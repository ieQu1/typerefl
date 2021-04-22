-module(typerefl).

-include("typerefl_int.hrl").

%% API
-export([typecheck/2, print/1, from_string/2, from_string_/2]).

%% Type reflections (Copy verbatim to types.hrl)
-export([ any/0, atom/0, binary/0, boolean/0, float/0, function/0
        , integer/0, list/0, list/1, map/0, nonempty_list/1, number/0
        , pid/0, port/0, reference/0, term/0, tuple/0, byte/0
        , char/0, arity/0, module/0, non_neg_integer/0
        , string/0, nil/0, map/1, maybe_improper_list/0
        , maybe_improper_list/2, nonempty_maybe_improper_list/0
        , nonempty_maybe_improper_list/2, nonempty_string/0
        , iolist/0, iodata/0, printable_latin1_list/0
        , printable_unicode_list/0
          %% Complex and nonstandard types
        , regexp_string/1, regexp_binary/1
        ]).

%% Internal
-export([fix_t/4, make_lazy/3, alias/2, alias/4]).

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

-define(prim(Name, Check, Rest),
        {?type_refl, #{ check => fun erlang:Check/1
                      , name => ??Name "()"
                      } Rest}).

-define(prim(Name, Check), ?prim(Name, Check, #{})).

-type prim_type() :: {?type_refl, #{ check := ccont()
                                   , name := typename()
                                   , definition => {typename(), iolist()}
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

%% @private Create an alias for a type.
%% @equiv alias(Name, Type, [], [])
-spec alias(string(), type()) -> type().
alias(Name, Type) ->
  alias(Name, Type, [], []).

%% @private Erase definition of the type (it can be useful for
%% avoiding printing obvious stuff like definition of `char()')
-spec nodef(type()) -> type().
nodef({?type_refl, Map}) ->
  {?type_refl, Map #{definition => []}}.

%% @private Create an alias for a higher-kind type
%%
%% Example:
%% ```
%% alias("lists", list(list('A')), ['A'], [bool()])
%% '''
%%
%% @param Name0 Name of the new type
%% @param TypeVars0 Symbolic names of type variables
%% @param Args Values of type variables
-spec alias(string(), type(), [atom()], [type()]) -> type().
alias(Name0, Type, TypeVars0, Args) ->
  %% TODO: Args? Why is it applied?
  TypeVars = [?type_var(I) || I <- TypeVars0],
  {?type_refl, Map} = Type,
  Name = [Name0, "(", string:join([name(I) || I <- Args], ", "), ")"],
  OldName = maps:get(name, Map),
  OldDefn = maps:get(definition, Map, []),
  {?type_refl, Map#{ name => Name
                   , definition =>
                       [{Name, OldName} | OldDefn]
                   }}.

%% @doc Check type of a term.
%%
%% Example:
%% ```
%% ok = typecheck(integer(), 12),
%% {error, _} = typecheck(integer(), [])
%% '''
-spec typecheck(type(), term()) -> ok | {error, string()}.
typecheck(Type, Term) ->
  case check(Type, Term) of
    true ->
      ok;
    {false, Stack0} ->
      %% TODO: do something with stack
      Result = io_lib:format( "Expected type: ~s~nGot: ~p~n"
                            , [print(Type), Term]
                            ),
      {error, lists:flatten(Result)}
  end.

%% @doc Print definition of a type.
-spec print(type()) -> iolist().
print(Type) ->
  Defn0 = defn(Type),
  Defn1 = lists:usort(lists:flatten(Defn0)),
  case Defn1 of
    [] ->
      name(Type);
    _ ->
      Defn = [lists:flatten(io_lib:format("~s :: ~s", [K, V]))
              || {K, V} <- Defn1],
      io_lib:format( "~s when~n  ~s."
                   , [name(Type), string:join(Defn, ",\n  ")])
  end.

%% @doc Try to parse a string or a list of strings in a smart way:
%% convert the string to atom when `Type' is `atom()', leave input as
%% is when `Type' is `string()' and try to parse the string as erlang
%% term otherwise.
%%
%% When `Type' is `list(A)' and the second argument is a list of
%% strings, the above transform is applied (with type `A') to each
%% element of the list.
%%
%% Note: It does NOT check type of the resulting term
-spec from_string(type(), string() | [string()]) ->
                     {ok, term()} | {error, string()}.
from_string(Type, String) ->
  try from_string_(Type, String) of
      Val -> {ok, Val}
  catch
    Err -> Err
  end.

%% @doc Version of `from_string/2' that throws an exception instead of
%% returning error-tuple
%%
%% @throws {error, string()}
%%
%% @see from_string/2
-spec from_string_(type(), string() | [string()]) -> term().
from_string_(Type, []) ->
  %% This is quite sketchy, but _the only_ valid values parsable from
  %% an empty string are `[]' and atom ''. It's typechecker's job to
  %% prove this assumption wrong.
  case Type of
    {?type_refl, #{from_string := Fun}} ->
      Fun([]);
    '' -> '';
    _  -> []
  end;
from_string_(Type, Strings = [Hd|_]) when is_list(Hd) ->
  {?type_refl, #{args := [T]}} = Type,
  [from_string_(T, I) || I <- Strings];
from_string_({?type_refl, Type}, Str) ->
  Fun = maps:get( from_string
                , Type
                , fun string_to_term/1
                ),
  Fun(Str);
from_string_(Type, Str) when is_atom(Type) -> %% Weird, but ok
  case atom_to_list(Type) of
    Str ->
      Type;
    Expected ->
      throw({error, "Expected: " ++ Expected ++ ", got:" ++ Str})
  end;
from_string_(Type0, Str) ->
  from_string_(desugar(Type0), Str).

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
  ?prim(atom, is_atom, #{from_string => fun list_to_atom/1}).

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

%% @doc List of printable latin1 characters
-spec printable_latin1_list() -> type().
printable_latin1_list() ->
  {?type_refl, #{ check => fun io_lib:printable_latin1_list/1
                , name  => "printable_latin1_list()"
                }}.

%% @doc List of printable unicode characters
-spec printable_unicode_list() -> type().
printable_unicode_list() ->
  {?type_refl, #{ check => fun io_lib:printable_unicode_list/1
                , name  => "printable_unicode_list()"
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
                , definition => [defn(A), defn(B)]
                , args => [A, B]
                }}.

%% @doc Reflection of `A | ...' type
-spec union([type(), ...]) -> type().
union([H|Rest]) ->
  lists:foldl(fun union/2, H, Rest).

%% @doc Reflection of `{A, B, ...}' type
-spec tuple([type()]) -> type().
tuple(Args) ->
  {?type_refl, #{ check => validate_tuple(Args)
                , name => ["{", string:join([name(I) || I <- Args], ", "), "}"]
                , definition => [defn(I) || I <- Args]
                , args => Args
                }}.

%% @doc Reflection of `[A]' type
-spec list(type()) -> type().
list(A) ->
  {?type_refl, #{ check => validate_list(A, nil(), true)
                , name => ["[", name(A), "]"]
                , args => [A]
                , definition => defn(A)
                }}.

%% @doc Reflection of `[A,...]' type
-spec nonempty_list(type()) -> type().
nonempty_list(A) ->
  {?type_refl, #{ check => validate_list(A, nil(), false)
                , name => ["[", name(A), ",...]"]
                , args => [A]
                , definition => defn(A)
                }}.

%% @doc Reflection of `maybe_improper_list(A, B)' type
-spec maybe_improper_list(type(), type()) -> type().
maybe_improper_list(A, B) ->
  {?type_refl, #{ check => validate_list(A, B, true)
                , name => io_lib:format("maybe_improper_list(~s, ~s)", [name(A), name(B)])
                , args => [A, B]
                , definition => [defn(A), defn(B)]
                }}.

%% @doc Reflection of `maybe_improper_list()' type
-spec maybe_improper_list() -> type().
maybe_improper_list() ->
  maybe_improper_list(term(), term()).

%% @doc Reflection of `nonempty_maybe_improper_list(A, B)' type
-spec nonempty_maybe_improper_list(type(), type()) -> type().
nonempty_maybe_improper_list(A, B) ->
  {?type_refl, #{ check => validate_list(A, B, false)
                , name => io_lib:format("nonempty_maybe_improper_list(~s, ~s)", [name(A), name(B)])
                , args => [A, B]
                , definition => [defn(A), defn(B)]
                }}.

%% @doc Reflection of `nonempty_maybe_improper_list()' type
-spec nonempty_maybe_improper_list() -> type().
nonempty_maybe_improper_list() ->
  nonempty_maybe_improper_list(term(), term()).

%% @doc Reflection of `A .. B' type
%%
%% Valid values of `A' and `B' are integers and atoms `inf'
%% and <code>'-inf'</code> denoting
-spec range(integer() | '-inf', integer() | inf) -> type().
range(Min, Max) ->
  {?type_refl, #{ check => fun(I) when is_integer(I) ->
                               I =< Max andalso (Min =:= '-inf' orelse I >= Min);
                              (_) ->
                               false
                           end
                , name => io_lib:format("~p..~p", [Min, Max])
                }}.

%% @doc Reflection of `char()' type
-spec char() -> type().
char() ->
  alias("char", nodef(range(0, 16#10ffff))).

%% @doc Reflection of `arity()' type
-spec arity() -> type().
arity() ->
  alias("arity", nodef(range(0, 255))).

%% @doc Reflection of `byte()' type
-spec byte() -> type().
byte() ->
  alias("byte", nodef(range(0, 255))).

%% @doc Reflection of `module()' type
-spec module() -> type().
module() ->
  ?prim(module, is_atom).

%% @doc Reflection of `non_neg_integer()' type
-spec non_neg_integer() -> type().
non_neg_integer() ->
  alias("non_neg_integer", nodef(range(0, inf))).

%% @doc Reflection of `node()' type
-spec node() -> type().
node() ->
  ?prim(node, is_atom).

%% @doc Reflection of `string()' type
-spec string() -> type().
string() ->
  {?type_refl, R0} = alias("string", nodef(list(char()))),
  {?type_refl, R0 #{from_string => fun id/1}}.

%% @doc Reflection of `nonempty_string()' type
-spec nonempty_string() -> type().
nonempty_string() ->
  {?type_refl, R0} = alias("nonempty_string", nodef(nonempty_list(char()))),
  {?type_refl, R0 #{from_string => fun id/1}}.

%% @doc Reflection of `nil()' type
-spec nil() -> type().
nil() ->
  {?type_refl, #{ check => fun(T) -> T =:= [] end
                , name => "[]"
                }}.

%% @doc Reflection of `#{...}' type
-spec map([map_field_spec()]) -> type().
map(FieldSpecs) ->
  Fuzzy = [{K, V} || {fuzzy, K, V} <- FieldSpecs],
  Strict = [{K, V} || {strict, K, V} <- FieldSpecs],
  StrictFieldNames = [io_lib:format("~p := ~s", [K, name(V)]) || {K, V} <- Strict],
  FuzzyFieldNames = [io_lib:format("~s => ~s", [name(K), name(V)]) || {K, V} <- Fuzzy],
  {?type_refl, #{ check => fun(Term) ->
                               validate_map(Fuzzy, Strict, Term)
                           end
                , name => ["#{", lists:join(", ", StrictFieldNames ++ FuzzyFieldNames), "}"]
                , fuzzy_map_fields => Fuzzy
                , strict_map_fields => Strict
                }}.

%% @doc Reflection of `iolist()' type
-spec iolist() -> type().
iolist() ->
  Self = make_lazy("iolist()", fun iolist/0, []),
  Elem = union([byte(), binary(), Self]),
  Tail = union(binary(), nil()),
  alias("iolist", maybe_improper_list(Elem, Tail)).

%% @doc Reflection of `iodata()' type
-spec iodata() -> type().
iodata() ->
  union(iolist(), binary()).

%% @doc Type of UTF8 strings that match a regexp
-spec regexp_string(_Regexp :: string() | binary()) -> type().
regexp_string(Regexp) ->
  {ok, RE} = re:compile(Regexp, [unicode]),
  Name = io_lib:format("string(~p)", [Regexp]),
  {?type_refl, #{ check => fun(Term) ->
                               is_list(Term) andalso re_match(Term, RE)
                           end
                , name => Name
                }}.


%% @doc Type of UTF8 binaries that match a regexp
-spec regexp_binary(_Regexp :: string() | binary()) -> type().
regexp_binary(Regexp) ->
  {ok, RE} = re:compile(Regexp, [unicode]),
  Name = io_lib:format("string(~p)", [Regexp]),
  {?type_refl, #{ check => fun(Term) ->
                               is_binary(Term) andalso re_match(Term, RE)
                           end
                , name => Name
                }}.

%%====================================================================
%% Internal functions
%%====================================================================

%% @private Get type name
-spec name(type() | ?type_var(atom())) -> iolist().
name(A) when is_atom(A) ->
  atom_to_list(A);
name(?type_var(A)) ->
  atom_to_list(A);
name({?type_refl, #{name := Name}}) ->
  Name;
name(#lazy_type{name = Name}) ->
  Name;
name(T) ->
  name(desugar(T)).

%% @private Get type definition (relevant for alias types)
-spec defn(type()) -> iolist().
defn(#lazy_type{name = Name}) ->
  Name;
defn(?type_var(_)) ->
  [];
defn(Type = {?type_refl, Map}) ->
  maps:get(definition, Map, []);
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

%% @private Make a thunk
-spec make_lazy(iolist(), fun(), [term()]) -> type().
make_lazy(Name, Fun, Args) ->
  #lazy_type{ name = Name
            , thunk = fun() -> apply(Fun, Args) end
            }.

%% @private Parse string as an Erlang term
-spec string_to_term(string()) -> term().
string_to_term(String) ->
  case erl_scan:string(String) of
    {ok, Tok0, _} ->
      Tok = Tok0 ++ [{dot, 1}],
      case erl_parse:parse_term(Tok) of
        {ok, Term} ->
          Term;
        {error, {_, _, Err}} ->
          throw({error, "Unable to parse Erlang term"})
      end;
    _ ->
      throw({error, "Unable to tokenize Erlang term"})
  end.

-spec id(A) -> A.
id(A) ->
  A.

-spec re_match(string() | binary(), re:mp()) -> boolean().
re_match(Str, RE)  ->
  try re:run(Str, RE, [{capture, none}]) of
    match   -> true;
    nomatch -> false
  catch
    error:badarg -> false
  end.
