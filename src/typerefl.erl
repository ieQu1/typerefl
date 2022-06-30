-module(typerefl).

-include("typerefl_int.hrl").

%% API
-export([typecheck/2, print/1, pretty_print_value/2,
         from_string/2, from_string_/2, name/1]).

%% Type reflections (Copy verbatim to types.hrl)
-export([ any/0, atom/0, binary/0, boolean/0, float/0, function/0
        , integer/0, list/0, list/1, map/0, nonempty_list/1, number/0
        , pid/0, port/0, reference/0, term/0, tuple/0, byte/0
        , char/0, arity/0, module/0, non_neg_integer/0, pos_integer/0
        , string/0, nil/0, map/1, maybe_improper_list/0
        , maybe_improper_list/2, nonempty_maybe_improper_list/0
        , nonempty_maybe_improper_list/2, nonempty_string/0
        , iolist/0, iodata/0, printable_latin1_list/0
        , printable_unicode_list/0, mfa/0, timeout/0, identifier/0
          %% Complex and nonstandard types
        , regexp_string/1, regexp_binary/1
        , ip4_address/0, ip6_address/0, ip_address/0, listen_port_ip4/0
        , integer/1, atom/1, unicode_charlist/0, unicode_chardata/0
        ]).

%% Internal
-export([make_lazy/3, alias/2, alias/4]).

%% Special types that should not be imported:
-export([node/0, union/2, union/1, tuple/1, range/2]).

-export_type([type/0, check_result/0, result/0, typename/0, err/0]).

-type err() :: map().

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
                      , name => str(??Name "()")
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
              | integer()
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
  alias(Name, Type, #{}, []).

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
%% @param Args Values of type variables
-spec alias(string(), type(), map(), [type()]) -> type().
alias(Name0, Type, AdditionalAttrs, Args) ->
  {?type_refl, Map0} = desugar(Type),
  Map = maps:merge(Map0, AdditionalAttrs),
  Name = [Name0, "(", string:join([name(I) || I <- Args], ", "), ")"],
  OldName = maps:get(name, Map),
  OldDefn = maps:get(definition, Map, []),
  {?type_refl, Map#{ name => str(Name)
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
-spec typecheck(type(), term()) -> ok | {error, err()}.
typecheck(Type, Term) ->
  case check(Type, Term) of
    true ->
      ok;
    {false, Stack} ->
      Result = #{ reason => typerefl_typecheck
                , expected => lists:flatten(print(Type))
                , got => Term
                , typerefl_path => lists:reverse(Stack)
                },
      {error, Result}
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
-spec from_string(type(), string() | [string()]) -> term().
from_string(Type, []) ->
  %% This is quite sketchy, but _the only_ valid values parsable from
  %% an empty string are `[]' and atom ''. It's typechecker's job to
  %% prove this assumption wrong.
  case Type of
    {?type_refl, #{from_string := Fun}} ->
      Fun([]);
    '' -> {ok, ''};
    _  -> {ok, []}
  end;
from_string(Type, Strings = [Hd|_]) when is_list(Hd) ->
  {?type_refl, #{args := [T]}} = Type,
  try [from_string_(T, I) || I <- Strings] of
    L -> {ok, L}
  catch
    _:_ -> {error, "Unable to parse strings"}
  end;
from_string({?type_refl, Type}, Str) ->
  Fun = maps:get( from_string
                , Type
                , fun string_to_term/1
                ),
  try Fun(Str) of
    Val -> Val
  catch
    _:_ -> {error, "Unable to parse"}
  end;
from_string(Atom, Str) when is_atom(Atom) -> %% Why would anyone want to parse a known atom? Weird, but ok
  case atom_to_list(Atom) of
    Str ->
      {ok, Atom};
    Expected ->
      {error, "Expected: " ++ Expected ++ ", got:" ++ Str}
  end;
from_string(Type0, Str) ->
  from_string(desugar(Type0), Str).

%% @doc Version of `from_string/2' that throws an exception instead of
%% returning error-tuple
%%
%% @throws {error, string()}
%%
%% @see from_string/2
-spec from_string_(type(), string() | [string()]) ->
                     {ok, term()} | {error, string()}.
from_string_(Type, String) ->
  case from_string(Type, String) of
    {ok, Val} -> Val;
    Err -> throw(Err)
  end.

%% @doc Pretty-print value of type
-spec pretty_print_value(type(), term()) -> iolist().
pretty_print_value({?type_refl, Args}, Term) ->
  case Args of
    #{pretty_print := Fun} ->
      Fun(Term);
    _ ->
      io_lib:format("~p", [Term])
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
  ?prim(atom, is_atom, #{from_string => fun atom_from_string/1}).

%% @doc Reflection of `binary()' type
-spec binary() -> type().
binary() ->
  ?prim(binary, is_binary,
        #{ from_string => fun(Str) -> {ok, unicode:characters_to_binary(Str)} end
         }).

%% @doc Reflection of `boolean()' type
-spec boolean() -> type().
boolean() ->
  ?prim(boolean, is_boolean, #{ from_string => fun to_boolean/1 }).

%% @doc Reflection of `float()' type
-spec float() -> type().
float() ->
  ?prim(float, is_float, #{ from_string => fun to_float/1 }).

%% @doc Reflection of `function()' type
-spec function() -> type().
function() ->
  ?prim(function, is_function).

%% @doc Reflection of `integer()' type
-spec integer() -> type().
integer() ->
  ?prim(integer, is_integer, #{ from_string => fun to_integer/1 }).

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
  ?prim(number, is_number, #{ from_string => fun to_number/1 }).

%% @doc Reflection of `pid()' type
-spec pid() -> type().
pid() ->
  ?prim(pid, is_pid, #{ from_string => make_to_unparsable("pid") }).

%% @doc Reflection of `port()' type
-spec port() -> type().
port() ->
  ?prim(port, is_port, #{ from_string => make_to_unparsable("port") }).

%% @doc Reflection of `reference()' type
-spec reference() -> type().
reference() ->
  ?prim(reference, is_reference, #{ from_string => make_to_unparsable("reference") }).

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
                , name => str([name(A), " | ", name(B)])
                , definition => [defn(A), defn(B)]
                , args => [A, B]
                , from_string => fun(S) -> union_from_string(S, A, B) end
                }}.

%% @doc Reflection of `A | ...' type
-spec union([type(), ...]) -> type().
union([H|Rest]) ->
  lists:foldl(fun union/2, H, Rest).

%% @doc Reflection of `{A, B, ...}' type
-spec tuple([type()]) -> type().
tuple(Args) ->
  {?type_refl, #{ check => validate_tuple(Args)
                , name => str(["{", string:join([name(I) || I <- Args], ", "), "}"])
                , definition => [defn(I) || I <- Args]
                , args => Args
                }}.

%% @doc Reflection of `[A]' type
-spec list(type()) -> type().
list(A) ->
  {?type_refl, #{ check => validate_list(A, nil(), true)
                , name => str(["[", name(A), "]"])
                , args => [A]
                , definition => defn(A)
                }}.

%% @doc Reflection of `[A,...]' type
-spec nonempty_list(type()) -> type().
nonempty_list(A) ->
  {?type_refl, #{ check => validate_list(A, nil(), false)
                , name => str(["[", name(A), ",...]"])
                , args => [A]
                , definition => defn(A)
                }}.

%% @doc Reflection of `maybe_improper_list(A, B)' type
-spec maybe_improper_list(type(), type()) -> type().
maybe_improper_list(A, B) ->
  {?type_refl, #{ check => validate_list(A, B, true)
                , name => name("maybe_improper_list(~s, ~s)", [name(A), name(B)])
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
                , name => name("nonempty_maybe_improper_list(~s, ~s)", [name(A), name(B)])
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
                , name => name("~p..~p", [Min, Max])
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

%% @doc Reflection of `pos_integer()' type
-spec pos_integer() -> type().
pos_integer() ->
  alias("pos_integer", nodef(range(1, inf))).

%% @doc Reflection of `mfa()' type
-spec mfa() -> type().
mfa() ->
  alias("mfa", tuple([module(), atom(), arity()])).

%% @doc Reflection of `identifier()' type
-spec identifier() -> type().
identifier() ->
  alias("identifier", union([pid(), port(), reference()])).

%% @doc Reflection of `timeout()' type
-spec timeout() -> type().
timeout() ->
  alias("timeout", union([infinity, non_neg_integer()])).

%% @doc Reflection of `node()' type
-spec node() -> type().
node() ->
  ?prim(node, is_atom).

%% @doc Reflection of `string()' type
-spec string() -> type().
string() ->
  {?type_refl, R0} = alias("string", nodef(list(char()))),
  {?type_refl, R0 #{from_string => fun wrap_ok/1}}.

%% @doc Reflection of `nonempty_string()' type
-spec nonempty_string() -> type().
nonempty_string() ->
  {?type_refl, R0} = alias("nonempty_string", nodef(nonempty_list(char()))),
  {?type_refl, R0 #{from_string => fun wrap_ok/1}}.

%% @doc Reflection of `nil()' type
-spec nil() -> type().
nil() ->
  {?type_refl, #{ check => fun(T) -> T =:= [] end
                , name => "[]"
                }}.

%% @doc Reflection of concrete atom type
-spec atom(atom()) -> type().
atom(A) ->
  {?type_refl, #{ check => fun(T) -> T =:= A end
                , name => atom_to_list(A)
                }}.

%% @doc Reflection of concrete integer type
-spec integer(integer()) -> type().
integer(I)->
  {?type_refl, #{ check => fun(T) -> T =:= I end
                , name => integer_to_list(I)
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
                , name => str(["#{", lists:join(", ", StrictFieldNames ++ FuzzyFieldNames), "}"])
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

%% @doc Approximate reflection of `unicode:charlist()' type
-spec unicode_charlist() -> type().
unicode_charlist() ->
  Self = make_lazy("unicode:charlist()", fun unicode_charlist/0, []),
  Elem = union([char(), binary(), Self]),
  Tail = union(binary(), nil()),
  alias("unicode:charlist", maybe_improper_list(Elem, Tail)).

%% @doc Reflection of `iodata()' type
-spec iodata() -> type().
iodata() ->
  union(iolist(), binary()).

%% @doc Approximate reflection of `unicode:chardata()' type
-spec unicode_chardata() -> type().
unicode_chardata() ->
  alias("unicode:chardata", union([unicode_charlist(), binary()])).

%% @doc Type of UTF8 strings that match a regexp
-spec regexp_string(_Regexp :: string() | binary()) -> type().
regexp_string(Regexp) ->
  {ok, RE} = re:compile(Regexp, [unicode]),
  Name = name("string(~p)", [Regexp]),
  {?type_refl, #{ check => fun(Term) ->
                               is_list(Term) andalso re_match(Term, RE)
                           end
                , name => Name
                , from_string => fun wrap_ok/1
                }}.

%% @doc Type of UTF8 binaries that match a regexp
-spec regexp_binary(_Regexp :: string() | binary()) -> type().
regexp_binary(Regexp) ->
  {ok, RE} = re:compile(Regexp, [unicode]),
  Name = name("binary(~p)", [Regexp]),
  {?type_refl, #{ check => fun(Term) ->
                               is_binary(Term) andalso re_match(Term, RE)
                           end
                , name => Name
                , from_string => fun (V) -> {ok, list_to_binary(V)} end
                }}.

%% @doc Type of IPv6 addresses
-spec ip4_address() -> type().
ip4_address() ->
  Range = range(0, 255),
  BaseType = tuple([Range, Range, Range, Range]),
  AdditionalAttrs = #{ from_string  => fun inet:parse_ipv4_address/1
                     , pretty_print => fun inet:ntoa/1
                     },
  alias("ip4_address", BaseType, AdditionalAttrs, []).

%% @doc Type of IPv6 addresses
-spec ip6_address() -> type().
ip6_address() ->
  Range = range(0, 1 bsl 16 - 1),
  BaseType = tuple([Range, Range, Range, Range, Range, Range, Range, Range]),
  AdditionalAttrs = #{ from_string  => fun inet:parse_ipv6_address/1
                     , pretty_print => fun inet:ntoa/1
                     },
  alias("ip6_address", BaseType, AdditionalAttrs, []).

%% @doc Listen IPv4 port, e.g. `127.0.0.1:8080' or `8080'
-spec listen_port_ip4() -> type().
listen_port_ip4() ->
  PortRange = range(1, 1 bsl 16 - 1),
  BaseType = tuple([ip4_address(), PortRange]),
  Parse = fun(Str) ->
              case string:split(Str, ":") of
                [Addr0, Port0] ->
                  {Port, _} = string:to_integer(Port0),
                  {ok, Addr} = inet:parse_ipv4_address(Addr0),
                  {ok, {Addr, Port}};
                [Port0] ->
                  {Port, _} = string:to_integer(Port0),
                  {ok, {{0, 0, 0, 0}, Port}}
              end
          end,
  PrettyPrint = fun({Addr, Port}) ->
                    [inet:ntoa(Addr), $:, integer_to_binary(Port)]
                end,
  AdditionalAttrs = #{ from_string  => Parse
                     , pretty_print => PrettyPrint
                     },
  alias("listen_port_ip4", BaseType, AdditionalAttrs, []).

%% @doc Type of IPv4 or IPv6 addresses
-spec ip_address() -> type().
ip_address() ->
  BaseType = union([ip4_address(), ip6_address()]),
  AdditionalAttrs = #{ from_string  => fun inet:parse_address/1
                     , pretty_print => fun inet:ntoa/1
                     },
  alias("ip_address", BaseType, AdditionalAttrs, []).

%% @doc Get type name.
-spec name(type() | ?type_var(atom())) -> string().
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

%%====================================================================
%% Internal functions
%%====================================================================

%% @private Try to parse boolean value from string
to_boolean(Str) ->
  case string:trim(Str) of
    "true" -> {ok, true};
    "false" -> {ok, false};
    _ -> {error, "Unable to parse boolean value"}
  end.

%% @private Try to parse integer value from string
to_integer(Str) ->
  case string:to_integer(string:trim(Str)) of
    {Num, ""} when is_integer(Num) -> {ok, Num};
    _ -> {error, "Unable to parse integer value"}
  end.

%% @private Try to parse float value from string
to_float(Str) ->
  case string:to_float(string:trim(Str)) of
    {Num, ""} when is_float(Num) -> {ok, Num};
    _ -> {error, "Unable to parse float value"}
  end.

%% @private Try to parse number value from string
to_number(Str) ->
  TrimmedStr = string:trim(Str),
  case string:to_integer(TrimmedStr) of
    {IntNum, ""} when is_integer(IntNum) -> {ok, IntNum};
    _ ->
      case string:to_float(TrimmedStr) of
        {FloatNum, ""} when is_float(FloatNum) -> {ok, FloatNum};
        _ -> {error, "Unable to parse number value"}
      end
  end.

%% @private Factory making functions returning constant parse errors.
make_to_unparsable(Name) ->
  Error = "Unable to parse " ++ Name ++ " value",
  fun(_Str) ->
    {error, Error}
  end.

%% @private Get type definition (relevant for alias types)
-spec defn(type()) -> iolist().
defn(#lazy_type{name = Name}) ->
  Name;
defn(?type_var(_)) ->
  [];
defn({?type_refl, Map}) ->
  maps:get(definition, Map, []);
defn(A) when is_atom(A) ->
  [];
defn(Type) ->
  defn(desugar(Type)).

%% @private Run the continuation and extend the result if needed
-spec check(type(), term()) -> result().
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
                  _    -> throw({false, [KeyT]})
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
desugar(A) when is_atom(A) ->
  atom(A);
desugar(I) when is_integer(I) ->
  integer(I);
desugar(T) when is_map(T) ->
  map([{fuzzy, K, V} || {K, V} <- maps:to_list(T)]).

%% @private Make a thunk
-spec make_lazy(iolist(), fun(), [term()]) -> type().
make_lazy(Name, Fun, Args) ->
  #lazy_type{ name = Name
            , thunk = fun() -> apply(Fun, Args) end
            }.

%% @private Parse string as an Erlang term
-spec string_to_term(string()) -> {ok, term()} | {error, _}.
string_to_term(String) ->
  case erl_scan:string(String) of
    {ok, Tok0, _} ->
      Tok = Tok0 ++ [{dot, 1}],
      case erl_parse:parse_term(Tok) of
        {ok, Term} ->
          {ok, Term};
        {error, {_, _, _Err}} ->
          {error, "Unable to parse Erlang term"}
      end;
    _ ->
      {error, "Unable to tokenize Erlang term"}
  end.

-spec re_match(string() | binary(), re:mp()) -> boolean().
re_match(Str, RE)  ->
  try re:run(Str, RE, [{capture, none}]) of
    match   -> true;
    nomatch -> false
  catch
    error:badarg -> false
  end.

wrap_ok(A) ->
  {ok, A}.

atom_from_string(Str) ->
  {ok, list_to_atom(Str)}.

%% @private Try to parse a string to either TypeA or TypeB.
%% If succeed in both, TypeA wins.
-spec union_from_string(string(), type(), type()) -> {ok, term()} | {error, string()}.
union_from_string(String, TypeA, TypeB) ->
  case {convert_and_check(TypeA, String), convert_and_check(TypeB, String)} of
    {{ok, ValueA}, _} ->
      {ok, ValueA};
    {_, {ok, VB}} ->
      {ok, VB};
    {{error, _}, {error, _}} ->
      {error, "Unable to parse string"}
  end.

%% @private convert string and check the output.
convert_and_check(Type, String) ->
  case from_string(Type, String) of
    {ok, Value} ->
      case typecheck(Type, Value) of
        ok ->
          {ok, Value};
        {error, _} = E ->
          E
      end;
    {error, _} = E ->
      E
  end.

%% @private Format a name string.
name(Fmt, Args) ->
    str(io_lib:format(Fmt, Args)).

str(Name) ->
    lists:flatten(Name).
