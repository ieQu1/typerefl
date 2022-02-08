-module(transform_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("typerefl/include/types.hrl").
-include_lib("typerefl/src/typerefl_int.hrl").

-typerefl_ignore([ignored/0]).

-define(add_module(Str), atom_to_list(?MODULE) ++ ":" ++ Str).

-define(typeEqual(A, B), typeEqual(?add_module(??B), A, B)).

-define(mapTypeEqual(A, B), mapTypeEqual(?add_module(??B), A, B)).

-reflect_type([ mybool/0, myterm1/0, myterm2/0, my_int/0, my_byte/0
              , list_of_bools/0, non_empty_list_of_bools/0, mylist0/0, strings/0
              , foo_atom/0, foobarbaz/0, mytuple/0, mytuple_any/0, mytuple_empty/0
              , simple/1, stupid_list/1, mymap/0, remote_types/0, ipv4_address/0
              , ipv6_address/0, uri/0
              ]).

%% silence the unused warning
-export_type([ignored/0]).

-export([verify_uri/1]).

%% -----------------------------------------------------------------------------

-type mybool() :: boolean().

boolean_refl_test() ->
  ?typeEqual(boolean(), mybool()).

%% -----------------------------------------------------------------------------

-type myterm1() :: term().

-type myterm2() :: any().

term_refl_test() ->
  ?typeEqual(term(), myterm1()),
  ?typeEqual(term(), myterm2()).

%% -----------------------------------------------------------------------------

-type my_int() :: non_neg_integer().

-type my_byte() :: 0..255.

integer_refl_test() ->
  ?typeEqual(non_neg_integer(), my_int()),
  ?typeEqual(range(0, 255), my_byte()).

%% -----------------------------------------------------------------------------

-type list_of_bools() :: [boolean()].

-type non_empty_list_of_bools() :: [boolean(), ...].

-type mylist0() :: list().

-type strings() :: list(string()).

list_refl_test() ->
  ?typeEqual(list(boolean()), list_of_bools()),
  ?typeEqual(nonempty_list(boolean()), non_empty_list_of_bools()),
  ?typeEqual(list(), mylist0()),
  ?typeEqual(list(string()), strings()).

%% -----------------------------------------------------------------------------

-type foo_atom() :: list(foo).

atom_refl_test() ->
  ?typeEqual(list(foo), foo_atom()).

%% -----------------------------------------------------------------------------

-type foobarbaz() :: foo | bar | baz.

union_refl_test() ->
  ?typeEqual(union([foo, bar, baz]), foobarbaz()).

%% -----------------------------------------------------------------------------

-type mytuple() :: {float(), float(), xxx}.

-type mytuple_any() :: tuple().

-type mytuple_empty() :: {}.

tuple_refl_test() ->
  ?typeEqual(tuple([float(), float(), xxx]), mytuple()),
  ?typeEqual(tuple(), mytuple_any()),
  ?typeEqual(tuple([]), mytuple_empty()).

%% -----------------------------------------------------------------------------

-type simple(A) :: A.

%% Recursive type is fine too:
-type stupid_list(OwO) :: {cons, OwO, stupid_list(OwO)} | nil.

higher_kind_refl_test() ->
  typeEqual(?add_module("simple(atom())"), atom(), simple(atom())),
  typeEqual(?add_module("simple([atom()])"), list(atom()), simple(list(atom()))),
  %% TODO can't simply check StupidList check function here... So just
  %% running reflection for it.
  ok.

%% -----------------------------------------------------------------------------

-type mymap1() :: map().

-type mymap2() :: #{integer() => atom()}.

-type mymap3() :: #{foo := integer()}.

-type mymap() :: #{ mymap1() => mymap2()
                  , integer() => mymap3()
                  , bar := {integer(), integer()}
                  }.

map_refl_test() ->
  ?typeEqual(map(), mymap1()),
  ?mapTypeEqual(typerefl:map([{fuzzy, integer(), atom()}]), mymap2()),
  ?mapTypeEqual(typerefl:map([{strict, foo, integer()}]), mymap3()),
  MyMap = typerefl:map([ {fuzzy, mymap1(), mymap2()}
                       , {fuzzy, integer(), mymap3()}
                       , {strict, bar, typerefl:tuple([integer(), integer()])}
                       ]),
  ?mapTypeEqual(MyMap, mymap()).

%% -----------------------------------------------------------------------------

-type remote_types() :: typerefl:list(typerefl:boolean()).

remote_type_refl_test() ->
  ?typeEqual(typerefl:list(typerefl:boolean()), remote_types()).

%% -----------------------------------------------------------------------------

-typerefl_verify({uri/0, ?MODULE, verify_uri}).

-typerefl_from_string({ipv4_address/0, inet, parse_ipv4_address}).
-typerefl_pretty_print({ipv4_address/0, inet, ntoa}).

-typerefl_from_string({ipv6_address/0, inet, parse_ipv6_address}).
-typerefl_pretty_print({ipv6_address/0, inet, ntoa}).

-type ignored() :: string().

-type uri() :: string().

verify_uri(Str) ->
  is_map(uri_string:parse(Str)).

verify_test() ->
  {?type_refl, #{check := Check}} = uri(),
  ?assertEqual(fun ?MODULE:verify_uri/1, Check).

%% -----------------------------------------------------------------------------

-type ipv4_address() :: {byte(), byte(), byte(), byte()}.

ipv4_address_test() ->
  {?type_refl, #{from_string := FromString, pretty_print := PrettyPrint}} = ipv4_address(),
  ?assertEqual(fun inet:parse_ipv4_address/1, FromString),
  ?assertEqual(fun inet:ntoa/1, PrettyPrint),

  ?assertMatch({ok, {127, 0, 0, 1}}, typerefl:from_string(ipv4_address(), "127.0.0.1")).

%% -----------------------------------------------------------------------------

-type ipv6_address() :: {0..65535, 0..65535, 0..65535, 0..65535,
                         0..65535, 0..65535, 0..65535, 0..65535}.

ip_address_test() ->
  {?type_refl, #{from_string := FromString, pretty_print := PrettyPrint}} = ipv6_address(),
  ?assertEqual(fun inet:parse_ipv6_address/1, FromString),
  ?assertEqual(fun inet:ntoa/1, PrettyPrint),

  ?assertMatch({ok, {0, 0, 0, 0, 0, 0, 0, 0}}, typerefl:from_string(ipv6_address(), "::")).

%% -----------------------------------------------------------------------------

exports_test() ->
    Exports = ?MODULE:module_info(exports),
    ?assertMatch( []
                , [ {mybool, 0}
                  , {strings, 0}
                  , {myterm1, 0}
                  , {foobarbaz, 0}
                  , {simple, 1}
                  , {stupid_list, 1}
                  ] -- Exports
                ).

%% -----------------------------------------------------------------------------

-type surrogate1() :: unicode:charlist().
-type surrogate2() :: unicode:chardata().

-reflect_type([surrogate1/0, surrogate2/0]).

surrogate_test() ->
  %% Verify that the reflected type's check function is the same as in
  %% the surrogate type:
  {?type_refl, #{check := Check1}} = typerefl:unicode_charlist(),
  {?type_refl, #{check := Check1}} = surrogate1(),

  {?type_refl, #{check := Check2}} = typerefl:unicode_chardata(),
  {?type_refl, #{check := Check2}} = surrogate2().

%% -----------------------------------------------------------------------------

typeEqual(ExpectedName0, A0, B0) ->
  %% 0. Check return type:
  ?assertMatch({?type_refl, #{}}, A0),
  ?assertMatch({?type_refl, #{}}, B0),
  {?type_refl, A} = A0,
  {?type_refl, B} = B0,
  %% 1. Check name of the type:
  ExpectedName = fix_name(ExpectedName0),
  Name = fix_name(maps:get(name, B)),
  ?assertEqual(ExpectedName, Name),
  %% 2. Check definition (TODO)
  %%?assertEqual((A)#type.name, (B)#type.definition),
  %% 3. Check `check' callback:
  ExpectedCheck = maps:get(check, A),
  Check = maps:get(check, B),
  ?assertEqual(ExpectedCheck, Check).

mapTypeEqual(_ExpectedName0, {?type_refl, A}, {?type_refl, B}) ->
  %% Check field specs:
  #{ fuzzy_map_fields := FA
   , strict_map_fields := SA
   } = A,
  #{ fuzzy_map_fields := FB
   , strict_map_fields := SB
   } = B,
  ?assertEqual(lists:sort(SA), lists:sort(SB)),
  ?assertEqual(lists:sort(FA), lists:sort(FB)).

fix_name(Str) ->
  [I || I <- lists:flatten(Str), I =/= $  ].
