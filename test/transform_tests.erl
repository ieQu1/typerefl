-module(transform_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("typerefl/include/types.hrl").
-include_lib("typerefl/src/typerefl_int.hrl").

-typerefl_verify({url/0, is_url/0}).

-typerefl_ignore([ignored/0]).

-define(add_module(Str), atom_to_list(?MODULE) ++ ":" ++ Str).

-define(typeEqual(A, B), typeEqual(?add_module(??B), A, B)).

-define(mapTypeEqual(A, B), mapTypeEqual(?add_module(??B), A, B)).

-reflect_type([ mybool/0, myterm1/0, myterm2/0, my_int/0, my_byte/0
              , list_of_bools/0, non_empty_list_of_bools/0, mylist0/0, strings/0
              , foo_atom/0, foobarbaz/0, mytuple/0, simple/1, stupid_list/1
              , mymap/0, remote_types/0
              ]).

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

tuple_refl_test() ->
  ?typeEqual(tuple([float(), float(), xxx]), mytuple()).

%% -----------------------------------------------------------------------------

-type simple(A) :: A.

%% Recursive type is fine too:
-type stupid_list(OwO) :: {cons, OwO, stupid_list(OwO)} | nil.

higher_kind_refl_test() ->
  SimpleName = ?add_module("simple(A)"),
  typeEqual(SimpleName, atom(), simple(atom())),
  typeEqual(SimpleName, list(atom()), simple(list(atom()))),
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

%% TODO: Test special attributes

-type ignored() :: string().

-type url() :: string().

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

mapTypeEqual(ExpectedName0, {?type_refl, A}, {?type_refl, B}) ->
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
