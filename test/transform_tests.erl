-module(transform_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("typerefl/include/types.hrl").
-include_lib("typerefl/src/typerefl_int.hrl").

-typerefl_verify({url/0, is_url/0}).

-typerefl_ignore([ignored/0]).

-define(add_module(Str), atom_to_list(?MODULE) ++ ":" ++ Str).

-define(typeEqual(A, B), typeEqual(?add_module(??B), A, B)).

-reflect_type([ mybool/0, myterm1/0, myterm2/0, my_int/0, my_byte/0
              , list_of_bools/0, non_empty_list_of_bools/0, mylist0/0, strings/0
              , foo_atom/0, foobarbaz/0, mytuple/0, simple/1, stupid_list/1
              , mymap1/0, remote_types/0
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

map_refl_test() ->
  ?typeEqual(map(), mymap1()).

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
  FixName = fun(Str) -> [I || I <- lists:flatten(Str)
                                , I =/= $  ]
            end,
  ExpectedName = FixName(ExpectedName0),
  Name = FixName(maps:get(name, B)),
  ?assertEqual(ExpectedName, Name),
  %% 2. Check definition (TODO)
  %%?assertEqual((A)#type.name, (B)#type.definition),
  %% 3. Check `check' callback:
  ExpectedCheck = maps:get(check, A),
  Check = maps:get(check, B),
  ?assertEqual(ExpectedCheck, Check).
