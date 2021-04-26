-module(check_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("typerefl/include/types.hrl").

-define(valid(Type, Term),
        ?assertMatch( ok
                    , typerefl:typecheck(Type, Term)
                    )).

-define(invalid(Type, Term),
        ?assertMatch( {error, _}
                    , typerefl:typecheck(Type, Term)
                    )).

-type simple(A) :: A.

%% Recursive type is fine too:
-type stupid_list(OwO, UwU) :: {cons, OwO, stupid_list(OwO, UwU)} | UwU.

-type stupid_list(A) :: stupid_list(A, nil).

-reflect_type([simple/1, stupid_list/1]).

concrete_atom_test() ->
  ?valid(true, true),
  ?valid(false, false),
  ?invalid(foo, 1),
  ?invalid(foo, []),
  ?invalid(foo, bar).

bool_test() ->
  ?valid(boolean(), true),
  ?valid(boolean(), false),
  ?invalid(boolean(), 1),
  ?invalid(boolean(), {}),
  ?invalid(boolean(), foo).

integer_test() ->
  ?valid(integer(), -1),
  ?valid(integer(), 1000),
  ?valid(integer(), 0),
  ?invalid(integer(), 1.0),
  ?invalid(integer(), foo),
  ?valid(range(-1, 1), 1),
  ?valid(range(-1, 1), -1),
  ?invalid(range(-1, 1), -2),
  ?invalid(range(-1, 1), 2),
  ?valid(non_neg_integer(), 0),
  ?valid(non_neg_integer(), 1),
  ?invalid(non_neg_integer(), -1).

union_test() ->
  T = union(boolean(), {integer()}),
  ?valid(T, {1}),
  ?valid(T, true),
  ?valid(T, false),
  ?invalid(T, foo).

term_test() ->
  ?valid(term(), 1),
  ?valid(term(), 1.1),
  ?valid(term(), {1, 2, [], foo}),
  ?valid(term(), [foo, 1, [] | gg]).

atom_test() ->
  ?valid(atom(), foo),
  ?valid(atom(), bar),
  ?invalid(atom(), {}),
  ?invalid(atom(), 1).

list_test() ->
  ?valid(list(), []),
  ?valid(nonempty_list(integer()), [1, 2, 3]),
  ?invalid(nonempty_list(term()), []),
  UnionL = [union(boolean(), integer())],
  ?valid(UnionL, [true, false, 1, 10, -1]),
  ?invalid(UnionL, [true, false, 1, bar]),
  ?invalid(list(), [foo, bar | baz]),
  ?valid(maybe_improper_list(), [1|foo]),
  ?invalid(maybe_improper_list(atom(), atom()), foo),
  ?valid(maybe_improper_list(atom(), atom()), [foo|bar]),
  ?invalid(maybe_improper_list(atom(), atom()), [1|bar]),
  ?invalid(maybe_improper_list(atom(), atom()), [foo]),
  ?invalid(maybe_improper_list(atom(), atom()), [foo|1]).

string_test() ->
  ?valid(string(), "this is a string"),
  ?valid(string(), "(✿ ┛O‿‿O)┛彡♥   ¯\_(ツ)_/¯"),
  ?invalid(string(), "foo" ++ [bar, {}] ++ "baz"),
  ?invalid(string(), [-1, 2]),
  ?valid(nonempty_string(), "A"),
  ?invalid(nonempty_string(), "").

printable_test() ->
  ?valid(printable_unicode_list(), ""),
  ?valid(printable_unicode_list(), "foo"),
  ?valid(printable_unicode_list(), "(✿ ┛O‿‿O)┛彡♥   ¯\_(ツ)_/¯"),
  ?invalid(printable_unicode_list(), [1, 0]),
  ?valid(printable_latin1_list(), ""),
  ?valid(printable_latin1_list(), "foo"),
  ?invalid(printable_latin1_list(), "(✿ ┛O‿‿O)┛彡♥   ¯\_(ツ)_/¯"),
  ?invalid(printable_latin1_list(), [1, 0]).

iolist_test() ->
  ?valid(iolist(), "uh-oh"),
  ?valid(iolist(), io_lib:format("A ~p ~s", [{foo, bar, 1}, ["1"]])).

tuple_test() ->
  ?valid(tuple(), {}),
  ?valid(tuple(), {foo, 1, []}),
  ?invalid(tuple(), 1),
  ?invalid(tuple(), []),
  ?valid(tuple([]), {}),
  ?invalid(tuple([]), {1}),
  T = {atom(), integer()},
  ?valid(T, {foo, 1}),
  ?valid(T, {false, -1}),
  ?invalid(T, {false, -1, 5}),
  ?invalid(T, {false}),
  ?invalid(T, {false, "1"}).

binary_test() ->
  ?valid(binary(), <<>>),
  ?valid(binary(), <<"foo">>),
  ?invalid(binary(), "fooo"),
  ?invalid(binary(), 1).

map_test() ->
  T = #{atom() => string()},
  ?valid(T, #{}),
  ?valid(T, #{foo => "bar"}),
  ?invalid(T, #{ foo => "bar"
               , "bar" => foo
               , baz => "quux"
               }),
  ?invalid(T, #{ foo => 1
               , bar => "bar"
               }).

exact_map_test() ->
  T = map([ {strict, foo, boolean()}
          , {strict, bar, string()}
          ]),
  ?valid(T, #{foo => true, bar => "bar"}),
  ?valid(T, #{foo => false, bar => []}),
  ?invalid(T, #{foo => foo, bar => "bar"}),
  ?invalid(T, #{foo => true}),
  ?invalid(T, #{foo => true, bar => 1}).

higher_kind_test() ->
  %% Simple:
  ?valid(simple(atom()), foo),
  ?valid(simple(atom()), bar),
  ?invalid(simple(atom()), 1),
  ?invalid(simple(atom()), <<>>),
  %% StupidList:
  T1 = stupid_list(atom()),
  T2 = stupid_list(integer()),
  ?valid(T1, nil),
  ?valid(T2, nil),
  ?valid(T1, {cons, foo, {cons, bar, nil}}),
  ?valid(T2, {cons, 1, {cons, 2, {cons, 3, nil}}}),
  ?invalid(T1, foo),
  ?invalid(T1, {cons, foo, {cons, bar, foo}}),
  ?invalid(T1, {cons, foo, {cons, 1, nil}}),
  ok.


re_string_test() ->
  ?valid(typerefl:regexp_string(""), "foo"),
  ?valid(typerefl:regexp_string("fo+"), "foo"),
  ?valid(typerefl:regexp_string("^(foo|bar)+$"), "foofoobarbar"),

  ?invalid(typerefl:regexp_string(""), bar),
  ?invalid(typerefl:regexp_string(""), 1),
  ?invalid(typerefl:regexp_string(""), [30, 30, foo]),
  ?invalid(typerefl:regexp_string("^foo$"), "fooo"),
  ?invalid(typerefl:regexp_string("^foo$"), <<"foo">>).

re_binary_test() ->
  ?valid(typerefl:regexp_binary(""), <<"foo">>),
  ?valid(typerefl:regexp_binary("fo+"), <<"foo">>),
  ?valid(typerefl:regexp_binary("^(foo|bar)+$"), <<"foofoobarbar">>),

  ?invalid(typerefl:regexp_binary(""), bar),
  ?invalid(typerefl:regexp_binary(""), 1),
  ?invalid(typerefl:regexp_binary("foo"), <<"bar">>),
  ?invalid(typerefl:regexp_binary("^foo$"), "foo").

ip4_address_test() ->
  Type = typerefl:ip4_address(),
  ?assertMatch({ok, {127, 0, 0, 1}}, typerefl:from_string(Type, "127.0.0.1")),
  ?assertMatch({error, _}, typerefl:from_string(Type, ".0.0.1")),
  ?valid(Type, {255, 255, 255, 255}),
  ?valid(Type, {0, 0, 0, 0}),
  ?invalid(Type, {256, 256, 256, 256}),
  ?invalid(Type, {100, -1, 0, 0}),
  ?invalid(Type, {0, 0, 0}),
  ?invalid(Type, foo).

ip6_address_test() ->
  Type = typerefl:ip6_address(),
  ?assertMatch({ok, {0, 0, 0, 0, 0, 0, 0, 0}}, typerefl:from_string(Type, "::")),
  ?assertMatch({error, _}, typerefl:from_string(Type, ":a")),
  ?valid(Type, {0, 0, 0, 0, 0, 0, 0, 0}),
  ?valid(Type, {65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535}),
  ?invalid(Type, {0, 0, 0, 0}),
  ?invalid(Type, {0, 0, 0, 0, 0, 0, -1, 0}),
  ?invalid(Type, {65535, 65535, 65535, 65535, 65535, 65535, 65535, 65536}),
  ?invalid(Type, foo).


ip_address_test() ->
  Type = typerefl:ip_address(),
  ?assertMatch({ok, {127, 0, 0, 1}}, typerefl:from_string(Type, "127.0.0.1")),
  ?assertMatch({ok, {0, 0, 0, 0, 0, 0, 0, 0}}, typerefl:from_string(Type, "::")),
  ?assertMatch({error, _}, typerefl:from_string(Type, ".0.0.1")),
  ?valid(Type, {255, 255, 255, 255}),
  ?valid(Type, {0, 0, 0, 0}),
  ?valid(Type, {0, 0, 0, 0, 0, 0, 0, 0}),
  ?valid(Type, {65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535}),
  ?invalid(Type, {256, 256, 256, 256}),
  ?invalid(Type, {100, -1, 0, 0}),
  ?invalid(Type, {0, 0, 0}),
  ?invalid(Type, {65535, 65535, 65535, 65535, 65535, 65535, 65535, 65536}),
  ?invalid(Type, foo).
