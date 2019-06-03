-module(print_type_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("typerefl/include/types.hrl").

-type foo(A) :: {foo, A}.

-type bar() :: bar | foo(bar).

-reflect_type([bar/0]).

nil_test() ->
  ?assertMatch( "[]"
              , lists:flatten(typerefl:print([]))
              ).

tuple_0_test() ->
  ?assertMatch( "{}"
              , lists:flatten(typerefl:print({}))
              ).

tuple_test() ->
  ?assertMatch( "{foo, bar}"
              , lists:flatten(typerefl:print({foo, bar}))
              ).

list_test() ->
  ?assertMatch( "[foo]"
              , lists:flatten(typerefl:print(list(foo)))
              ).

nonempty_list_test() ->
  ?assertMatch( "[foo,...]"
              , lists:flatten(typerefl:print(nonempty_list(foo)))
              ).

union_test() ->
  ?assertMatch( "foo | bar"
              , lists:flatten(typerefl:print(union(foo, bar)))
              ).

byte_test() ->
  ?assertMatch( "byte() when\n"
                "  byte() :: 0..255."
              , lists:flatten(typerefl:print(byte()))
              ).

iolist_test() ->
  ?assertMatch( "iolist() when\n"
                "  byte() :: 0..255,\n"
                "  iolist() :: maybe_improper_list(iolist() | binary() | byte(), binary() | [])."
              , lists:flatten(typerefl:print(iolist()))
              ).

%% TODO: Correct printing
%% bar_test() ->
%%   ?assertMatch( "print_type_tests:bar() when\n"
%%                 "  print_type_tests:bar() :: print_type_tests:foo(bar) | bar,\n"
%%                 "  print_type_tests:foo(A) :: {foo, A}."
%%               , lists:flatten(typerefl:print(bar()))
%%               ).

%% TODO: Incorrect printing
bar_test() ->
  ?assertMatch( "print_type_tests:bar() when\n"
                "  print_type_tests:bar() :: print_type_tests:foo(bar) | bar,\n"
                "  print_type_tests:foo(bar) :: {foo, bar}."
              , lists:flatten(typerefl:print(bar()))
              ).
