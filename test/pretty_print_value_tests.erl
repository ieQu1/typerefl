-module(pretty_print_value_tests).

-export([print_bar/1]).

-include_lib("eunit/include/eunit.hrl").
-include_lib("typerefl/include/types.hrl").

-typerefl_pretty_print({bar/0, ?MODULE, print_bar}).

-type foo(A) :: {foo, A}.

-type bar() :: bar | foo(bar).

-reflect_type([bar/0]).

print_bar({foo, A}) ->
  "[" ++ print_bar(A) ++ "]";
print_bar(bar) ->
  "bar".

default_print_test() ->
  ?assertEqual("{foo,bar}",
               lists:flatten(
                 typerefl:pretty_print_value(tuple(), {foo, bar}))).

override_print_test() ->
  ?assertEqual("bar",
               lists:flatten(
                 typerefl:pretty_print_value(bar(), bar))),
  ?assertEqual("[[bar]]",
               lists:flatten(
                 typerefl:pretty_print_value(bar(), {foo, {foo, bar}}))).

print_ip4_address_test() ->
  ?assertEqual("127.0.0.1",
               typerefl:pretty_print_value(typerefl:ip_address(), {127, 0, 0, 1})),
  ?assertEqual("127.0.0.1",
               typerefl:pretty_print_value(typerefl:ip4_address(), {127, 0, 0, 1})).

print_ip6_address_test() ->
  ?assertEqual("::",
               typerefl:pretty_print_value(typerefl:ip_address(), {0, 0, 0, 0, 0, 0, 0, 0})),
  ?assertEqual("::",
               typerefl:pretty_print_value(typerefl:ip6_address(), {0, 0, 0, 0, 0, 0, 0, 0})),
  ?assertEqual("be::1",
               typerefl:pretty_print_value(typerefl:ip_address(), {16#be, 0, 0, 0, 0, 0, 0, 1})),
  ?assertEqual("be::1",
               typerefl:pretty_print_value(typerefl:ip6_address(), {16#be, 0, 0, 0, 0, 0, 0, 1})).
