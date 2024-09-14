-module(from_string_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("typerefl/include/types.hrl").

from_string_test() ->
  MyAtom = typerefl:alias("my_atom", atom()),
  MyString = typerefl:alias("my_string", string()),
  ?assertMatch({ok, ""}, typerefl:from_string(string(), "")),
  ?assertMatch({ok, ''}, typerefl:from_string(atom(), "")),
  ?assertMatch({ok, <<>>}, typerefl:from_string(binary(), "")),
  ?assertMatch({ok, 'foo bar'}, typerefl:from_string(atom(), "foo bar")),
  ?assertMatch({ok, 'foo bar'}, typerefl:from_string(MyAtom, "foo bar")),
  ?assertMatch({ok, "foo bar"}, typerefl:from_string(MyString, "foo bar")),
  ?assertMatch({ok, "foo"}, typerefl:from_string(string(), "foo")),
  ?assertMatch({ok, <<"foo">>}, typerefl:from_string(binary(), "foo")),
  ?assertMatch({ok, <<"foo/你好"/utf8>>}, typerefl:from_string(binary(), "foo/你好")),
  ?assertMatch({ok, <<0, 12, 3>>}, typerefl:from_string(binary(), [0, 12, 3])),

  ?assertMatch({ok, true},  typerefl:from_string(boolean(), "true")),
  ?assertMatch({ok, false}, typerefl:from_string(boolean(), "false")),
  ?assertMatch({ok, true},  typerefl:from_string(boolean(), " true ")),
  ?assertMatch({ok, false}, typerefl:from_string(boolean(), " false ")),
  ?assertMatch({error, _}, typerefl:from_string(boolean(), "}")),
  ?assertMatch({error, _}, typerefl:from_string(boolean(), ",")),

  ?assertMatch({ok, "1"}, typerefl:from_string(string(), "1")),
  ?assertMatch({ok, '1'}, typerefl:from_string(atom(), "1")),

  ?assertMatch({ok, 1}, typerefl:from_string(integer(), "1")),
  ?assertMatch({ok, 1}, typerefl:from_string(integer(), " 1 ")),
  ?assertMatch({error, _}, typerefl:from_string(integer(), " abc ")),

  ?assertMatch({ok, 1.1}, typerefl:from_string(float(), "1.1")),
  ?assertMatch({ok, 1.1}, typerefl:from_string(float(), " 1.1 ")),
  ?assertMatch({error, _}, typerefl:from_string(float(), " 1 ")),

  ?assertMatch({ok, 1.1}, typerefl:from_string(number(), "1.1")),
  ?assertMatch({ok, 1.1}, typerefl:from_string(number(), " 1.1 ")),
  ?assertMatch({ok, 1}, typerefl:from_string(number(), " 1 ")),

  ?assertMatch({error, _}, typerefl:from_string(pid(), "<0.123.0>")),
  ?assertMatch({error, _}, typerefl:from_string(port(), "#Port<0.5>")),
  ?assertMatch({error, _}, typerefl:from_string(number(), "#Ref<0.4195819181.3441426434.261872>")),

  ?assertMatch({ok, {foo, "bar", []}}, typerefl:from_string(term(), "{foo, \"bar\", []}")),
  ?assertMatch({ok, foo}, typerefl:from_string(foo, "foo")),
  ?assertMatch({error, _}, typerefl:from_string(foo, "bar")),
  ?assertMatch({ok, ''}, typerefl:from_string('', "")),
  ?assertMatch({ok, "hi"}, typerefl:from_string(typerefl:regexp_string("^hi$"), "hi")),
  ?assertMatch({ok, <<"hi">>}, typerefl:from_string(typerefl:regexp_binary("^hi$"), "hi")),
  ?assertMatch({ok, "}"}, typerefl:from_string(union(string(), boolean()), "}")),
  ?assertMatch({ok, "}"}, typerefl:from_string(union(boolean(), string()), "}")),
  ?assertMatch({error, _}, typerefl:from_string(union(boolean(), boolean()), "}")),
  ?assertMatch({ok, '}'}, typerefl:from_string(union([boolean(), foo, atom()]), "}")),
  ?assertMatch({ok, "foo"}, typerefl:from_string(union(integer(), string()), "foo")),
  ?assertMatch({ok, "foo"}, typerefl:from_string(union(string(), integer()), "foo")),
  ?assertMatch({error, _}, typerefl:from_string(union(integer(), integer()), "foo")),
  ok.

from_strings_test() ->
  %% ?assertMatch( {ok, []}
  %%             , typerefl:from_string(list(string()), "")), ??????
  ?assertMatch( {ok, [[]]}
              , typerefl:from_string(list(string()), [""])),
  ?assertMatch( {ok, ["foo", "bar"]}
              , typerefl:from_string(list(string()), ["foo", "bar"])),
  ?assertMatch( {ok, ['foo bar']}
              , typerefl:from_string(list(atom()), ["foo bar"])),
  ?assertMatch( {ok, [true]}
              , typerefl:from_string(list(boolean()), ["true"])),
  ?assertMatch( {ok, [false]}
              , typerefl:from_string(list(boolean()), ["false"])),
  ?assertMatch( {ok, ["1"]}
              , typerefl:from_string(list(string()), ["1"])),
  ?assertMatch( {ok, ['1']}
              , typerefl:from_string(list(atom()), ["1"])),
  ?assertMatch( {ok, [1]}
              , typerefl:from_string(list(integer()), ["1"])),
  ?assertMatch( {ok, [1.1]}
              , typerefl:from_string(list(float()), ["1.1"])),
  ?assertMatch( {ok, [{foo, "bar", []}]}
              , typerefl:from_string(list(term()), ["{foo, \"bar\", []}"])),
  ?assertMatch( {error, _}
              , typerefl:from_string(list(boolean()), ["}"])),
  ?assertMatch( {error, _}
              , typerefl:from_string(list(boolean()), [","])).
