-ifndef(LEE_TYPES_HRL).
-define(LEE_TYPES_HRL, true).

-import(typerefl,
        [ any/0, atom/0, binary/0, boolean/0, float/0, function/0
        , integer/0, list/0, list/1, map/0, nonempty_list/1, number/0
        , pid/0, port/0, reference/0, term/0, tuple/0, byte/0
        , char/0, arity/0, module/0, non_neg_integer/0
        , string/0, nil/0, map/1, maybe_improper_list/0
        , maybe_improper_list/2, nonempty_maybe_improper_list/0
        , nonempty_maybe_improper_list/2, nonempty_string/0
        , iolist/0, iodata/0, union/2, union/1, tuple/1, range/2
        ]).

%-compile({parse_transform, lee_transform}).

-endif.
