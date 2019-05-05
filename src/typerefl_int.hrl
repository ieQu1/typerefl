-ifndef(TYPEREFL_HRL).
-define(TYPEREFL_HRL, true).

-define(typerefl_fix(Name, Args, Self, Body),
        typerefl:fix_t(Name, fun ?FUNCTION_NAME/?FUNCTION_ARITY, fun(Self) -> Body end, Args)).

-endif.
