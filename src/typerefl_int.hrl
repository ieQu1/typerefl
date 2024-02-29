-ifndef(TYPEREFL_HRL).
-define(TYPEREFL_HRL, true).

-record(thunk,
        { function :: fun((list(), atom()) -> _)
        , args = [] :: list()
        }).

-record(lazy_type,
        { name  :: typerefl:typename()
        , thunk :: function()
        , args  :: list()
        }).

-define(type_refl, '$type_refl').

-define(type_var(A), {'$type_var', A}).

-define(is_type_refl(Term), (element(1, Term) =:= ?type_refl)).

-endif.
