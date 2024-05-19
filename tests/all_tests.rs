mod infra;

// Your tests go here!
success_tests! {
    {
        name: fact,
        file: "fact.snek",
        input: "10",
        expected: "3628800",
    },
    {
        name: lam0,
        file: "lam0.snek",
        input: "0",
        expected: "6",
    },
    {
        name: lam1,
        file: "lam1.snek",
        input: "0",
        expected: "50",
    },
    {
        name: lam2,
        file: "lam2.snek",
        input: "0",
        expected: "(vec 6 50)",
    },
    {
        name: lam_compose,
        file: "lam-compose.snek",
        input: "100",
        expected: "102",
    },
    {
        name: lam_fac,
        file: "lam-fac.snek",
        input: "5",
        expected: "120",
    },
    {
        name: lam_map,
        file: "lam-map.snek",
        input: "100",
        expected: "(vec 110 (vec 120 (vec 130 false)))",
    },


}

runtime_error_tests! {
    {
        name: lam_not_fun,
        file: "lam_not_fun.snek",
        input: "0",
        expected: "callee is not a function",
    },
    {
        name: lam_arity,
        file: "lam_arity.snek",
        input: "0",
        expected: "arity mismatch",
    }
}

static_error_tests! {
    {
        name: unbound,
        file: "unbound.snek",
        expected: "Unbound variable",
    }
}
