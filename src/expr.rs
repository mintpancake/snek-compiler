use sexp::Atom::*;
use sexp::*;

#[derive(Debug, Clone)]
pub struct Defn {
    pub name: Option<String>,
    pub params: Vec<String>,
    pub body: Box<Expr>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Num(i32),
    Add1(Box<Expr>),
    Sub1(Box<Expr>),
    Neg(Box<Expr>),
    Var(String),
    Let(String, Box<Expr>, Box<Expr>),
    Plus(Box<Expr>, Box<Expr>),
    Mult(Box<Expr>, Box<Expr>),
    Input,
    True,
    False,
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Set(String, Box<Expr>),
    Block(Vec<Expr>),
    Loop(Box<Expr>),
    Break(Box<Expr>),
    Print(Box<Expr>),
    Vec(Box<Expr>, Box<Expr>),
    Get(Box<Expr>, Index),
    Call(String, Vec<Expr>),
    Fun(Defn),
}

#[derive(Debug, Clone)]
pub enum Index {
    Zero,
    One,
}

impl Index { 
    pub fn val(&self) -> usize { 
        match self {
            Index::Zero => 0,
            Index::One => 1,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Arg {
    Var(usize),  // variable on stack frame at rbp - 8*i 
    Lbl(String), // code label 
    Con(usize),  // constant
}
pub fn num(n: i32) -> Expr {
    Expr::Num(n)
}

pub fn add1(e: Expr) -> Expr {
    Expr::Add1(Box::new(e))
}

pub fn sub1(e: Expr) -> Expr {
    Expr::Sub1(Box::new(e))
}

pub fn negate(e: Expr) -> Expr {
    Expr::Neg(Box::new(e))
}

pub fn expr0() -> Expr {
    add1(sub1(num(5)))
}

pub fn expr1() -> Expr {
    negate(add1(num(5)))
}

pub fn plus(e1: Expr, e2: Expr) -> Expr {
    Expr::Plus(Box::new(e1), Box::new(e2))
}

pub fn mult(e1: Expr, e2: Expr) -> Expr {
    Expr::Mult(Box::new(e1), Box::new(e2))
}

pub fn eq(e1: Expr, e2: Expr) -> Expr {
    Expr::Eq(Box::new(e1), Box::new(e2))
}

pub fn le(e1: Expr, e2: Expr) -> Expr {
    Expr::Le(Box::new(e1), Box::new(e2))
}

pub fn ite(e1: Expr, e2: Expr, e3: Expr) -> Expr {
    Expr::If(Box::new(e1), Box::new(e2), Box::new(e3))
}

fn parse_bind(s: &Sexp) -> (String, Expr) {
    match s {
        Sexp::List(vec) => match &vec[..] {
            [Sexp::Atom(S(x)), e] => (x.to_string(), parse_expr(e)),
            _ => panic!("parse error"),
        },
        _ => panic!("parse error"),
    }
}

fn parse_ident(s: &Sexp) -> String {
    match s {
        Sexp::Atom(S(x)) => x.to_string(),
        _ => panic!("parse error"),
    }
}

pub fn parse_defn(s: &Sexp) -> Expr {
    let Sexp::List(es) = s else {
        panic!("syntax error: expected a list")
    };
    match &es[..] {
        [Sexp::Atom(S(op)), Sexp::List(xs), body] if op == "defn" => {
            let [name, params @ ..] = &xs[..] else {
                panic!("missing function name");
            };
            let body = Box::new(parse_expr(body));
            let name = parse_ident(name);
            let params = params.iter().map(parse_ident).collect();
            Expr::Fun(Defn {
                name: Some(name),
                params,
                body,
            })
        }
        [Sexp::Atom(S(op)), Sexp::List(xs), body] if op == "fn" => {
            let [params @ ..] = &xs[..]; 
            let body = Box::new(parse_expr(body));
            let params = params.iter().map(parse_ident).collect();
            Expr::Fun(Defn {
                name: None,
                params,
                body,
            })
        }


        _ => panic!("syntax error: expected a list of 4 elements: {s}"),
    }
}

fn parse_prog(e: &Sexp) -> Expr {
    let Sexp::List(es) = e else {
        panic!("syntax error: expected a list")
    };

    if let [defs @ .., expr] = &es[..] {
        let defs = defs.iter().map(|e| parse_defn(e)).collect();
        let expr = Box::new(parse_expr(expr));
        prog(defs, expr)
    } else {
        panic!("syntax error: program must contain a main expression")
    }
}

fn prog(defs: Vec<Expr>, expr: Box<Expr>) -> Expr {
    let mut res = *expr;
    for def in defs.into_iter().rev() {
        if let Expr::Fun(Defn { name, .. }) = &def {
            res = Expr::Let(name.clone().unwrap(), Box::new(def), Box::new(res));
        } else {
            panic!("syntax error: expected a function definition")
        }
    }
    res
}

fn parse_index(s: &Sexp) -> Index {
    match s {
        Sexp::Atom(I(0)) => Index::Zero,
        Sexp::Atom(I(1)) => Index::One,
        _ => panic!("parse error: {s}"),
    }
}

fn parse_expr(s: &Sexp) -> Expr {
    match s {
        Sexp::Atom(I(n)) => num(i32::try_from(*n).unwrap()),

        Sexp::Atom(S(s)) if s == "input" => Expr::Input,
        Sexp::Atom(S(s)) if s == "true" => Expr::True,
        Sexp::Atom(S(s)) if s == "false" => Expr::False,

        Sexp::Atom(S(s)) => Expr::Var(s.clone()),
        Sexp::List(vec) => match &vec[..] {
            [Sexp::Atom(S(op)), e] if op == "add1" => add1(parse_expr(e)),
            [Sexp::Atom(S(op)), e] if op == "sub1" => sub1(parse_expr(e)),
            [Sexp::Atom(S(op)), e] if op == "negate" => negate(parse_expr(e)),
            [Sexp::Atom(S(op)), e] if op == "loop" => Expr::Loop(Box::new(parse_expr(e))),
            [Sexp::Atom(S(op)), e] if op == "print" => Expr::Print(Box::new(parse_expr(e))),
            [Sexp::Atom(S(op)), e] if op == "break" => Expr::Break(Box::new(parse_expr(e))),
            [Sexp::Atom(S(op)), e1, e2] if op == "+" => plus(parse_expr(e1), parse_expr(e2)),
            [Sexp::Atom(S(op)), e1, e2] if op == "*" => mult(parse_expr(e1), parse_expr(e2)),
            [Sexp::Atom(S(op)), e1, e2] if op == "=" => eq(parse_expr(e1), parse_expr(e2)),
            [Sexp::Atom(S(op)), e1, e2] if op == "<=" => le(parse_expr(e1), parse_expr(e2)),
            [Sexp::Atom(S(op)), e1, e2, e3] if op == "if" => {
                ite(parse_expr(e1), parse_expr(e2), parse_expr(e3))
            }
            [Sexp::Atom(S(op)), bind, e2] if op == "let" => {
                let (x, e1) = parse_bind(bind);
                let e2 = parse_expr(e2);
                Expr::Let(x, Box::new(e1), Box::new(e2))
            }
            [Sexp::Atom(S(op)), Sexp::List(binds), e] if op == "let*" => {
                let xes :Vec<(String, Expr)> = binds.iter().map(parse_bind).collect();
                let mut res = parse_expr(e);
                for (x, e) in xes.into_iter().rev() {
                    res = Expr::Let(x, Box::new(e), Box::new(res))
                }
                res
            }


            [Sexp::Atom(S(op)), Sexp::Atom(S(x)), e] if op == "set!" => {
                Expr::Set(x.to_string(), Box::new(parse_expr(e)))
            }
            [Sexp::Atom(S(op)), exprs @ ..] if op == "block" => {
                Expr::Block(exprs.into_iter().map(parse_expr).collect())
            }
            [Sexp::Atom(S(op)), e1, e2] if op == "vec" => {
                Expr::Vec(Box::new(parse_expr(e1)), Box::new(parse_expr(e2)))
            }
            [Sexp::Atom(S(op)), e1, e2] if op == "vec-get" => {
                Expr::Get(Box::new(parse_expr(e1)), parse_index(e2))
            }
            [Sexp::Atom(S(op)), _, _] if op == "defn" || op == "fn" => {
                parse_defn(s)
            }
            [Sexp::Atom(S(f)), exprs @ ..] => {
                Expr::Call(f.to_string(), exprs.into_iter().map(parse_expr).collect())
            }
            _ => panic!("parse error (1) {}", s),
        },
        _ => panic!("parse error (2) {}", s),
    }
}

pub fn parse(s: &str) -> Expr {
    let s = format!("({})", s);
    let s = sexp::parse(&s).unwrap_or_else(|_| panic!("invalid s-expr"));
    parse_prog(&s)
}
