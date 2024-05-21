use std::env;
use std::fs::File;
use std::io::prelude::*;

use sexp::*;

use im::HashMap as ImHashMap;
use std::collections::HashSet;

const NIL: &str = "nil";
const TRUE: &str = "true";
const FALSE: &str = "false";
const INPUT: &str = "input";
const LET: &str = "let";
const LET_AST: &str = "let*";
const ADD1: &str = "add1";
const SUB1: &str = "sub1";
const NEG: &str = "negate";
const ISNUM: &str = "isnum";
const ISBOOL: &str = "isbool";
const PRINT: &str = "print";
const PLUS: &str = "+";
const MINUS: &str = "-";
const TIMES: &str = "*";
const EQUAL: &str = "=";
const GREATER: &str = ">";
const GREATER_EQUAL: &str = ">=";
const LESS: &str = "<";
const LESS_EQUAL: &str = "<=";
const IF: &str = "if";
const LOOP: &str = "loop";
const BREAK: &str = "break";
const SET: &str = "set!";
const BLOCK: &str = "block";
const DEFN: &str = "defn";
const FN: &str = "fn";
const VEC: &str = "vec";
const VEC_GET: &str = "vec-get";
const VEC_SET: &str = "vec-set";

const MAX_NUM: i64 = 4611686018427387903;
const MIN_NUM: i64 = -4611686018427387904;

const NIL_LIT: i64 = 1;
const TRUE_LIT: i64 = 7;
const FALSE_LIT: i64 = 3;

const TAG_MASK_1: i64 = 1;
const TAG_MASK_2: i64 = 3;
const TAG_MASK_3: i64 = 7;
const PTR_MASK: i64 = -8;

const NUM_TAG: i64 = 0;
const BOOL_TAG: i64 = 3;
const PTR_TAG: i64 = 1;
const CLS_TAG: i64 = 5;

const NOT_A_NUM_ERROR: i64 = 1;
const TYPE_MISMATCH_ERROR: i64 = 2;
const OVERFLOW_ERROR: i64 = 3;
const OUT_OF_BOUNDS_ERROR: i64 = 4;
const ARITY_MISMATCH_ERROR: i64 = 5;
const NOT_A_FUNCTION_ERROR: i64 = 6;

const LABEL_ERROR: &str = "label_error";

const FUN_SNEK_ERROR: &str = "snek_error";
const FUN_SNEK_PRINT: &str = "snek_print";
const OUR_CODE: &str = "our_code_starts_here";

#[derive(Debug, Clone)]
enum Val {
    Reg(Reg),
    Imm(i64),
    RegOffset(Reg, i32),
    Label(String),
}

#[derive(Debug, Clone)]
enum Reg {
    RAX,
    RCX,
    RDX,
    RSP,
    RBP,
    RDI,
    RSI,
    R12,
}

#[derive(Debug, Clone)]
enum Instr {
    IMov(Val, Val),
    IAdd(Val, Val),
    ISub(Val, Val),
    IMul(Val, Val),
    SAR(Val, Val),
    SAL(Val, Val),
    CMP(Val, Val),
    NEG(Val),
    LABEL(String),
    JMP(Val),
    JE(Val),
    JNE(Val),
    JG(Val),
    JGE(Val),
    JL(Val),
    JLE(Val),
    JO(Val),
    AND(Val, Val),
    Call(Val),
    Push(Val),
    Pop(Val),
    Ret,
}

#[derive(Debug, Clone)]
enum Op1 {
    Add1,
    Sub1,
    Neg,
    IsNum,
    IsBool,
    Print,
}

#[derive(Debug, Clone)]
enum Op2 {
    Plus,
    Minus,
    Times,
    Equal,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
}

#[derive(Debug, Clone)]
struct Defn {
    pub name: Option<String>,
    pub params: Vec<String>,
    pub body: Box<Expr>,
}

#[derive(Debug, Clone)]
enum Expr {
    NIL,
    Input,
    Number(i64),
    Boolean(bool),
    Id(String),
    Let(Vec<(String, Expr)>, Box<Expr>),
    UnOp(Op1, Box<Expr>),
    BinOp(Op2, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Loop(Box<Expr>),
    Break(Box<Expr>),
    Set(String, Box<Expr>),
    Block(Vec<Expr>),
    Fun(Defn),
    Call(String, Vec<Expr>),
    Vec(Vec<Expr>),
    VecGet(Box<Expr>, Box<Expr>),
    VecSet(Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
enum Prog {
    Prog(Vec<Expr>, Expr),
}

fn valid_num(n: i64) -> bool {
    n >= MIN_NUM && n <= MAX_NUM
}

fn valid_bool(b: &str) -> bool {
    b == TRUE || b == FALSE
}

fn valid_id(x: &str) -> bool {
    if x.is_empty()
        || x == NIL
        || x == TRUE
        || x == FALSE
        || x == INPUT
        || x == LET
        || x == LET_AST
        || x == ADD1
        || x == SUB1
        || x == NEG
        || x == ISNUM
        || x == ISBOOL
        || x == PRINT
        || x == PLUS
        || x == MINUS
        || x == TIMES
        || x == EQUAL
        || x == GREATER
        || x == GREATER_EQUAL
        || x == LESS
        || x == LESS_EQUAL
        || x == IF
        || x == LOOP
        || x == BREAK
        || x == SET
        || x == BLOCK
        || x == DEFN
        || x == FN
        || x == VEC
        || x == VEC_GET
        || x == VEC_SET
    {
        panic!("Invalid: {} is a reserved keyword", x);
    }
    if x.chars().next().unwrap().is_alphabetic()
        && x.chars()
            .all(|c| c.is_alphanumeric() || c == '-' || c == '_')
    {
        return true;
    } else {
        panic!("Invalid: {} is an invalid keyword", x);
    }
}

fn parse_sexpr(s: &str) -> Prog {
    let res = parse(s);
    match res {
        Ok(sexpr) => parse_prog(&sexpr),
        Err(_) => panic!("Invalid"),
    }
}

fn parse_prog(s: &Sexp) -> Prog {
    match s {
        Sexp::List(ss) => match &ss[..] {
            [ds @ .., s1] => {
                let defns = ds.iter().map(|d| parse_defn(d)).collect();
                let expr = parse_expr(s1);
                Prog::Prog(defns, expr)
            }
            _ => panic!("Invalid"),
        },
        _ => panic!("Invalid"),
    }
}

fn parse_defn(d: &Sexp) -> Expr {
    match d {
        Sexp::List(ss) => match &ss[..] {
            [Sexp::Atom(Atom::S(fun)), Sexp::List(names), s1] if fun == DEFN => {
                let fun_name = match names.first() {
                    Some(Sexp::Atom(Atom::S(n))) if valid_id(n) => n.clone(),
                    _ => panic!("Invalid"),
                };
                let params = names
                    .iter()
                    .skip(1)
                    .map(|name| match name {
                        Sexp::Atom(Atom::S(p)) if valid_id(p) => p.clone(),
                        _ => panic!("Invalid"),
                    })
                    .collect();
                let body = Box::new(parse_expr(s1));
                Expr::Fun(Defn {
                    name: Some(fun_name),
                    params,
                    body,
                })
            }
            [Sexp::Atom(Atom::S(fun)), Sexp::List(names), s1] if fun == FN => {
                let params = names
                    .iter()
                    .map(|name| match name {
                        Sexp::Atom(Atom::S(p)) if valid_id(p) => p.clone(),
                        _ => panic!("Invalid"),
                    })
                    .collect();
                let body = Box::new(parse_expr(s1));
                Expr::Fun(Defn {
                    name: None,
                    params,
                    body,
                })
            }
            _ => panic!("Invalid"),
        },
        _ => panic!("Invalid"),
    }
}

fn parse_expr(s: &Sexp) -> Expr {
    match s {
        Sexp::Atom(Atom::S(nil)) if nil == NIL => Expr::NIL,
        Sexp::Atom(Atom::S(input)) if input == INPUT => Expr::Input,
        Sexp::Atom(Atom::I(n)) if valid_num(*n) => Expr::Number(*n),
        Sexp::Atom(Atom::S(bool)) if valid_bool(bool) => Expr::Boolean(bool == TRUE),
        Sexp::Atom(Atom::S(x)) if valid_id(x) => Expr::Id(x.clone()),
        Sexp::List(ss) => match &ss[..] {
            [Sexp::Atom(Atom::S(op)), b, s1] if op == LET => {
                Expr::Let(vec![parse_bind(b)], Box::new(parse_expr(s1)))
            }
            [Sexp::Atom(Atom::S(op)), bs, s1] if op == LET_AST => {
                Expr::Let(parse_binds(bs), Box::new(parse_expr(s1)))
            }
            [Sexp::Atom(Atom::S(op)), s1] if op == ADD1 => {
                Expr::UnOp(Op1::Add1, Box::new(parse_expr(s1)))
            }
            [Sexp::Atom(Atom::S(op)), s1] if op == SUB1 => {
                Expr::UnOp(Op1::Sub1, Box::new(parse_expr(s1)))
            }
            [Sexp::Atom(Atom::S(op)), s1] if op == NEG => {
                Expr::UnOp(Op1::Neg, Box::new(parse_expr(s1)))
            }
            [Sexp::Atom(Atom::S(op)), s1] if op == ISNUM => {
                Expr::UnOp(Op1::IsNum, Box::new(parse_expr(s1)))
            }
            [Sexp::Atom(Atom::S(op)), s1] if op == ISBOOL => {
                Expr::UnOp(Op1::IsBool, Box::new(parse_expr(s1)))
            }
            [Sexp::Atom(Atom::S(op)), s1] if op == PRINT => {
                Expr::UnOp(Op1::Print, Box::new(parse_expr(s1)))
            }
            [Sexp::Atom(Atom::S(op)), s1, s2] if op == PLUS => Expr::BinOp(
                Op2::Plus,
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
            ),
            [Sexp::Atom(Atom::S(op)), s1, s2] if op == MINUS => Expr::BinOp(
                Op2::Minus,
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
            ),
            [Sexp::Atom(Atom::S(op)), s1, s2] if op == TIMES => Expr::BinOp(
                Op2::Times,
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
            ),
            [Sexp::Atom(Atom::S(op)), s1, s2] if op == EQUAL => Expr::BinOp(
                Op2::Equal,
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
            ),
            [Sexp::Atom(Atom::S(op)), s1, s2] if op == GREATER => Expr::BinOp(
                Op2::Greater,
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
            ),
            [Sexp::Atom(Atom::S(op)), s1, s2] if op == GREATER_EQUAL => Expr::BinOp(
                Op2::GreaterEqual,
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
            ),
            [Sexp::Atom(Atom::S(op)), s1, s2] if op == LESS => Expr::BinOp(
                Op2::Less,
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
            ),
            [Sexp::Atom(Atom::S(op)), s1, s2] if op == LESS_EQUAL => Expr::BinOp(
                Op2::LessEqual,
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
            ),
            [Sexp::Atom(Atom::S(op)), s1, s2, s3] if op == IF => Expr::If(
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
                Box::new(parse_expr(s3)),
            ),
            [Sexp::Atom(Atom::S(op)), s1] if op == LOOP => Expr::Loop(Box::new(parse_expr(s1))),
            [Sexp::Atom(Atom::S(op)), s1] if op == BREAK => Expr::Break(Box::new(parse_expr(s1))),
            [Sexp::Atom(Atom::S(op)), Sexp::Atom(Atom::S(x)), s2] if op == SET && valid_id(x) => {
                Expr::Set(x.clone(), Box::new(parse_expr(s2)))
            }
            [Sexp::Atom(Atom::S(op)), ss @ ..] if op == BLOCK => Expr::Block(parse_blocks(ss)),
            [Sexp::Atom(Atom::S(op)), _, _] if op == DEFN || op == FN => parse_defn(s),
            [Sexp::Atom(Atom::S(op)), ss @ ..] if op == VEC => Expr::Vec(parse_vec(ss)),
            [Sexp::Atom(Atom::S(op)), s1, s2] if op == VEC_GET => {
                Expr::VecGet(Box::new(parse_expr(s1)), Box::new(parse_expr(s2)))
            }
            [Sexp::Atom(Atom::S(op)), s1, s2, s3] if op == VEC_SET => Expr::VecSet(
                Box::new(parse_expr(s1)),
                Box::new(parse_expr(s2)),
                Box::new(parse_expr(s3)),
            ),
            [Sexp::Atom(Atom::S(fun)), ss @ ..] if valid_id(fun) => {
                Expr::Call(fun.clone(), ss.iter().map(|s| parse_expr(s)).collect())
            }
            _ => panic!("Invalid"),
        },
        _ => panic!("Invalid"),
    }
}

fn parse_bind(s: &Sexp) -> (String, Expr) {
    match s {
        Sexp::List(ss) => match &ss[..] {
            [Sexp::Atom(Atom::S(x)), s1] if valid_id(x) => (x.clone(), parse_expr(s1)),
            _ => panic!("Invalid"),
        },
        _ => panic!("Invalid"),
    }
}

fn parse_binds(s: &Sexp) -> Vec<(String, Expr)> {
    match s {
        Sexp::List(bs) => {
            if bs.is_empty() {
                panic!("Invalid");
            }
            bs.into_iter().map(|b| parse_bind(b)).collect()
        }
        _ => panic!("Invalid"),
    }
}

fn parse_blocks(ss: &[Sexp]) -> Vec<Expr> {
    if ss.is_empty() {
        panic!("Invalid");
    }
    ss.iter().map(|s| parse_expr(s)).collect()
}

fn parse_vec(ss: &[Sexp]) -> Vec<Expr> {
    if ss.is_empty() {
        panic!("Invalid");
    }
    ss.iter().map(|s| parse_expr(s)).collect()
}

fn to_num_literal(n: i64) -> i64 {
    n << 1
}

fn to_bool_literal(b: bool) -> i64 {
    if b {
        TRUE_LIT
    } else {
        FALSE_LIT
    }
}

fn compile_num_type_check(v: Val, instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), v.clone()));
    instrs.push(Instr::AND(Val::Reg(Reg::RCX), Val::Imm(TAG_MASK_1)));
    instrs.push(Instr::CMP(Val::Reg(Reg::RCX), Val::Imm(NUM_TAG)));
    instrs.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(NOT_A_NUM_ERROR)));
    instrs.push(Instr::JNE(Val::Label(LABEL_ERROR.to_string())));
}

fn compile_ptr_type_check(v: Val, instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), v.clone()));
    instrs.push(Instr::AND(Val::Reg(Reg::RCX), Val::Imm(TAG_MASK_3)));
    instrs.push(Instr::CMP(Val::Reg(Reg::RCX), Val::Imm(PTR_TAG)));
    instrs.push(Instr::IMov(
        Val::Reg(Reg::RDI),
        Val::Imm(TYPE_MISMATCH_ERROR),
    ));
    instrs.push(Instr::JNE(Val::Label(LABEL_ERROR.to_string())));
}

fn compile_nil_ptr_check(v: Val, instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), v.clone()));
    instrs.push(Instr::CMP(Val::Reg(Reg::RCX), Val::Imm(NIL_LIT)));
    instrs.push(Instr::IMov(
        Val::Reg(Reg::RDI),
        Val::Imm(TYPE_MISMATCH_ERROR),
    ));
    instrs.push(Instr::JE(Val::Label(LABEL_ERROR.to_string())));
}

fn compile_cls_type_check(v: Val, instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), v.clone()));
    instrs.push(Instr::AND(Val::Reg(Reg::RCX), Val::Imm(TAG_MASK_3)));
    instrs.push(Instr::CMP(Val::Reg(Reg::RCX), Val::Imm(CLS_TAG)));
    instrs.push(Instr::IMov(
        Val::Reg(Reg::RDI),
        Val::Imm(NOT_A_FUNCTION_ERROR),
    ));
    instrs.push(Instr::JNE(Val::Label(LABEL_ERROR.to_string())));
}

fn compile_cls_check(v: Val, len: i64, instrs: &mut Vec<Instr>) {
    compile_cls_type_check(v.clone(), instrs);
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), v.clone()));
    instrs.push(Instr::ISub(Val::Reg(Reg::RCX), Val::Imm(CLS_TAG)));
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), Val::RegOffset(Reg::RCX, 1)));
    instrs.push(Instr::CMP(
        Val::Reg(Reg::RCX),
        Val::Imm(to_num_literal(len)),
    ));
    instrs.push(Instr::IMov(
        Val::Reg(Reg::RDI),
        Val::Imm(ARITY_MISMATCH_ERROR),
    ));
    instrs.push(Instr::JNE(Val::Label(LABEL_ERROR.to_string())));
}

fn compile_out_of_bound_check(v: Val, ptr: Val, instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), v.clone()));
    instrs.push(Instr::IMov(Val::Reg(Reg::RDX), ptr.clone()));
    instrs.push(Instr::IMov(Val::Reg(Reg::RDX), Val::RegOffset(Reg::RDX, 0)));
    instrs.push(Instr::CMP(Val::Reg(Reg::RCX), Val::Reg(Reg::RDX)));
    instrs.push(Instr::IMov(
        Val::Reg(Reg::RDI),
        Val::Imm(OUT_OF_BOUNDS_ERROR),
    ));
    instrs.push(Instr::JGE(Val::Label(LABEL_ERROR.to_string())));
}

fn compile_same_type_check(v1: Val, v2: Val, label_seq: &mut i32, instrs: &mut Vec<Instr>) {
    let my_label_seq = *label_seq;
    *label_seq += 1;
    instrs.push(Instr::LABEL(format!("label_check_num_{}", my_label_seq)));
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), v1.clone()));
    instrs.push(Instr::AND(Val::Reg(Reg::RCX), Val::Imm(TAG_MASK_1)));
    instrs.push(Instr::CMP(Val::Reg(Reg::RCX), Val::Imm(NUM_TAG)));
    instrs.push(Instr::JNE(Val::Label(format!(
        "label_check_bool_{}",
        my_label_seq
    ))));
    instrs.push(Instr::IMov(Val::Reg(Reg::RDX), v2.clone()));
    instrs.push(Instr::AND(Val::Reg(Reg::RDX), Val::Imm(TAG_MASK_1)));
    instrs.push(Instr::CMP(Val::Reg(Reg::RDX), Val::Imm(NUM_TAG)));
    instrs.push(Instr::JE(Val::Label(format!(
        "label_check_end_{}",
        my_label_seq
    ))));
    instrs.push(Instr::JNE(Val::Label(format!(
        "label_check_error_{}",
        my_label_seq
    ))));

    instrs.push(Instr::LABEL(format!("label_check_bool_{}", my_label_seq)));
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), v1.clone()));
    instrs.push(Instr::AND(Val::Reg(Reg::RCX), Val::Imm(TAG_MASK_2)));
    instrs.push(Instr::CMP(Val::Reg(Reg::RCX), Val::Imm(BOOL_TAG)));
    instrs.push(Instr::JNE(Val::Label(format!(
        "label_check_ptr_cls_{}",
        my_label_seq
    ))));
    instrs.push(Instr::IMov(Val::Reg(Reg::RDX), v2.clone()));
    instrs.push(Instr::AND(Val::Reg(Reg::RDX), Val::Imm(TAG_MASK_2)));
    instrs.push(Instr::CMP(Val::Reg(Reg::RDX), Val::Imm(BOOL_TAG)));
    instrs.push(Instr::JE(Val::Label(format!(
        "label_check_end_{}",
        my_label_seq
    ))));
    instrs.push(Instr::JNE(Val::Label(format!(
        "label_check_error_{}",
        my_label_seq
    ))));

    instrs.push(Instr::LABEL(format!(
        "label_check_ptr_cls_{}",
        my_label_seq
    )));
    instrs.push(Instr::IMov(Val::Reg(Reg::RCX), v1.clone()));
    instrs.push(Instr::AND(Val::Reg(Reg::RCX), Val::Imm(TAG_MASK_3)));
    instrs.push(Instr::IMov(Val::Reg(Reg::RDX), v2.clone()));
    instrs.push(Instr::AND(Val::Reg(Reg::RDX), Val::Imm(TAG_MASK_3)));
    instrs.push(Instr::CMP(Val::Reg(Reg::RCX), Val::Reg(Reg::RDX)));
    instrs.push(Instr::JE(Val::Label(format!(
        "label_check_end_{}",
        my_label_seq
    ))));

    instrs.push(Instr::LABEL(format!("label_check_error_{}", my_label_seq)));
    instrs.push(Instr::IMov(
        Val::Reg(Reg::RDI),
        Val::Imm(TYPE_MISMATCH_ERROR),
    ));
    instrs.push(Instr::JMP(Val::Label(LABEL_ERROR.to_string())));

    instrs.push(Instr::LABEL(format!("label_check_end_{}", my_label_seq)));
}

fn compile_overflow_check(instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(OVERFLOW_ERROR)));
    instrs.push(Instr::JO(Val::Label(LABEL_ERROR.to_string())));
}

fn compile_expr(
    e: &Expr,
    env: &ImHashMap<String, i32>,
    st_ptr: i32,
    label_seq: &mut i32,
    loop_seq: i32,
    curr_fun: &str,
    funs: &mut HashSet<String>,
    instrs: &mut Vec<Instr>,
) {
    match e {
        Expr::NIL => instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(NIL_LIT))),
        Expr::Input => {
            if curr_fun != "" {
                panic!("Input not allowed in function");
            }
            instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::RegOffset(Reg::RBP, 1)))
        }
        Expr::Number(n) => instrs.push(Instr::IMov(
            Val::Reg(Reg::RAX),
            Val::Imm(to_num_literal(*n)),
        )),
        Expr::Boolean(b) => instrs.push(Instr::IMov(
            Val::Reg(Reg::RAX),
            Val::Imm(to_bool_literal(*b)),
        )),
        Expr::Id(x) => {
            if !env.contains_key(x) {
                panic!("Unbound variable identifier {}", x);
            }
            let x_pos = *env.get(x).unwrap();
            instrs.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, x_pos),
            ));
        }
        Expr::Let(bs, e1) => {
            let mut bound_ids = HashSet::<String>::new();
            let mut new_env = env.clone();
            let mut new_st_ptr = st_ptr;
            for (x, e) in bs {
                if bound_ids.contains(x) {
                    panic!("Duplicate binding");
                }
                compile_expr(
                    e, &new_env, new_st_ptr, label_seq, loop_seq, curr_fun, funs, instrs,
                );
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, new_st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                bound_ids.insert(x.clone());
                new_env = new_env.update(x.clone(), new_st_ptr);
                new_st_ptr += 1;
            }
            compile_expr(
                e1, &new_env, new_st_ptr, label_seq, loop_seq, curr_fun, funs, instrs,
            );
        }
        Expr::UnOp(op, e1) => match op {
            Op1::Add1 => {
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::IAdd(Val::Reg(Reg::RAX), Val::Imm(to_num_literal(1))));
                compile_overflow_check(instrs);
            }
            Op1::Sub1 => {
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::ISub(Val::Reg(Reg::RAX), Val::Imm(to_num_literal(1))));
                compile_overflow_check(instrs);
            }
            Op1::Neg => {
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::NEG(Val::Reg(Reg::RAX)));
                compile_overflow_check(instrs);
            }
            Op1::IsNum => {
                let my_label_seq = *label_seq;
                *label_seq += 1;
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                instrs.push(Instr::AND(Val::Reg(Reg::RAX), Val::Imm(TAG_MASK_1)));
                instrs.push(Instr::CMP(Val::Reg(Reg::RAX), Val::Imm(NUM_TAG)));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(TRUE_LIT)));
                instrs.push(Instr::JE(Val::Label(format!("label_end_{}", my_label_seq))));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(FALSE_LIT)));
                instrs.push(Instr::LABEL(format!("label_end_{}", my_label_seq)));
            }
            Op1::IsBool => {
                let my_label_seq = *label_seq;
                *label_seq += 1;
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                instrs.push(Instr::AND(Val::Reg(Reg::RAX), Val::Imm(TAG_MASK_2)));
                instrs.push(Instr::CMP(Val::Reg(Reg::RAX), Val::Imm(BOOL_TAG)));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(TRUE_LIT)));
                instrs.push(Instr::JE(Val::Label(format!("label_end_{}", my_label_seq))));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(FALSE_LIT)));
                instrs.push(Instr::LABEL(format!("label_end_{}", my_label_seq)));
            }
            Op1::Print => {
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                instrs.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
                instrs.push(Instr::Call(Val::Label(FUN_SNEK_PRINT.to_string())));
            }
        },
        Expr::BinOp(op, e1, e2) => match op {
            Op2::Plus => {
                compile_expr(e2, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                compile_expr(
                    e1,
                    env,
                    st_ptr + 1,
                    label_seq,
                    loop_seq,
                    curr_fun,
                    funs,
                    instrs,
                );
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::IAdd(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, st_ptr),
                ));
                compile_overflow_check(instrs);
            }
            Op2::Minus => {
                compile_expr(e2, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                compile_expr(
                    e1,
                    env,
                    st_ptr + 1,
                    label_seq,
                    loop_seq,
                    curr_fun,
                    funs,
                    instrs,
                );
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::ISub(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, st_ptr),
                ));
                compile_overflow_check(instrs);
            }
            Op2::Times => {
                compile_expr(e2, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                compile_expr(
                    e1,
                    env,
                    st_ptr + 1,
                    label_seq,
                    loop_seq,
                    curr_fun,
                    funs,
                    instrs,
                );
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::SAR(Val::Reg(Reg::RAX), Val::Imm(1)));
                instrs.push(Instr::IMul(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, st_ptr),
                ));
                compile_overflow_check(instrs);
            }
            Op2::Equal => {
                let my_label_seq = *label_seq;
                *label_seq += 1;
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                compile_expr(
                    e2,
                    env,
                    st_ptr + 1,
                    label_seq,
                    loop_seq,
                    curr_fun,
                    funs,
                    instrs,
                );
                compile_same_type_check(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                    label_seq,
                    instrs,
                );
                instrs.push(Instr::CMP(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(TRUE_LIT)));
                instrs.push(Instr::JE(Val::Label(format!("label_end_{}", my_label_seq))));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(FALSE_LIT)));
                instrs.push(Instr::LABEL(format!("label_end_{}", my_label_seq)));
            }
            Op2::Greater => {
                let my_label_seq = *label_seq;
                *label_seq += 1;
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                compile_expr(
                    e2,
                    env,
                    st_ptr + 1,
                    label_seq,
                    loop_seq,
                    curr_fun,
                    funs,
                    instrs,
                );
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::CMP(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(TRUE_LIT)));
                instrs.push(Instr::JG(Val::Label(format!("label_end_{}", my_label_seq))));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(FALSE_LIT)));
                instrs.push(Instr::LABEL(format!("label_end_{}", my_label_seq)));
            }
            Op2::GreaterEqual => {
                let my_label_seq = *label_seq;
                *label_seq += 1;
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                compile_expr(
                    e2,
                    env,
                    st_ptr + 1,
                    label_seq,
                    loop_seq,
                    curr_fun,
                    funs,
                    instrs,
                );
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::CMP(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(TRUE_LIT)));
                instrs.push(Instr::JGE(Val::Label(format!(
                    "label_end_{}",
                    my_label_seq
                ))));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(FALSE_LIT)));
                instrs.push(Instr::LABEL(format!("label_end_{}", my_label_seq)));
            }
            Op2::Less => {
                let my_label_seq = *label_seq;
                *label_seq += 1;
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                compile_expr(
                    e2,
                    env,
                    st_ptr + 1,
                    label_seq,
                    loop_seq,
                    curr_fun,
                    funs,
                    instrs,
                );
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::CMP(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(TRUE_LIT)));
                instrs.push(Instr::JL(Val::Label(format!("label_end_{}", my_label_seq))));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(FALSE_LIT)));
                instrs.push(Instr::LABEL(format!("label_end_{}", my_label_seq)));
            }
            Op2::LessEqual => {
                let my_label_seq = *label_seq;
                *label_seq += 1;
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                compile_expr(
                    e2,
                    env,
                    st_ptr + 1,
                    label_seq,
                    loop_seq,
                    curr_fun,
                    funs,
                    instrs,
                );
                compile_num_type_check(Val::Reg(Reg::RAX), instrs);
                instrs.push(Instr::CMP(
                    Val::RegOffset(Reg::RBP, st_ptr),
                    Val::Reg(Reg::RAX),
                ));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(TRUE_LIT)));
                instrs.push(Instr::JLE(Val::Label(format!(
                    "label_end_{}",
                    my_label_seq
                ))));
                instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(FALSE_LIT)));
                instrs.push(Instr::LABEL(format!("label_end_{}", my_label_seq)));
            }
        },
        Expr::If(e_cond, e_then, e_else) => {
            let my_label_seq = *label_seq;
            *label_seq += 1;
            compile_expr(
                e_cond, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs,
            );
            instrs.push(Instr::CMP(Val::Reg(Reg::RAX), Val::Imm(FALSE_LIT)));
            let label_else = format!("label_else_{}", my_label_seq);
            instrs.push(Instr::JE(Val::Label(label_else.clone())));
            compile_expr(
                e_then, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs,
            );
            let label_end = format!("label_end_{}", my_label_seq);
            instrs.push(Instr::JMP(Val::Label(label_end.clone())));
            instrs.push(Instr::LABEL(label_else.clone()));
            compile_expr(
                e_else, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs,
            );
            instrs.push(Instr::LABEL(label_end.clone()));
        }
        Expr::Loop(e1) => {
            let my_label_seq = *label_seq;
            *label_seq += 1;
            let label_loop = format!("label_loop_{}", my_label_seq);
            instrs.push(Instr::LABEL(label_loop.clone()));
            compile_expr(
                e1,
                env,
                st_ptr,
                label_seq,
                my_label_seq,
                curr_fun,
                funs,
                instrs,
            );
            instrs.push(Instr::JMP(Val::Label(label_loop.clone())));
            instrs.push(Instr::LABEL(format!("label_end_{}", my_label_seq)));
        }
        Expr::Break(e1) => {
            if loop_seq == -1 {
                panic!("Cannot break outside of loop");
            }
            compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
            instrs.push(Instr::JMP(Val::Label(format!("label_end_{}", loop_seq))));
        }
        Expr::Set(x, e1) => {
            if !env.contains_key(x) {
                panic!("Unbound variable identifier {}", x);
            }
            compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
            let x_pos = *env.get(x).unwrap();
            instrs.push(Instr::IMov(
                Val::RegOffset(Reg::RBP, x_pos),
                Val::Reg(Reg::RAX),
            ));
        }
        Expr::Block(es) => {
            for e1 in es {
                compile_expr(e1, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs);
            }
        }
        Expr::Call(fun, es) => {
            if !env.contains_key(fun) {
                panic!("Undefined function {}", fun);
            }
            let fun_pos = *env.get(fun).unwrap();
            let len = es.len() as i64;

            instrs.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, fun_pos),
            ));
            compile_cls_check(Val::Reg(Reg::RAX), len, instrs);

            for (i, e1) in es.iter().enumerate() {
                let new_st_ptr = st_ptr + (i as i32);
                compile_expr(
                    e1, env, new_st_ptr, label_seq, loop_seq, curr_fun, funs, instrs,
                );
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, new_st_ptr),
                    Val::Reg(Reg::RAX),
                ));
            }

            for i in (0..es.len()).rev() {
                instrs.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, st_ptr + i as i32),
                ));
                instrs.push(Instr::Push(Val::Reg(Reg::RAX)));
            }

            instrs.push(Instr::IMov(
                Val::Reg(Reg::RCX),
                Val::RegOffset(Reg::RBP, fun_pos),
            ));
            instrs.push(Instr::Push(Val::Reg(Reg::RCX)));
            instrs.push(Instr::ISub(Val::Reg(Reg::RCX), Val::Imm(CLS_TAG)));
            instrs.push(Instr::IMov(Val::Reg(Reg::RCX), Val::RegOffset(Reg::RCX, 0)));
            instrs.push(Instr::Call(Val::Reg(Reg::RCX)));
            instrs.push(Instr::IAdd(Val::Reg(Reg::RSP), Val::Imm(8 * (1 + len))));
        }
        Expr::Fun(d) => {
            if let Some(fun) = &d.name {
                if funs.contains(fun) {
                    panic!("Duplicate function definition {}", fun);
                }
                funs.insert(fun.clone());
            }
            compile_defn(env, d, label_seq, funs, instrs);
        }
        Expr::Vec(es) => {
            for (i, e1) in es.iter().enumerate() {
                let new_st_ptr = st_ptr + (i as i32);
                compile_expr(
                    e1, env, new_st_ptr, label_seq, loop_seq, curr_fun, funs, instrs,
                );
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::RBP, new_st_ptr),
                    Val::Reg(Reg::RAX),
                ));
            }
            instrs.push(Instr::IMov(
                Val::RegOffset(Reg::R12, 0),
                Val::Imm(to_num_literal(es.len() as i64)),
            ));
            for i in 0..es.len() {
                instrs.push(Instr::IMov(
                    Val::Reg(Reg::RCX),
                    Val::RegOffset(Reg::RBP, st_ptr + (i as i32)),
                ));
                instrs.push(Instr::IMov(
                    Val::RegOffset(Reg::R12, 1 + i as i32),
                    Val::Reg(Reg::RCX),
                ));
            }
            instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Reg(Reg::R12)));
            instrs.push(Instr::IAdd(Val::Reg(Reg::RAX), Val::Imm(PTR_TAG)));
            instrs.push(Instr::IAdd(
                Val::Reg(Reg::R12),
                Val::Imm(8 * (1 + es.len() as i64)),
            ));
        }
        Expr::VecGet(e_vec, e_index) => {
            compile_expr(
                e_vec, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs,
            );
            compile_ptr_type_check(Val::Reg(Reg::RAX), instrs);
            compile_nil_ptr_check(Val::Reg(Reg::RAX), instrs);
            instrs.push(Instr::ISub(Val::Reg(Reg::RAX), Val::Imm(PTR_TAG)));
            instrs.push(Instr::IMov(
                Val::RegOffset(Reg::RBP, st_ptr),
                Val::Reg(Reg::RAX),
            ));
            compile_expr(
                e_index,
                env,
                st_ptr + 1,
                label_seq,
                loop_seq,
                curr_fun,
                funs,
                instrs,
            );
            compile_num_type_check(Val::Reg(Reg::RAX), instrs);
            compile_out_of_bound_check(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, st_ptr),
                instrs,
            );
            instrs.push(Instr::SAL(Val::Reg(Reg::RAX), Val::Imm(2)));
            instrs.push(Instr::IMov(
                Val::Reg(Reg::RCX),
                Val::RegOffset(Reg::RBP, st_ptr),
            ));
            instrs.push(Instr::IAdd(Val::Reg(Reg::RCX), Val::Imm(8)));
            instrs.push(Instr::IAdd(Val::Reg(Reg::RCX), Val::Reg(Reg::RAX)));
            instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::RegOffset(Reg::RCX, 0)));
        }
        Expr::VecSet(e_vec, e_index, e_val) => {
            compile_expr(
                e_vec, env, st_ptr, label_seq, loop_seq, curr_fun, funs, instrs,
            );
            compile_ptr_type_check(Val::Reg(Reg::RAX), instrs);
            compile_nil_ptr_check(Val::Reg(Reg::RAX), instrs);
            instrs.push(Instr::ISub(Val::Reg(Reg::RAX), Val::Imm(PTR_TAG)));
            instrs.push(Instr::IMov(
                Val::RegOffset(Reg::RBP, st_ptr),
                Val::Reg(Reg::RAX),
            ));
            compile_expr(
                e_index,
                env,
                st_ptr + 1,
                label_seq,
                loop_seq,
                curr_fun,
                funs,
                instrs,
            );
            compile_num_type_check(Val::Reg(Reg::RAX), instrs);
            compile_out_of_bound_check(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, st_ptr),
                instrs,
            );
            instrs.push(Instr::SAL(Val::Reg(Reg::RAX), Val::Imm(2)));
            instrs.push(Instr::IMov(
                Val::Reg(Reg::RCX),
                Val::RegOffset(Reg::RBP, st_ptr),
            ));
            instrs.push(Instr::IAdd(Val::Reg(Reg::RCX), Val::Imm(8)));
            instrs.push(Instr::IAdd(Val::Reg(Reg::RCX), Val::Reg(Reg::RAX)));
            instrs.push(Instr::IMov(
                Val::RegOffset(Reg::RBP, st_ptr),
                Val::Reg(Reg::RCX),
            ));
            compile_expr(
                e_val,
                env,
                st_ptr + 1,
                label_seq,
                loop_seq,
                curr_fun,
                funs,
                instrs,
            );
            instrs.push(Instr::IMov(
                Val::Reg(Reg::RCX),
                Val::RegOffset(Reg::RBP, st_ptr),
            ));
            instrs.push(Instr::IMov(Val::RegOffset(Reg::RCX, 0), Val::Reg(Reg::RAX)));
        }
    }
}

fn check_defn(d: &Defn, label_seq: &mut i32) -> String {
    let Defn {
        name,
        params,
        body: _,
    } = d;
    let mut param_set = HashSet::<String>::new();
    for p in params {
        if param_set.contains(p) {
            panic!("Duplicate parameter {}", p);
        }
        param_set.insert(p.clone());
    }
    let fun;
    match name {
        Some(f) => {
            fun = f.clone();
        }
        None => {
            fun = format!("$anon_{}", *label_seq);
            *label_seq += 1;
        }
    }
    fun
}

fn init_defn_env(fun: String, params: &Vec<String>, xs: &Vec<String>) -> ImHashMap<String, i32> {
    let mut env = ImHashMap::<String, i32>::new();
    for (i, p) in params.iter().enumerate() {
        env = env.update(p.clone(), -(3 + i as i32));
    }
    env = env.update(fun.clone(), -2);
    for (i, x) in xs.iter().enumerate() {
        env = env.update(x.clone(), 1 + i as i32);
    }
    env
}

fn compile_free_vars(xs: &Vec<String>, instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(
        Val::Reg(Reg::RCX),
        Val::RegOffset(Reg::RBP, -2),
    ));
    instrs.push(Instr::ISub(Val::Reg(Reg::RCX), Val::Imm(CLS_TAG)));
    for (i, _) in xs.iter().enumerate() {
        instrs.push(Instr::IMov(
            Val::Reg(Reg::RAX),
            Val::RegOffset(Reg::RCX, 2 + i as i32),
        ));
        instrs.push(Instr::IMov(
            Val::RegOffset(Reg::RBP, 1 + i as i32),
            Val::Reg(Reg::RAX),
        ));
    }
}

fn compile_closure(
    env: &ImHashMap<String, i32>,
    fun: &String,
    arity: i64,
    xs: &Vec<String>,
    instrs: &mut Vec<Instr>,
) {
    instrs.push(Instr::IMov(
        Val::Reg(Reg::RAX),
        Val::Label(format!("fun_start_{}", fun)),
    ));
    instrs.push(Instr::IMov(Val::RegOffset(Reg::R12, 0), Val::Reg(Reg::RAX)));
    instrs.push(Instr::IMov(
        Val::RegOffset(Reg::R12, 1),
        Val::Imm(to_num_literal(arity)),
    ));
    for (i, x) in xs.iter().enumerate() {
        if !env.contains_key(x) {
            panic!("Unbound variable identifier {}", x);
        }
        let x_pos = *env.get(x).unwrap();
        instrs.push(Instr::IMov(
            Val::Reg(Reg::RAX),
            Val::RegOffset(Reg::RBP, x_pos),
        ));
        instrs.push(Instr::IMov(
            Val::RegOffset(Reg::R12, 2 + i as i32),
            Val::Reg(Reg::RAX),
        ));
    }
    instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Reg(Reg::R12)));
    instrs.push(Instr::IAdd(Val::Reg(Reg::RAX), Val::Imm(5)));
    instrs.push(Instr::IAdd(
        Val::Reg(Reg::R12),
        Val::Imm(8 * (2 + xs.len() as i64)),
    ));
}

fn compile_defn(
    env: &ImHashMap<String, i32>,
    d: &Defn,
    label_seq: &mut i32,
    funs: &mut HashSet<String>,
    instrs: &mut Vec<Instr>,
) {
    let Defn {
        name: _,
        params,
        body: e,
    } = d;
    let fun = check_defn(d, label_seq);
    let arity = params.len() as i64;
    let free_xs: Vec<String> = find_free_vars_defn(d).into_iter().collect();
    let new_env = init_defn_env(fun.clone(), params, &free_xs);

    instrs.push(Instr::JMP(Val::Label(format!("fun_finish_{}", fun))));
    instrs.push(Instr::LABEL(format!("fun_start_{}", fun)));
    compile_entry(instrs, free_xs.len() as i32 + estimate_stack_size(e));
    instrs.push(Instr::LABEL(format!("fun_body_{}", fun)));
    compile_free_vars(&free_xs, instrs);
    compile_expr(
        e,
        &new_env,
        1 + free_xs.len() as i32,
        label_seq,
        -1,
        &fun,
        funs,
        instrs,
    );
    instrs.push(Instr::LABEL(format!("fun_end_{}", fun)));
    compile_exit(instrs);
    instrs.push(Instr::LABEL(format!("fun_finish_{}", fun)));
    compile_closure(env, &fun, arity, &free_xs, instrs);
}

fn compile_entry(instrs: &mut Vec<Instr>, stack_size: i32) {
    instrs.push(Instr::Push(Val::Reg(Reg::RBP)));
    instrs.push(Instr::IMov(Val::Reg(Reg::RBP), Val::Reg(Reg::RSP)));
    instrs.push(Instr::ISub(
        Val::Reg(Reg::RSP),
        Val::Imm(8 * stack_size as i64),
    ));
}

fn compile_exit(instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::RBP)));
    instrs.push(Instr::Pop(Val::Reg(Reg::RBP)));
    instrs.push(Instr::Ret);
}

fn compile_in(instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(Val::RegOffset(Reg::RBP, 1), Val::Reg(Reg::RDI)));
    instrs.push(Instr::IMov(Val::RegOffset(Reg::RBP, 2), Val::Reg(Reg::R12)));
    instrs.push(Instr::IMov(Val::Reg(Reg::R12), Val::Reg(Reg::RSI)));
    instrs.push(Instr::IAdd(Val::Reg(Reg::R12), Val::Imm(7)));
    instrs.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(PTR_MASK)));
    instrs.push(Instr::AND(Val::Reg(Reg::R12), Val::Reg(Reg::RAX)));
}

fn compile_out(instrs: &mut Vec<Instr>) {
    instrs.push(Instr::IMov(Val::Reg(Reg::R12), Val::RegOffset(Reg::RBP, 2)));
}

fn check_prog(prog: &Prog) -> (Vec<Defn>, Expr, HashSet<String>) {
    let (defns, expr) = match prog {
        Prog::Prog(ds, e) => {
            let mut defns = Vec::new();
            for d1 in ds {
                match d1 {
                    Expr::Fun(d) => defns.push(d.clone()),
                    _ => panic!("Invalid"),
                }
            }
            (defns, e.clone())
        }
    };
    let mut funs = HashSet::new();
    for d in &defns {
        if let Some(fun) = &d.name {
            if funs.contains(fun) {
                panic!("Duplicate function definition {}", fun);
            }
            funs.insert(fun.clone());
        }
    }
    (defns, expr, funs)
}

fn init_env(defns: &Vec<Defn>) -> (ImHashMap<String, i32>, i32) {
    let mut env = ImHashMap::<String, i32>::new();
    let mut num_bound = 0;
    for d in defns {
        if let Some(fun) = &d.name {
            env = env.update(fun.clone(), num_bound + 3);
            num_bound += 1;
        }
    }
    (env, num_bound)
}

fn compile_global_defns(
    defns: &Vec<Defn>,
    env: &ImHashMap<String, i32>,
    label_seq: &mut i32,
    funs: &mut HashSet<String>,
    instrs: &mut Vec<Instr>,
) {
    for d in defns {
        compile_defn(env, d, label_seq, funs, instrs);
        if let Some(fun) = &d.name {
            instrs.push(Instr::IMov(
                Val::RegOffset(Reg::RBP, *env.get(fun).unwrap()),
                Val::Reg(Reg::RAX),
            ));
        }
    }
}

fn compile(prog: &Prog) -> String { // TODO: Do not support mutual calls
    let (defns, expr, mut funs) = check_prog(prog);
    let mut instrs = Vec::new();
    let (env, num_bound) = init_env(&defns);
    let mut label_seq = 0;

    instrs.push(Instr::LABEL(LABEL_ERROR.to_string()));
    instrs.push(Instr::Call(Val::Label(FUN_SNEK_ERROR.to_string())));
    instrs.push(Instr::LABEL(OUR_CODE.to_string()));

    compile_entry(&mut instrs, 2 + num_bound + estimate_stack_size(&expr));
    compile_in(&mut instrs);
    compile_global_defns(&defns, &env, &mut label_seq, &mut funs, &mut instrs);
    compile_expr(
        &expr,
        &env,
        3 + num_bound,
        &mut label_seq,
        -1,
        "",
        &mut funs,
        &mut instrs,
    );
    compile_out(&mut instrs);
    compile_exit(&mut instrs);

    instrs
        .iter()
        .map(instr_to_str)
        .collect::<Vec<String>>()
        .join("\n")
}

fn find_free_vars_defn(d: &Defn) -> HashSet<String> {
    match d {
        Defn {
            name,
            params,
            body: e,
        } => {
            let mut s = find_free_vars(e);
            for p in params {
                s.remove(p);
            }
            if let Some(f) = name {
                s.remove(f);
            }
            s
        }
    }
}

fn find_free_vars(e: &Expr) -> HashSet<String> {
    match e {
        Expr::NIL | Expr::Input | Expr::Number(_) | Expr::Boolean(_) => HashSet::new(),
        Expr::Id(x) => HashSet::from_iter([x.clone()]),
        Expr::Fun(d) => find_free_vars_defn(d),
        Expr::Let(bs, e1) => {
            let mut s = HashSet::new();
            let mut xs = HashSet::new();
            for (x, e1) in bs {
                let s1 = find_free_vars(e1);
                s.extend(s1.difference(&xs).cloned());
                xs.insert(x.clone());
            }
            let s1 = find_free_vars(e1);
            s.extend(s1.difference(&xs).cloned());
            s
        }
        Expr::UnOp(_, e1) | Expr::Loop(e1) | Expr::Break(e1) | Expr::Set(_, e1) => {
            find_free_vars(e1)
        }
        Expr::BinOp(_, e1, e2) | Expr::VecGet(e1, e2) => {
            let mut s = find_free_vars(e1);
            s.extend(find_free_vars(e2));
            s
        }
        Expr::If(e1, e2, e3) | Expr::VecSet(e1, e2, e3) => {
            let mut s = find_free_vars(e1);
            s.extend(find_free_vars(e2));
            s.extend(find_free_vars(e3));
            s
        }
        Expr::Block(es) | Expr::Vec(es) => {
            let mut s = HashSet::new();
            for e1 in es {
                s.extend(find_free_vars(e1));
            }
            s
        }
        Expr::Call(fun, es) => {
            let mut s = HashSet::from_iter([fun.clone()]);
            for e1 in es {
                s.extend(find_free_vars(e1));
            }
            s
        }
    }
}

fn estimate_stack_size(e: &Expr) -> i32 {
    match e {
        Expr::NIL
        | Expr::Input
        | Expr::Number(_)
        | Expr::Boolean(_)
        | Expr::Id(_)
        | Expr::Fun(_) => 0,
        Expr::Let(bs, e1) => {
            let mut max_size = 0;
            for (i, (_, e)) in bs.iter().enumerate() {
                max_size = max_size
                    .max(i as i32 + estimate_stack_size(e))
                    .max((i + 1) as i32);
            }
            max_size.max(bs.len() as i32 + estimate_stack_size(e1))
        }
        Expr::UnOp(_, e1) => estimate_stack_size(e1),
        Expr::BinOp(_, e1, e2) | Expr::VecGet(e1, e2) => {
            1 + estimate_stack_size(e1).max(estimate_stack_size(e2))
        }
        Expr::If(e_cond, e_then, e_else) => estimate_stack_size(e_cond)
            .max(estimate_stack_size(e_then))
            .max(estimate_stack_size(e_else)),
        Expr::Loop(e1) | Expr::Break(e1) | Expr::Set(_, e1) => estimate_stack_size(e1),
        Expr::Block(es) => {
            let mut max_size = 0;
            for e1 in es {
                max_size = max_size.max(estimate_stack_size(e1));
            }
            max_size
        }
        Expr::Call(_, es) | Expr::Vec(es) => {
            let mut max_size = 0;
            for (i, e1) in es.iter().enumerate() {
                max_size = max_size
                    .max(i as i32 + estimate_stack_size(e1))
                    .max((i + 1) as i32);
            }
            max_size
        }
        Expr::VecSet(e_vec, e_index, e_val) => {
            1 + estimate_stack_size(e_vec)
                .max(estimate_stack_size(e_index))
                .max(estimate_stack_size(e_val))
        }
    }
}

fn instr_to_str(i: &Instr) -> String {
    match i {
        Instr::IMov(v1, v2) => format!("  mov {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::IAdd(v1, v2) => format!("  add {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ISub(v1, v2) => format!("  sub {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::IMul(v1, v2) => format!("  imul {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::SAR(v1, v2) => format!("  sar {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::SAL(v1, v2) => format!("  sal {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::CMP(v1, v2) => format!("  cmp {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::NEG(v) => format!("  neg {}", val_to_str(v)),
        Instr::LABEL(l) => format!("{}:", l),
        Instr::JMP(l) => format!("  jmp {}", val_to_str(l)),
        Instr::JE(l) => format!("  je {}", val_to_str(l)),
        Instr::JNE(l) => format!("  jne {}", val_to_str(l)),
        Instr::JG(l) => format!("  jg {}", val_to_str(l)),
        Instr::JGE(l) => format!("  jge {}", val_to_str(l)),
        Instr::JL(l) => format!("  jl {}", val_to_str(l)),
        Instr::JLE(l) => format!("  jle {}", val_to_str(l)),
        Instr::JO(l) => format!("  jo {}", val_to_str(l)),
        Instr::AND(v1, v2) => format!("  and {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::Call(f) => format!("  call {}", val_to_str(f)),
        Instr::Push(v) => format!("  push {}", val_to_str(v)),
        Instr::Pop(v) => format!("  pop {}", val_to_str(v)),
        Instr::Ret => "  ret".to_string(),
    }
}

fn val_to_str(v: &Val) -> String {
    match v {
        Val::Reg(r) => match r {
            Reg::RAX => "rax".to_string(),
            Reg::RCX => "rcx".to_string(),
            Reg::RDX => "rdx".to_string(),
            Reg::RSP => "rsp".to_string(),
            Reg::RBP => "rbp".to_string(),
            Reg::RDI => "rdi".to_string(),
            Reg::RSI => "rsi".to_string(),
            Reg::R12 => "r12".to_string(),
        },
        Val::Imm(n) => format!("{}", n),
        Val::RegOffset(r, n) => match r {
            Reg::RSP => format!("qword [rsp - 8*{}]", n),
            Reg::RBP => format!("qword [rbp - 8*{}]", n),
            Reg::RAX => format!("qword [rax + 8*{}]", n),
            Reg::RCX => format!("qword [rcx + 8*{}]", n),
            Reg::RDX => format!("qword [rdx + 8*{}]", n),
            Reg::R12 => format!("qword [r12 + 8*{}]", n),
            _ => panic!("Invalid"),
        },
        Val::Label(l) => l.clone(),
    }
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();

    let in_name = &args[1];
    let out_name = &args[2];

    let mut in_file = File::open(in_name)?;
    let mut in_str = String::new();
    in_file.read_to_string(&mut in_str)?;

    let prog = parse_sexpr(&format!("({})", in_str));
    let result = compile(&prog);

    let asm_program = format!(
        "section .text\nglobal {}\nextern {}\nextern {}\n{}\n",
        OUR_CODE, FUN_SNEK_ERROR, FUN_SNEK_PRINT, result
    );

    let mut out_file = File::create(out_name)?;
    out_file.write_all(asm_program.as_bytes())?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const IN_STR: &str = "";

    #[test]
    fn test_parse_sexpr() {
        let expr = parse_sexpr(&format!("({})", IN_STR));
        println!("{:?}", expr);
    }

    #[test]
    fn test_compile() {
        let expr = parse_sexpr(&format!("({})", IN_STR));
        println!("{}", compile(&expr));
    }
}
