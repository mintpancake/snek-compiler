use std::fs::File;
use std::io::prelude::*;
use std::{cmp::max, env};

use expr::{Arg, Defn, Expr};
use im::{hashmap, HashMap, HashSet};

pub mod expr;

type Stack = HashMap<String, i32>;

fn test_number(code: usize) -> String {
    format!(
        "mov rcx, rax
             and rcx, 1
             cmp rcx, 0
             mov rdi, {code}
             jne label_error"
    )
}

fn label(prefix: String, count: &i32) -> String {
    format!("{prefix}_{count}")
}

const FALSE: usize = 3;
const TRUE: usize = 7;

fn compile_args(
    exprs: &Vec<Expr>,
    env: &Stack,
    sp: usize,
    count: &mut i32,
    brk: &str,
    f: &str,
) -> String {
    let args_code: Vec<String> = exprs
        .iter()
        .enumerate()
        .map(|(i, e)| {
            let e_code = compile_expr(e, env, sp + i, count, brk, false, f);
            let e_pos = sp + i;
            format!(
                "{e_code}
                 mov [rbp - 8*{e_pos}], rax",
            )
        })
        .collect();
    args_code.join("\n")
}

fn tuple_read(tag: usize, index: usize) -> String {
    format!(
        ";; TODO: check rax is pointer
             sub rax, {tag}             ; strip tag
             mov rax, [rax + 8*{index}] ; read at index"
    )
}

fn tuple_alloc(args: &Vec<Arg>) -> String {
    let mut res: Vec<String> = vec![];
    for (i, arg) in args.iter().enumerate() {
        let load_rcx = match arg {
            Arg::Con(n) => format!("mov rcx, {n}"),
            Arg::Var(i_pos) => format!("mov rcx, [rbp - 8*{i_pos}]"),
            Arg::Lbl(label) => format!("lea rcx, QWORD [rel {label}]"),
        };
        res.push(format!(
            "{load_rcx}
             mov [r11 + 8*{i}], rcx",
        ));
    }
    res.push(format!(
        "mov rax, r11
                      add r11, 8*{}",
        args.len()
    ));
    res.join("\n")
}

fn lookup_var(env: &Stack, x: &str) -> i32 {
    match env.get(x) {
        None => panic!("Unbound variable {}", x),
        Some(x_pos) => *x_pos,
    }
}

fn compile_var(env: &Stack, x: &str) -> String {
    let x_pos = lookup_var(env, x);
    format!("mov rax, [rbp - 8*{}]", x_pos)
}

fn compile_expr(
    e: &Expr,
    env: &Stack,
    sp: usize,
    count: &mut i32,
    brk: &str,
    tr: bool,
    f: &str,
) -> String {
    match e {
        Expr::Num(n) => format!("mov rax, {}", *n << 1),
        Expr::Add1(subexpr) => {
            compile_expr(subexpr, env, sp, count, brk, false, f) + "\nadd rax, 2"
        }
        Expr::Sub1(subexpr) => {
            compile_expr(subexpr, env, sp, count, brk, false, f) + "\nsub rax, 2"
        }
        Expr::Neg(subexpr) => compile_expr(subexpr, env, sp, count, brk, false, f) + "\nneg rax",
        Expr::Var(x) => compile_var(env, x),
        Expr::Let(x, e1, e2) => {
            let e1_code = compile_expr(e1, env, sp, count, brk, false, f);
            let x_pos = sp;
            let x_save = format!("mov [rbp - 8*{}], rax", x_pos);
            let new_env = env.update(x.to_string(), x_pos as i32);
            let e2_code = compile_expr(e2, &new_env, sp + 1, count, brk, tr, f);
            format!("{e1_code:}\n{x_save:}\n{e2_code:}")
        }
        Expr::Plus(e1, e2) => {
            let e1_code = compile_expr(e1, env, sp, count, brk, false, f);
            let e2_code = compile_expr(e2, env, sp + 1, count, brk, false, f);
            let test_code_1 = test_number(99);
            let test_code_2 = test_number(33);

            format!(
                "{e1_code}
                 {test_code_1}
                 mov [rbp - 8*{sp}], rax
                 {e2_code}
                 {test_code_2}
                 add rax, [rbp - 8*{sp}]
                "
            )
        }
        Expr::Mult(e1, e2) => {
            let e1_code = compile_expr(e1, env, sp, count, brk, false, f);
            let e2_code = compile_expr(e2, env, sp + 1, count, brk, false, f);
            let test_code_1 = test_number(99);
            let test_code_2 = test_number(33);
            let off = 8 * sp;
            format!(
                "{e1_code}
                 {test_code_1}
                 mov [rbp - {off}], rax
                 {e2_code}
                 {test_code_2}
                 sar rax, 1
                 imul rax, [rbp - {off}]
                "
            )
        }
        Expr::If(e_cond, e_then, e_else) => {
            *count += 1;
            let e_cond_code = compile_expr(e_cond, env, sp, count, brk, false, f);
            let e_then_code = compile_expr(e_then, env, sp, count, brk, tr, f);
            let e_else_code = compile_expr(e_else, env, sp, count, brk, tr, f);
            format!(
                "{e_cond_code}
                      cmp rax, {FALSE}
                      je label_else_{count}
                      {e_then_code}
                      jmp label_exit_{count}
                    label_else_{count}:
                      {e_else_code}
                    label_exit_{count}:"
            )
        }
        Expr::Input => {
            format!("mov rax, [rbp - 8]")
        }
        Expr::True => {
            format!("mov rax, {TRUE}")
        }
        Expr::False => {
            format!("mov rax, {FALSE}")
        }
        Expr::Eq(e1, e2) => {
            let e1_code = compile_expr(e1, env, sp, count, brk, false, f);
            let e2_code = compile_expr(e2, env, sp + 1, count, brk, false, f);
            *count += 1;
            let exit = label("eq_exit".to_string(), count);
            format!(
                "{e1_code}
                 mov [rbp - 8*{sp}], rax
                 {e2_code}
                 cmp rax, [rbp - 8*{sp}]
                 mov rax, {FALSE}
                 jne {exit}
                 mov rax, {TRUE}
               {exit}:
                "
            )
        }
        Expr::Le(e1, e2) => {
            let e1_code = compile_expr(e1, env, sp, count, brk, false, f);
            let e2_code = compile_expr(e2, env, sp + 1, count, brk, false, f);
            *count += 1;
            let exit = label("eq_exit".to_string(), count);
            format!(
                "{e1_code}
                 mov [rbp - 8*{sp}], rax
                 {e2_code}
                 cmp rax, [rbp - 8*{sp}]
                 mov rax, {FALSE}
                 jl {exit}
                 mov rax, {TRUE}
               {exit}:
                "
            )
        }
        Expr::Set(x, e) => {
            let x_pos = env.get(x).unwrap();
            let e_code = compile_expr(e, env, sp, count, brk, false, f);
            format!(
                "{e_code}
                     mov [rbp - 8*{}], rax",
                x_pos
            )
        }
        Expr::Block(es) => {
            let n = es.len();
            let e_codes: Vec<String> = es
                .iter()
                .enumerate()
                .map(|(i, e)| compile_expr(e, env, sp, count, brk, tr && i == n - 1, f))
                .collect();
            e_codes.join("\n")
        }
        Expr::Loop(e) => {
            *count += 1;
            let loop_start = label("loop_start".to_string(), count);
            let loop_exit = label("loop_exit".to_string(), count);
            let e_code = compile_expr(e, env, sp, count, &loop_exit, false, f);
            format!(
                "{loop_start}:
                        {e_code}
                        jmp {loop_start}
                     {loop_exit}:"
            )
        }
        Expr::Break(e) => {
            let e_code = compile_expr(e, env, sp, count, brk, false, f);
            format!(
                "{e_code}
                     jmp {brk}"
            )
        }
        Expr::Print(e) => {
            let e_code = compile_expr(e, env, sp, count, brk, false, f);
            format!(
                "{e_code}
                 mov rdi, rax
                 call snek_print"
            )
        }
        Expr::Vec(e1, e2) => {
            let e1 = e1.clone();
            let e2 = e2.clone();
            let exprs = vec![*e1, *e2];
            let exprs_code = compile_args(&exprs, env, sp, count, brk, f);
            let args: Vec<Arg> = (sp..sp + exprs.len()).map(|i| Arg::Var(i)).collect();
            let alloc_code = tuple_alloc(&args);
            format!(
                "{exprs_code}
                     {alloc_code}
                     add rax, 0x1"
            )
        }
        Expr::Get(e, idx) => {
            let e_code = compile_expr(e, env, sp, count, brk, false, f);
            let tuple_read = tuple_read(1, idx.val());
            format!(
                "{e_code}
                 {tuple_read}",
            )
        }
        Expr::Call(f, exprs) => {
            todo!()
        }
        Expr::Fun(defn) => compile_defn(defn, env, count),
    }
}

fn compile_exit() -> String {
    format!(
        "mov rsp, rbp
             pop rbp
             ret"
    )
}

fn compile_entry(e: &Expr, sp: usize) -> String {
    let free_vars = free_vars(e);
    let vars = expr_vars(e) + sp + free_vars.len() + 100;
    format!(
        "push rbp
         mov rbp, rsp
         sub rsp, 8*{vars}"
    )
}

fn free_vars(e: &Expr) -> HashSet<String> {
    todo!()
}

fn expr_vars(e: &Expr) -> usize {
    match e {
        Expr::Num(_) | Expr::Var(_) | Expr::Input | Expr::True | Expr::False | Expr::Fun(_) => 0,
        Expr::Add1(e)
        | Expr::Sub1(e)
        | Expr::Neg(e)
        | Expr::Set(_, e)
        | Expr::Loop(e)
        | Expr::Break(e)
        | Expr::Print(e)
        | Expr::Get(e, _) => expr_vars(e),
        Expr::Let(_, e1, e2)
        | Expr::Eq(e1, e2)
        | Expr::Le(e1, e2)
        | Expr::Plus(e1, e2)
        | Expr::Mult(e1, e2)
        | Expr::Vec(e1, e2) => max(expr_vars(e1), 1 + expr_vars(e2)),
        Expr::If(e1, e2, e3) => max(expr_vars(e1), max(expr_vars(e2), expr_vars(e3))),
        Expr::Block(es) => es.iter().map(|e| expr_vars(e)).max().unwrap(),
        Expr::Call(_, exprs) => exprs
            .iter()
            .enumerate()
            .map(|(i, e)| i + expr_vars(e))
            .max()
            .unwrap(),
    }
}

fn compile_defn(defn: &Defn, env: &Stack, count: &mut i32) -> String {
    todo!()
}

fn compile_prog(prog: &Expr) -> String {
    let mut count = 0;
    let e_entry = compile_entry(prog, 1);
    let e_code = compile_expr(
        prog,
        &hashmap! {},
        2,
        &mut count,
        "time_to_exit",
        false,
        "main",
    );
    let e_exit = compile_exit();
    format!(
        "section .text
global our_code_starts_here
extern snek_error
extern snek_print
label_error:
  push rsp
  call snek_error
our_code_starts_here:
 {e_entry}
 mov [rbp - 8], rdi
 mov r11, rsi               ;; save start of heap in r11
 {e_code}
 {e_exit}
time_to_exit:
  ret
"
    )
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();

    let in_name = &args[1];
    let out_name = &args[2];

    let mut in_file = File::open(in_name)?;
    let mut in_contents = String::new();
    in_file.read_to_string(&mut in_contents)?;

    let prog = expr::parse(&in_contents);

    let mut out_file = File::create(out_name)?;
    let asm_program = compile_prog(&prog);

    out_file.write_all(asm_program.as_bytes())?;

    Ok(())
}
