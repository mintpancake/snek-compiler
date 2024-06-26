use std::env;
use std::mem;

static mut HEAP: [u64; 100000] = [0; 100000];

const MAX_NUM: i64 = 4611686018427387903;
const MIN_NUM: i64 = -4611686018427387904;

const NIL_LIT: i64 = 1;
const TRUE_LIT: i64 = 7;
const FALSE_LIT: i64 = 3;

const TAG_MASK_1: i64 = 1;
const TAG_MASK_3: i64 = 7;

const NUM_TAG: i64 = 0;
const PTR_TAG: i64 = 1;
const CLS_TAG: i64 = 5;

const NOT_A_NUM_ERROR: i64 = 1;
const TYPE_MISMATCH_ERROR: i64 = 2;
const OVERFLOW_ERROR: i64 = 3;
const OUT_OF_BOUNDS_ERROR: i64 = 4;
const ARITY_MISMATCH_ERROR: i64 = 5;
const NOT_A_FUNCTION_ERROR: i64 = 6;

#[link(name = "our_code")]
extern "C" {
    // The \x01 here is an undocumented feature of LLVM that ensures
    // it does not add an underscore in front of the name.
    // Courtesy of Max New (https://maxsnew.com/teaching/eecs-483-fa22/hw_adder_assignment.html)
    #[link_name = "\x01our_code_starts_here"]
    fn our_code_starts_here(input: i64, heap: *mut u64) -> i64;
}

#[no_mangle]
#[export_name = "\x01snek_error"]
pub fn snek_error(errcode: i64) {
    if errcode == NOT_A_NUM_ERROR {
        eprintln!("invalid argument: not a number");
    } else if errcode == TYPE_MISMATCH_ERROR {
        eprintln!("invalid argument: type mismatch");
    } else if errcode == OVERFLOW_ERROR {
        eprintln!("overflow");
    } else if errcode == OUT_OF_BOUNDS_ERROR {
        eprintln!("index out of bounds");
    } else if errcode == ARITY_MISMATCH_ERROR {
        eprintln!("arity mismatch");
    } else if errcode == NOT_A_FUNCTION_ERROR {
        eprintln!("not a function");
    } else {
        eprintln!("unknown error code: {}", errcode);
    }
    std::process::exit(errcode as i32);
}

#[no_mangle]
#[export_name = "\x01snek_print"]
pub fn snek_print(val: i64) -> i64 {
    print_inline(val);
    println!();
    return val;
}

fn print_inline(val: i64) {
    if val == NIL_LIT {
        print!("nil");
    } else if val == FALSE_LIT {
        print!("false");
    } else if val == TRUE_LIT {
        print!("true");
    } else if val & TAG_MASK_1 == NUM_TAG {
        print!("{}", val >> 1);
    } else if val & TAG_MASK_3 == PTR_TAG {
        let ptr: *const i64 = unsafe { mem::transmute::<i64, *const i64>(val - PTR_TAG) };
        let len = unsafe { *ptr } >> 1;
        print!("(vec ");
        for i in 0..len {
            print_inline(unsafe { *ptr.add(i as usize + 1) });
            if i != len - 1 {
                print!(" ");
            }
        }
        print!(")");
    } else if val & TAG_MASK_3 == CLS_TAG {
        let ptr: *const i64 = unsafe { mem::transmute::<i64, *const i64>(val - CLS_TAG) };
        let fun = unsafe { *ptr };
        print!("fn:{}", fun);
    } else {
        print!("unknown");
    }
}

fn parse_input(input: &str) -> i64 {
    if input == "false" {
        FALSE_LIT
    } else if input == "true" {
        TRUE_LIT
    } else {
        match input.parse::<i64>() {
            Ok(n) => {
                if n > MAX_NUM || n < MIN_NUM {
                    eprintln!("overflow");
                    std::process::exit(OVERFLOW_ERROR as i32);
                }
                n << 1
            }
            Err(_) => {
                eprintln!("invalid input");
                std::process::exit(NOT_A_NUM_ERROR as i32);
            }
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let input = if args.len() == 2 { &args[1] } else { "false" };
    let input = parse_input(&input);

    let i: i64 = unsafe { our_code_starts_here(input, HEAP.as_mut_ptr()) };
    snek_print(i);
}
