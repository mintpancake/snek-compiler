use std::env;
use std::mem;

static mut HEAP: [u64; 100000] = [0; 100000];

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
    const NOT_A_NUM_ERROR: i64 = 1;
    const TYPE_MISMATCH_ERROR: i64 = 2;
    const OVERFLOW_ERROR: i64 = 3;
    const OUT_OF_BOUNDS_ERROR: i64 = 4;

    if errcode == NOT_A_NUM_ERROR || errcode == TYPE_MISMATCH_ERROR {
        eprintln!("invalid argument");
    } else if errcode == OVERFLOW_ERROR {
        eprintln!("overflow");
    } else if errcode == OUT_OF_BOUNDS_ERROR {
        eprintln!("index out of bounds");
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
    if val == 1 {
        print!("nil");
    } else if val == 3 {
        print!("false");
    } else if val == 7 {
        print!("true");
    } else if val & 1 == 0 {
        print!("{}", val >> 1);
    } else {
        let ptr: *const i64 = unsafe { mem::transmute::<i64, *const i64>(val - 1) };
        let len = unsafe { *ptr } >> 1;
        print!("(vec ");
        for i in 0..len {
            print_inline(unsafe { *ptr.add(i as usize + 1) });
            if i != len - 1 {
                print!(" ");
            }
        }
        print!(")");
    }
}

fn parse_input(input: &str) -> i64 {
    const MAX_NUM: i64 = 4611686018427387903;
    const MIN_NUM: i64 = -4611686018427387904;

    if input == "false" {
        3
    } else if input == "true" {
        7
    } else {
        match input.parse::<i64>() {
            Ok(n) => {
                if n > MAX_NUM || n < MIN_NUM {
                    eprintln!("overflow");
                    std::process::exit(3);
                }
                n << 1
            }
            Err(_) => {
                eprintln!("invalid input");
                std::process::exit(1);
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
