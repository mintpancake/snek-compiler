# [Fer-de-lance](https://ucsd-cse231.github.io/sp24/week8/index.html)

> The description is copied from UCSD CSE 231 Compiler Construction Spring 24 [course website](https://ucsd-cse231.github.io/sp24/week8/index.html). Thanks to Professor [Ranjit Jhala](https://ranjitjhala.github.io/) and Professor [Joe Politz](https://jpolitz.github.io/). 

Fer-de-lance, aka FDL, aka **F**unctions **D**efined by **L**ambdas, is an egg-eater-like language with anonymous, first-class functions.    

## [Additions](#additions)

`fdl` starts with the `egg-eater` and has two significant syntactic changes.

1.  First, it makes function definitions `(defn (f x1 ... xn) e)` a form of _expression_ that can be bound to a variable and passed as a parameter,
    
2.  Second, it adds the notion of a `(fn (x1 ... xn) e)` expression for defining anonymous or nameless functions,
    

```rust
pub enum Expr {
    ...
    Fun(Defn),
    Call(String, Vec<Expr>),
}


pub struct Defn {
    pub name: Option<String>,
    pub params: Vec<String>,
    pub body: Box<Expr>,
}
```

For example

```clojure
(defn (f it)
  (it 5))

(let (foo (fn (z) (* z 10))) 
  (f foo)
)
```

```clojure
(defn (compose f g) 
  (fn (x) (f (g x))))

(defn (inc x) 
  (+ x 1))

(let (f (compose inc inc))
  (f input))
```

You can write recursive functions as

```clojure
(defn (f it x)
  (it x))

(defn (fac n) 
  (if (= n 0) 1 (* n (fac (+ n -1)))))

(f fac input)
```


## [Semantics](#semantics)

Functions should behave just as if they followed a substitution-based semantics. This means that when a function is constructed, the program should store any "free" variables that they reference that aren't part of the argument list, for use when the function is called. This naturally matches the semantics of function values in languages like OCaml, Haskell and Python.

## [Runtime Errors](#runtime-errors)

There are several updates to runtime errors as a result of adding first-class functions:

*   You should throw an error with `arity mismatch` when there is mismatch in the number of arguments at a call.
    
*   The value in function position may not be a function (for example, a user may erroneously apply a number), which should trigger a runtime error error that reports `not a function`.

## [Implementation](#implementation)

### [Memory Layout](#memory-layout)

Functions/Closures should be stored in the heap as a tuple

```
-----------------------------------------------
| code-ptr | arity | var1 | var2 | ... | varN | 
-----------------------------------------------
```

For example, in this program:

```clojure
(let* ((x  10)
       (y  12)
       (f  (fn (z) (+ x (+ y z))))) 
  (f 5))
```

The memory layout of the `fn` would be:

```
----------------------------------
|  <address> |  1   | 20  |  24  |
----------------------------------
```

*   There is one argument (`z`), so `1` is stored for arity.
    
*   There are two free variables—`x` and `y`—so the corresponding values are stored in contiguous addresses (`20` to represent `10` and `24` to represent 12).
    

### [Function Values](#function-values)

Function _values_ are stored in variables and registers as the address of the first word in the function's memory, but with an additional `5` (`101` in binary) added to the value to act as a tag.

Hence, the value layout is now:

```
0xWWWWWWW[www0] - Number
0xWWWWWWW[w111] - True
0xWWWWWWW[w011] - False 
0xWWWWWWW[w001] - Pair
0xWWWWWWW[w101] - Function
```

### [Computing and Storing Free Variables](#computing-and-storing-free-variables)

An important part of saving function values is figuring out the set of **free variables** that need to be stored, and storing them on the heap.

Our compiler needs to generated code to store all of the _free_ variables in a function – all the variables that are used but not defined by an argument or let binding inside the function.

So, for example, `x` is free and `y` is not in:

```
(fn (y) (+ x y))
```

In this next expression, `z` is free, but `x` and `y` are not, because `x` is bound by the `let` expression.

```
(fn (y) (let (x 10) (+ x (+ y z))))
```

Note that if these examples were the whole program, well-formedness would signal an error that these variables are unbound. However, these expressions could appear as sub-expressions in other programs, for example:

```
(let* ((x 10) 
       (f (fn (y) (+ x y)))) 
  (f 10))
```

In this program, `x` is not unbound – it has a binding in the first branch of the `let`. However, relative to the `lambda` expression, it is _free_, since there is no binding for it within the `lambda`’s arguments or body.

You should fill in the function `free_vars` that returns the set of free variables in an `Expr`.

```Haskell
fn freeVars(e: &Expr) -> HashSet<String>
```

You may need to write one or more helper functions for `free_vars`, that keep track of an environment.  
Then `free_vars` can be used when compiling `Defn` to fetch the values from the surrounding environment, and store them on the heap.

In the example of heap layout above, the `free_vars` function should return the set `hashset!{"x", "y"}`, and that information can be used in conjunction with `env` to perform the necessary `mov` instructions.

This means that the generated code for a `Defn` will look much like it did in class but with an extra step to move the stored variables into their respective tuple slots.

### [Restoring Saved Variables](#restoring-saved-variables)

The description above outlines how to **store** the free variables of a function. They also need to be **restored** when the function is called, so that each time the function is called, they can be accessed.

In this assignment we'll treat the stored variables as if they were a special kind of **local variable**, and reallocate space for them on the stack at the beginning of each function body.

So each function body will have an additional part of the prelude to `restore` **the variables onto the stack**, and their uses will be compiled just as local variables are.  
This lets us re-use much of our infrastructure of stack offsets and the environment.

The outline of work here is:

1.  At the prelude of the function body, get a reference to the function closure's address from which the free variables' values can be obtained and restored,
    
2.  Add instructions to the prelude of each function that restore the stored variables onto the stack, given this address
    
3.  Assuming this stack layout, compile the function's body in an environment that will look up all variables, whether stored, arguments, or let-bound, in the correct location
    

The second and third points are straightforward applications of ideas we've seen already – copying appropriate values from the heap into the stack, and using the environment to make variable references look at the right locations on the stack.

The first point requires a little more design work.

If we try to fill in the body of `temp_closure_1` above, we immediately run into the issue of where we should find the stored values in memory.

We'd like some way to, say, move the address of the function value into `rax` so we could start copying values onto the stack.

But how do we get access to the function value?

To solve this, we are going to augment the **calling convention** in Fer-de-lance to **pass along the closure-pointer** as the _zero-th parameter_ when calling a function.

So, for example, in call like:

```
(f 4 5)
```

We would generate code **for the caller** like:

```
mov rax, [rbp-16]  ;; (wherever 'f' is stored)
<code to check that rax is tagged 101, and has arity 2>
push 10            ;; 2nd param = 5
push 8             ;; 1st param = 4
mov rax, [rbp-16]  ;; 
push rax	   ;; 0th param = closure
sub rax, 5         ;; remove tag
mov rax, [rax]     ;; load code-pointer from closure
call rax           ;; call the function
```

Now the function's closure is available on the stack, accessible just as the 0th argument so we can use that in the prelude for restoration.
