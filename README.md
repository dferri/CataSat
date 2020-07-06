# CataSat
A semidecision procedure for catamorphisms. Uses [Z3](https://github.com/Z3Prover/z3) as backend.

# Usage
Pass as argument the path to a `.cata` file, or any text file written with the CataSat syntax.

```
catasat.py [-h] [-npev] [-ss] [-max MAX_ITERATIONS] [-pm] [-v] [-stf SAVE_TMP_FILE] file
```

## Options

### `-h`, `--help`
Show help message.

###  `-v`, `--verbose`
Prints more details, like depth levels and range and control conditions.

### `-pm`, `--print-model`
If a model is found, print it (implied by `--verbose`).

### `-stf OUT_FILE`, `--save-tmp-file OUT_FILE`
Save the temporary `.smt2` file produced by CataSat to `OUT_FILE`.

###  `-max ITER`, `--max-iterations ITER`
The max number of iterations to perform.

### `-npev`, `--no-partial-evaluation`
Disable partial evaluation of the catamorphisms.
This can affect performance since partially evaluating the catamorphisms may reduce the number of iterations (and the calls to Z3).

Example:
```
(+ (Length Nil) (Length (Cons 2 x)))

```
becomes:
```
(+ 0 (1 + (Length x)))
```

### -ss, --strict-selectors
Enable strict selectors, so that selectors applied to the *wrong* terms make the formula unsatisfiable.

**NOTE:** it doesn't mantain equisatisfiability

Example, the term:
```
(head x)
```
becomes:
```
y
```
with the accompanying assertions:
```
(assert (= x (Cons y ys))
```

# CataSat syntax
The `.cata` files syntax is the same as the [SMT-LIB standard](http://smtlib.cs.uiowa.edu/language.shtml), with the addition of some new commands:

```
    <new_commands> ::= "(" "define-cata" <cata_def> ")" "(" "define-range" <range_def> ")"

    <cata_def> ::= <symbol> "(" <sorted_var> ")" <sort> <match_term>

    <sorted_var> ::= "(" <symbol> <sort> ")"

    <match_term> ::= "(" "match" <term> "(" <match_case>+ ")" ")"

    <match_case> ::= "(" <pattern> <term> ")"

    <pattern> ::= <symbol> | "(" <symbol> <symbol>* ")"

    <range_def> ::= "(" <var_cata>+ ")" <term>

    <var_cata> ::= "(" <symbol> <symbol> ")"
```

See [examples](examples) for some actual `.cata` files.

## Example

You can see the effectiveness of partial evaluation by checking [partial_eval.cata](examples/partial_eval.cata).

With partial evaluation CataSat returns `UNSAT` at depth zero.
```
$ python catasat.py examples/partial_eval.cata -v
```

Without partial evaluation it takes CataSat 4 iterations to return `UNSAT`.
```
$ python catasat.py examples/partial_eval.cata -v -npev
```
