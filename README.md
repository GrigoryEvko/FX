FX
==

Graded dependently-typed programming language with native compilation
to x86, ARM, and WebAssembly.  Nineteen type dimensions — usage,
effects, security, protocols, lifetimes, and fourteen others — are
checked simultaneously by a single grade-checking algorithm.  Release
builds require all code to be verified.  The same source language
describes software, synthesizable hardware, and the contracts between
systems.


Properties
----------

- Deny-by-default capability model.  Mutation, allocation, IO, public
  exposure, and duplication require explicit grants in the type.
- Exact decimal arithmetic by default.  IEEE floats are opt-in.
  Integers are arbitrary precision.
- Errors are algebraic effects (`Fail`), not special operators.
  Propagation is automatic through the effect system.
- State machines and data contracts are first-class declarations
  with compiler-verified properties.
- Bit-precise dependent types for hardware.  Register files,
  pipelines, and clock domains are typed constructs that synthesize
  to Verilog.
- Constant-time verification.  The CT effect proves execution traces
  are independent of secret-graded inputs.
- Five-level proof automation: type checking, SMT, lemma hints,
  tactics, manual proofs.  Most code requires no manual proof work.


Example
-------

```
fn merge_sort<a: type>(xs: list(a)) : list(a)
  where Ord(a);
  pre length(xs) > 0;
  post r => is_sorted(r);
  post r => is_permutation(xs, r);
  decreases length(xs);
begin fn
  if length(xs) <= 1;
    return xs;
  end if;
  let mid = length(xs) / 2;
  let left = take(count: mid, from: xs);
  let right = drop(count: mid, from: xs);
  return merge(left: merge_sort(xs: left),
               right: merge_sort(xs: right));
end fn;
```


Compilation pipeline
--------------------

```
FX source -> FX AST -> FXCore (typed SSA) -> FXLow (virtual registers)
          -> FXAsm (target instructions) -> object file -> binary
```


Documentation
-------------

- [fx_design.md](fx_design.md) — language specification
- [fx_grammar.md](fx_grammar.md) — formal EBNF grammar
- [fx_lexer.md](fx_lexer.md) — tokenizer and transformer rules


Status
------

Active design.  The specification is complete.  Implementation is
bootstrapping from Lean 4, then self-hosting.


License
-------

Apache 2.0.  See [LICENSE](LICENSE).
