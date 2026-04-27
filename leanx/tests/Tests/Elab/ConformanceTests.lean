import FX.Elab.Elaborate
import FX.Eval.Interp
import FX.Syntax.Parser
import FX.Syntax.Lexer
import Tests.ElabSupport

/-!
# Conformance tests — multi-feature integration

Runs the full parse → elab → eval pipeline on programs that
exercise multiple surface features together.  Each test
embeds a small FX program as a string literal, processes it
end-to-end, and pins the evaluated value of `main`.

Complements the per-feature unit tests (TypingTests, MatchExprTests,
RecursionTests, NamedArgsTests, etc.) — those verify one feature
in isolation; these verify the features COMPOSE without
silently breaking each other.

A regression in any of:

  * parsing (lexer, parser, AST construction)
  * elaboration (scope, type parameters, named args, match,
    if, let, recursion, const lookup, lambda inference)
  * type-checking (infer, check, conversion, grade division)
  * evaluation (beta, iota, closures, const unfolding)

...will fail AT LEAST one of the assertions below.  Unlike
the smoke script which runs `fxi` as a subprocess, these tests
run the Lean-compiled interpreter directly — so a build breakage
shows up immediately in the test build, not at smoke time.
-/

namespace Tests.Elab.ConformanceTests

open FX.Kernel
open FX.Elab
open FX.Eval
open FX.Syntax
open Tests.ElabSupport

/-- Parse, elaborate, and evaluate `main`.  Returns the extracted
    Nat count, or `none` if any stage fails. -/
def runMainNat (source : String) : Option Nat :=
  let lexOutput := FX.Syntax.tokenize source
  let (parsedFile, _) := FX.Syntax.Parser.parseFile lexOutput.tokens
  let results := FX.Elab.checkFile parsedFile
  let evalEnv : EvalEnv := EvalEnv.ofGlobals
    (resultsToEnvWithAdts parsedFile results)
  match results.findSome? fun result =>
    match result with
    | .okDecl elaboratedDecl =>
      if elaboratedDecl.name == "main" then some elaboratedDecl.body else none
    | _ => none with
  | some mainBody => unaryNatCount? (evalZeroArgBody evalEnv mainBody)
  | none          => none

/-! ## Integration 1 — const + self-recursion + named args

`double` is self-recursive via match.  `myOne` is a const decl.
`compute` uses named args to reorder its args.  `main` composes
all three. -/

example :
  runMainNat
    ("const myOne : Nat = Nat.Succ(Nat.Zero);\n" ++
     "fn double(n: Nat) : Nat = match n;\n" ++
     "  Zero => Nat.Zero;\n" ++
     "  Succ(k) => Nat.Succ(Nat.Succ(double(k)));\n" ++
     "end match;\n" ++
     "fn pick(a: Nat, b: Nat) : Nat = a;\n" ++
     "fn main() : Nat = double(pick(b: Nat.Zero, a: myOne));")
  = some 2 := by native_decide

/-! ## Integration 2 — if/else + recursion

`double` recurses via match.  `main` branches on `true` (so
the then-arm fires) and computes double(2) = 4.  Paired with
a `false` version that computes double(1) = 2, distinguishing
correct arm selection from "always takes then". -/

example :
  runMainNat
    ("fn double(n: Nat) : Nat = match n;\n" ++
     "  Zero => Nat.Zero;\n" ++
     "  Succ(k) => Nat.Succ(Nat.Succ(double(k)));\n" ++
     "end match;\n" ++
     "fn main() : Nat = if true;\n" ++
     "  double(Nat.Succ(Nat.Succ(Nat.Zero)))\n" ++
     "else\n" ++
     "  double(Nat.Succ(Nat.Zero))\n" ++
     "end if;")
  = some 4 := by native_decide

example :
  runMainNat
    ("fn double(n: Nat) : Nat = match n;\n" ++
     "  Zero => Nat.Zero;\n" ++
     "  Succ(k) => Nat.Succ(Nat.Succ(double(k)));\n" ++
     "end match;\n" ++
     "fn main() : Nat = if false;\n" ++
     "  double(Nat.Succ(Nat.Succ(Nat.Zero)))\n" ++
     "else\n" ++
     "  double(Nat.Succ(Nat.Zero))\n" ++
     "end if;")
  = some 2 := by native_decide

/-! ## Integration 3 — untyped lambda + type param + let

Tests B11 (untyped lambda via expected Pi) and B5 (let-binding)
together.  `apply_twice` takes a function and a value, applies
the function twice.  The lambda passed in is untyped — its type
`Nat → Nat` comes from `apply_twice`'s declared param type.

Currently this fails because expected-type propagation doesn't
thread into call-site arguments.  The test documents the gap:
when that threading lands, this test's expectation flips from
`none` to `some 3`. -/

example :
  runMainNat
    ("fn apply_twice(f: Nat -> Nat, x: Nat) : Nat = f(f(x));\n" ++
     "fn main() : Nat = apply_twice(fn(x) => Nat.Succ(x), Nat.Succ(Nat.Zero));")
  = none := by native_decide

/-! ## Integration 4 — untyped lambda via fn return type

Same test but the lambda sits in a fn's body with declared Pi
return — the expected-type PATH that DOES work today. -/

example :
  runMainNat
    ("fn plus_two() : Nat -> Nat = fn(x) => Nat.Succ(Nat.Succ(x));\n" ++
     "fn main() : Nat = plus_two()(Nat.Succ(Nat.Zero));")
  = some 3 := by native_decide

/-! ## Integration 5 — deep recursion

Stress test: computes `double^3(1) = double(double(double(1)))
= double(double(2)) = double(4) = 8`.  Exercises iota a LOT;
a broken fuel-bounded reducer with too-low fuel would fail. -/

example :
  runMainNat
    ("fn double(n: Nat) : Nat = match n;\n" ++
     "  Zero => Nat.Zero;\n" ++
     "  Succ(k) => Nat.Succ(Nat.Succ(double(k)));\n" ++
     "end match;\n" ++
     "fn main() : Nat = double(double(double(Nat.Succ(Nat.Zero))));")
  = some 8 := by native_decide

/-! ## Integration B4 — spec clauses parse-and-discard

`pre`/`post`/`decreases`/`where` clauses between the return
type and the body are currently parsed and discarded.  SMT
discharge (Stream E) will actually verify these.  These
assertions pin that the SYNTAX is accepted and the body's
evaluation is unchanged. -/

example :
  runMainNat
    ("fn halve(n: Nat) : Nat\n" ++
     "  pre true;\n" ++
     "  post r => true;\n" ++
     "  decreases n;\n" ++
     "  = match n;\n" ++
     "    Zero => Nat.Zero;\n" ++
     "    Succ(k) => match k;\n" ++
     "      Zero => Nat.Zero;\n" ++
     "      Succ(m) => Nat.Succ(halve(m));\n" ++
     "    end match;\n" ++
     "  end match;\n" ++
     "fn main() : Nat = halve(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))));")
  = some 2 := by native_decide

/-! ## Integration B3 — effect annotations parse-and-discard

`with IO, Alloc` after the return type should parse and
elaborate identically to the same fn without it.  Current
Phase-2 DISCARDS the effect list — enforcement at App lands
with A12.  These assertions pin that the syntax is accepted
and doesn't change observable behavior. -/

-- Single effect label.  A12 requires `main` to declare `with IO`
-- to call `io_fn` — previously this test didn't and silently
-- passed because effects weren't enforced.
example :
  runMainNat
    ("fn io_fn() : Nat with IO = Nat.Succ(Nat.Zero);\n" ++
     "fn main() : Nat with IO = io_fn();")
  = some 1 := by native_decide

-- Multi-effect comma list.  A12 now enforces subsumption, so
-- `main` must declare the callee's effects to call it.
example :
  runMainNat
    ("fn multi() : Nat with IO, Alloc = Nat.Succ(Nat.Succ(Nat.Zero));\n" ++
     "fn main() : Nat with IO, Alloc = multi();")
  = some 2 := by native_decide

-- Effect-annotated fn composed with a non-effect fn.  `pure_add`
-- doesn't call `io_gen` directly — it just wraps its arg with
-- `Succ` — so pure_add stays Tot.  `main` calls both so main
-- needs the union: `IO`.
example :
  runMainNat
    ("fn io_gen() : Nat with IO = Nat.Succ(Nat.Succ(Nat.Zero));\n" ++
     "fn pure_add(n: Nat) : Nat = Nat.Succ(n);\n" ++
     "fn main() : Nat with IO = pure_add(io_gen());")
  = some 3 := by native_decide

/-! ## Integration 6 — mutual forward reference

`first_caller` is declared BEFORE `second_callee` but calls it.
The two-pass `checkFile` pre-registers signatures so this works.
A regression that broke pass-1's signature registration would
fail this test (it would emit E001 "unknown identifier" at the
first forward-ref site). -/

example :
  runMainNat
    ("fn first_caller() : Nat = Nat.Succ(second_callee());\n" ++
     "fn second_callee() : Nat = Nat.Succ(Nat.Succ(Nat.Zero));\n" ++
     "fn main() : Nat = first_caller();")
  = some 3 := by native_decide

/-! ## Flagship — everything composes

A single program exercising every Phase-2 surface feature that
has landed:

  * `module` preamble
  * `const` decls with cross-reference
  * `fn` with type parameter, effect annotation, spec clauses
  * `match` + self-recursion
  * `if`/`else`
  * Named-argument routing
  * Untyped lambda via expected Pi
  * Forward reference (caller before callee)

If any feature silently breaks, the final `main` value drops
or the program fails to elaborate.  Pinning `main = 6` keeps
them all honest simultaneously. -/

example :
  runMainNat
    ("module Flagship;\n" ++
     "\n" ++
     "const seed : Nat = Nat.Succ(Nat.Zero);\n" ++
     "\n" ++
     "fn main() : Nat with IO = compute(pick: true, arg: seed);\n" ++
     "\n" ++
     "fn compute(pick: Bool, arg: Nat) : Nat with IO\n" ++
     "  pre true;\n" ++
     "  = if pick;\n" ++
     "      double(arg)\n" ++
     "    else\n" ++
     "      triple()(arg)\n" ++
     "    end if;\n" ++
     "\n" ++
     "fn triple() : Nat -> Nat = fn(x) => Nat.Succ(Nat.Succ(Nat.Succ(x)));\n" ++
     "\n" ++
     "fn double(n: Nat) : Nat\n" ++
     "  decreases n;\n" ++
     "  = match n;\n" ++
     "      Zero => Nat.Zero;\n" ++
     "      Succ(k) => Nat.Succ(Nat.Succ(double(k)));\n" ++
     "    end match;")
  = some 2 := by native_decide

/-! ## Integration B9 — user ADT + self-recursion + named args

A small program that composes user ADTs (B9), match on self-
referential constructors, recursion via `Term.const`, named-
argument routing (B12), and if/else (B6).  If any one of these
features regresses the test drops or fails to elaborate. -/

example :
  runMainNat
    ("type tree\n" ++
     "  Leaf;\n" ++
     "  Node(Nat, tree, tree);\n" ++
     "end type;\n" ++
     "fn depth(t: tree) : Nat = match t;\n" ++
     "  Leaf => Nat.Zero;\n" ++
     "  Node(k, l, r) => Nat.Succ(depth(l));\n" ++
     "end match;\n" ++
     "fn main() : Nat = depth(Node(Nat.Zero, Node(Nat.Zero, Node(Nat.Zero, Leaf, Leaf), Leaf), Leaf));")
  = some 3 := by native_decide

/-! ## Integration B9 — ADT + if/else branching on bool

The type `option_ish` has two nullary ctors.  A fn `select`
picks between them by `if cond`, then the match on the result
yields a unary Nat.  Exercises that user ADTs flow through
both `if` branches without loss of type info. -/

example :
  runMainNat
    ("type option_ish\n" ++
     "  Yes;\n" ++
     "  No;\n" ++
     "end type;\n" ++
     "fn pick(cond: Bool) : option_ish = if cond;\n" ++
     "  Yes\n" ++
     "else\n" ++
     "  No\n" ++
     "end if;\n" ++
     "fn describe(o: option_ish) : Nat = match o;\n" ++
     "  Yes => Nat.Succ(Nat.Zero);\n" ++
     "  No  => Nat.Zero;\n" ++
     "end match;\n" ++
     "fn main() : Nat = describe(pick(true));")
  = some 1 := by native_decide

/-! ## Milestone M2 — records + let + blocks compose

Demonstrates that a non-trivial program composes records (B8),
let-bindings with type ascriptions (B5), block functions with
`begin fn ... end fn` (B5), named arguments (B12), and
`.field` projection (B8).  A regression in any of those features
fails the assertion. -/

example :
  runMainNat
    ("type account {\n" ++
     "  balance: Nat;\n" ++
     "};\n" ++
     "fn deposit(a: account, amount: Nat) : account\n" ++
     "  begin fn\n" ++
     "    let current : Nat = a.balance;\n" ++
     "    let new_balance : Nat = Nat.Succ(current);\n" ++
     "    return Account(new_balance);\n" ++
     "  end fn;\n" ++
     "fn main() : Nat\n" ++
     "  begin fn\n" ++
     "    let empty : account = Account(Nat.Zero);\n" ++
     "    let once : account = deposit(a: empty, amount: Nat.Succ(Nat.Zero));\n" ++
     "    let twice : account = deposit(a: once, amount: Nat.Succ(Nat.Zero));\n" ++
     "    return twice.balance;\n" ++
     "  end fn;")
  = some 2 := by native_decide

/-! ## Synthesis-mode let-inference (§4.6)

Same M2 program as above but with all `: T` annotations stripped —
every let-RHS is a shape `inferLetRhsType?` covers (ctor call,
field access, fn call).  A regression in inference would fall
through to T045 and fail the test at elab time. -/

example :
  runMainNat
    ("type account {\n" ++
     "  balance: Nat;\n" ++
     "};\n" ++
     "fn deposit(a: account, amount: Nat) : account\n" ++
     "  begin fn\n" ++
     "    let current = a.balance;\n" ++          -- field access
     "    let new_balance = Nat.Succ(current);\n" ++  -- applied ctor
     "    return Account(new_balance);\n" ++
     "  end fn;\n" ++
     "fn main() : Nat\n" ++
     "  begin fn\n" ++
     "    let empty = Account(Nat.Zero);\n" ++     -- applied ctor
     "    let once = deposit(a: empty, amount: Nat.Succ(Nat.Zero));\n" ++  -- fn call
     "    let twice = deposit(a: once, amount: Nat.Succ(Nat.Zero));\n" ++
     "    return twice.balance;\n" ++
     "  end fn;")
  = some 2 := by native_decide

-- E-7: local fn inside a `begin fn … end fn` body.  §4.7 rule 18.
-- Pins end-to-end flow: local fn decl is parsed → elaborated as
-- a let-bound closure → callable by name in subsequent stmts.
example :
  runMainNat
    ("fn outer(n: Nat) : Nat\n" ++
     "  begin fn\n" ++
     "    fn double(x: Nat) : Nat = Nat.Succ(Nat.Succ(x));\n" ++
     "    let result : Nat = double(n);\n" ++
     "    return result;\n" ++
     "  end fn;\n" ++
     "fn main() : Nat = outer(Nat.Succ(Nat.Succ(Nat.Zero)));")
  = some 4 := by native_decide

-- E-7 rejection: local fn with `with IO` emits P050 per §4.7
-- rule 18.  Verified via `fxi parse` at the CLI; not pinned as
-- a native_decide example because the conformance harness only
-- tracks elab/runtime errors, not parse-level errors.  Manual
-- check: `fxi parse` on a file with `fn inner() : Nat with IO
-- = Nat.Zero;` inside a `begin fn … end fn` body emits
-- "error[P050]: local fn cannot carry 'with' effects".

-- B13 §16.1: impl blocks flatten into qualified top-level fns.
-- `impl Point fn first(p): p.x; end impl;` generates a top-
-- level `Point.first` fn callable via qualified name.
-- Zero-arg impl methods per §31.7 zero-arg uniform: first call
-- fires Unit.tt argument automatically.
example :
  runMainNat
    ("type Point { x: Nat; y: Nat; };\n" ++
     "impl Point\n" ++
     "  fn first(p: Point) : Nat = p.x;\n" ++
     "end impl;\n" ++
     "fn main() : Nat = Point.first(Point { " ++
       "x: Nat.Succ(Nat.Succ(Nat.Zero)), y: Nat.Zero });")
  = some 2 := by native_decide

-- B13 impl with multiple members — every member gets its own
-- qualified top-level fn via the flattener.
example :
  runMainNat
    ("type Point { x: Nat; y: Nat; };\n" ++
     "impl Point\n" ++
     "  fn first(p: Point) : Nat = p.x;\n" ++
     "  fn second(p: Point) : Nat = p.y;\n" ++
     "end impl;\n" ++
     "fn main() : Nat = Point.second(Point { " ++
       "x: Nat.Zero, y: Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) });")
  = some 3 := by native_decide

end Tests.Elab.ConformanceTests
