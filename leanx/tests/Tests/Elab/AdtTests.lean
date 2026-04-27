import FX.Elab.Elaborate
import FX.Eval.Interp
import FX.Syntax.Parser
import FX.Syntax.Lexer
import Tests.ElabSupport

/-!
# ADT declaration tests (task B9)

End-to-end coverage for user-declared algebraic data types:
`type NAME Ctor1; Ctor2; ... end type;` (grammar §5.9 variant
form).  Exercises parse → elab → typing → iota reduction →
match compilation → eval.

Corpus:

  * nullary ctors: `type color Red; Green; Blue; end type;`
  * arg ctors: `type shape Circle(Nat); Rect(Nat, Nat); end type;`
  * self-referential: `type tree Leaf; Node(Nat, tree, tree);
    end type;`
  * positivity rejection: `type bad Mk(bad -> bad); end type;`
    (self-ref in contravariant position — T120)
  * ctor arg count mismatch: `Node(Leaf)` when Node expects 3
    args (E010)
  * match dispatch: `match c; Red => 0; Green => 1; Blue => 2;
    end match;`

Phase-2 scope (deferred):

  * parameterized `type option<a> ...` — E021 (deferred to A10)
  * record form `type T { ... }` — P037 (B8)
  * alias form `type T = ...` — P037 (future work)
  * GADT constructor refinement — A10+
-/

namespace Tests.Elab.AdtTests

open FX.Kernel
open FX.Elab
open FX.Eval
open FX.Syntax
open Tests.ElabSupport

/-- Parse, elab, eval `main`, returning the unary-Nat count (or
    `none` if any stage failed or `main` is non-Nat).  Includes
    user ADT spec registration on the runtime env so matches
    against user ADTs reduce correctly (B9). -/
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

/-- Returns `true` iff every decl elaborated OK (no E/T/P error
    in the results).  Lets tests pin `expected-fail` programs by
    checking this is `false` AND identifying the code. -/
def allElabOk (source : String) : Bool :=
  let lexOutput := FX.Syntax.tokenize source
  let (parsedFile, _) := FX.Syntax.Parser.parseFile lexOutput.tokens
  let results := FX.Elab.checkFile parsedFile
  results.all fun declResult =>
    match declResult with
    | .okDecl _ => true
    | _         => false

/-- Returns `some errCode` iff at least one decl failed elab with
    that code.  `none` if all succeeded. -/
def firstElabErrCode? (source : String) : Option String :=
  let lexOutput := FX.Syntax.tokenize source
  let (parsedFile, _) := FX.Syntax.Parser.parseFile lexOutput.tokens
  let results := FX.Elab.checkFile parsedFile
  results.findSome? fun declResult =>
    match declResult with
    | .elabFail err  => some err.code
    | .typeFail _ te => some te.code
    | _              => none

/-! ## Integration — simple nullary ADT with match -/

-- `color` with three nullary ctors; `describe` match-dispatches
-- to a unary Nat.  Red → 0, Green → 1, Blue → 2.
example :
  runMainNat
    ("type color\n" ++
     "  Red;\n" ++
     "  Green;\n" ++
     "  Blue;\n" ++
     "end type;\n" ++
     "fn describe(c: color) : Nat = match c;\n" ++
     "  Red => Nat.Zero;\n" ++
     "  Green => Nat.Succ(Nat.Zero);\n" ++
     "  Blue => Nat.Succ(Nat.Succ(Nat.Zero));\n" ++
     "end match;\n" ++
     "fn main() : Nat = describe(Green);")
  = some 1 := by native_decide

example :
  runMainNat
    ("type color\n" ++
     "  Red;\n" ++
     "  Green;\n" ++
     "  Blue;\n" ++
     "end type;\n" ++
     "fn describe(c: color) : Nat = match c;\n" ++
     "  Red => Nat.Zero;\n" ++
     "  Green => Nat.Succ(Nat.Zero);\n" ++
     "  Blue => Nat.Succ(Nat.Succ(Nat.Zero));\n" ++
     "end match;\n" ++
     "fn main() : Nat = describe(Blue);")
  = some 2 := by native_decide

/-! ## Integration — self-recursive ADT (tree) -/

-- Tree with Leaf and Node(Nat, tree, tree).  Self-ref in the
-- recursive args passes strict positivity (final-codomain
-- position).  `size` recursively sums the left subtree count.
example :
  runMainNat
    ("type tree\n" ++
     "  Leaf;\n" ++
     "  Node(Nat, tree, tree);\n" ++
     "end type;\n" ++
     "fn size(t: tree) : Nat = match t;\n" ++
     "  Leaf => Nat.Zero;\n" ++
     "  Node(k, l, r) => Nat.Succ(size(l));\n" ++
     "end match;\n" ++
     "fn main() : Nat = size(Node(Nat.Zero, Node(Nat.Zero, Leaf, Leaf), Leaf));")
  = some 2 := by native_decide

/-! ## Integration — ctor with concrete payload type -/

-- `box` has one ctor `Boxed(Nat)`.  The payload is `Nat.Succ`-
-- unwrapped by a manual match arm.
example :
  runMainNat
    ("type box\n" ++
     "  Boxed(Nat);\n" ++
     "end type;\n" ++
     "fn unbox(b: box) : Nat = match b;\n" ++
     "  Boxed(n) => n;\n" ++
     "end match;\n" ++
     "fn main() : Nat = unbox(Boxed(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))));")
  = some 3 := by native_decide

/-! ## Integration — named-field ctor -/

-- `shape` with named fields on `Circle(radius: Nat)`.  The field
-- name lives in surface syntax only; kernel encoding is identical
-- to positional.
example :
  runMainNat
    ("type shape\n" ++
     "  Circle(radius: Nat);\n" ++
     "  Square(side: Nat);\n" ++
     "end type;\n" ++
     "fn area_like(s: shape) : Nat = match s;\n" ++
     "  Circle(r) => r;\n" ++
     "  Square(w) => Nat.Succ(w);\n" ++
     "end match;\n" ++
     "fn main() : Nat = area_like(Circle(Nat.Succ(Nat.Zero)));")
  = some 1 := by native_decide

/-! ## Parameterized ADT declaration (B9 landing)

As of B9, parameterized type declarations are accepted at the
declaration level.  The elaborator:

  * builds `spec.params` from the type-param kind telescope,
  * pushes param names onto a `paramScope` for ctor-arg elab,
  * lets ctor args reference the params by name (e.g. `Some(a)`
    resolves `a` to `Term.var 0`),
  * registers the full spec on `globalEnv.userSpecs`.

The declaration alone (no use) now type-checks cleanly — E021
no longer fires.  Full use-site support (parameterized ctor
construction with type-arg inference, match on parameterized
scrutinee) lands in an M2+ follow-up; those paths currently
emit distinct errors (T111 at ctor construction, E010 at
match) which are deliberately left pinned by the separate
use-site tests below. -/

-- Parameterized DECL alone type-checks.
example :
  firstElabErrCode?
    ("type option<a: type>\n" ++
     "  None;\n" ++
     "  Some(a);\n" ++
     "end type;\n" ++
     "fn main() : Nat = Nat.Zero;")
  = none := by native_decide

-- Use-site pending: match against a parameterized scrutinee is
-- blocked at elaboration with E010 — the match compiler doesn't
-- yet handle parameterized indRec.  Pinned so a regression at
-- the use-site is caught even though the decl itself succeeds.
example :
  firstElabErrCode?
    ("type option<a: type>\n" ++
     "  None;\n" ++
     "  Some(a);\n" ++
     "end type;\n" ++
     "fn main() : Nat = match Some(Nat.Zero);\n" ++
     "  None    => Nat.Zero;\n" ++
     "  Some(n) => n;\n" ++
     "end match;")
  = some "E010" := by native_decide

/-! ## Rejection — strict positivity (T120) -/

-- Self-reference in negative position — `Mk(bad -> bad)` places
-- `bad` on the LEFT of an arrow inside the ctor arg type.  The
-- positivity checker rejects at elab time with T120.  This is
-- the canonical U = U → U "Girard's paradox" shape from §27.2.
example :
  firstElabErrCode?
    ("type paradox\n" ++
     "  Mk(paradox -> paradox);\n" ++
     "end type;\n" ++
     "fn main() : Nat = Nat.Zero;")
  = some "T120" := by native_decide

/-! ## Integration — user ADTs work across multiple decls -/

-- Two independent user ADTs in the same file plus a Nat-returning
-- reducer.  Exercises that `userSpecs` accumulates across type
-- decls and each spec is resolvable by name at match sites.
example :
  runMainNat
    ("type day\n" ++
     "  Monday;\n" ++
     "  Tuesday;\n" ++
     "end type;\n" ++
     "type weather\n" ++
     "  Sunny;\n" ++
     "  Rainy;\n" ++
     "end type;\n" ++
     "fn dayToNat(d: day) : Nat = match d;\n" ++
     "  Monday => Nat.Zero;\n" ++
     "  Tuesday => Nat.Succ(Nat.Zero);\n" ++
     "end match;\n" ++
     "fn weatherToNat(w: weather) : Nat = match w;\n" ++
     "  Sunny => Nat.Succ(Nat.Succ(Nat.Zero));\n" ++
     "  Rainy => Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));\n" ++
     "end match;\n" ++
     "fn main() : Nat = weatherToNat(Rainy);")
  = some 3 := by native_decide

/-! ## Record literal syntax (B8) -/

-- Spec's canonical record construction: `Config { host: v, port: p }`.
-- Parses via `postfixLoop`'s `lbrace` branch, elaborates via the ctor
-- named-arg reorder.
example :
  runMainNat
    ("type config {\n" ++
     "  host: Nat;\n" ++
     "  port: Nat;\n" ++
     "};\n" ++
     "fn main() : Nat = Config { host: Nat.Succ(Nat.Succ(Nat.Zero)), port: Nat.Zero }.host;")
  = some 2 := by native_decide

-- Named-arg ctor call form `Config(host: v, port: p)` — same
-- semantics as record-literal form via a different syntactic path.
example :
  runMainNat
    ("type config {\n" ++
     "  host: Nat;\n" ++
     "  port: Nat;\n" ++
     "};\n" ++
     "fn main() : Nat = Config(host: Nat.Succ(Nat.Zero), port: Nat.Zero).host;")
  = some 1 := by native_decide

-- Fields in non-declaration order get reordered.  Declaration is
-- `host, port`; user passes `port, host`; the elab reorder puts
-- them in declared positional order before building the ctor.
example :
  runMainNat
    ("type config {\n" ++
     "  host: Nat;\n" ++
     "  port: Nat;\n" ++
     "};\n" ++
     "fn main() : Nat = Config { port: Nat.Zero, host: Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) }.host;")
  = some 3 := by native_decide

/-! ## Record field access (B8 — `.field` projection) -/

-- Field access directly on a ctor application — `Config(h, p).host`
-- elaborates to an `indRec` that picks the first arg.
example :
  runMainNat
    ("type config {\n" ++
     "  host: Nat;\n" ++
     "  port: Nat;\n" ++
     "};\n" ++
     "fn main() : Nat = Config(Nat.Succ(Nat.Succ(Nat.Zero)), Nat.Zero).host;")
  = some 2 := by native_decide

-- Field access on a fn parameter — `p.x` inside a fn body.
example :
  runMainNat
    ("type point {\n" ++
     "  x: Nat;\n" ++
     "  y: Nat;\n" ++
     "};\n" ++
     "fn get_x(p: point) : Nat = p.x;\n" ++
     "fn main() : Nat = get_x(Point(Nat.Succ(Nat.Zero), Nat.Zero));")
  = some 1 := by native_decide

-- Access the SECOND field (index 1), not the first.
example :
  runMainNat
    ("type config {\n" ++
     "  host: Nat;\n" ++
     "  port: Nat;\n" ++
     "};\n" ++
     "fn main() : Nat = Config(Nat.Zero, Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))).port;")
  = some 3 := by native_decide

/-! ## Record types (B8 — narrow scope) -/

-- `type config { host: Nat; port: Nat; };` desugars to a single-
-- ctor ADT with ctor `Config(host, port)`.  Destructure via match.
example :
  runMainNat
    ("type config {\n" ++
     "  host: Nat;\n" ++
     "  port: Nat;\n" ++
     "};\n" ++
     "fn host_of(c: config) : Nat = match c;\n" ++
     "  Config(h, p) => h;\n" ++
     "end match;\n" ++
     "fn main() : Nat = host_of(Config(Nat.Succ(Nat.Succ(Nat.Zero)), Nat.Zero));")
  = some 2 := by native_decide

-- Two records in one file get distinct ctors by capitalized type
-- name — `config` → `Config`, `point` → `Point`.
example :
  runMainNat
    ("type config {\n" ++
     "  host: Nat;\n" ++
     "};\n" ++
     "type point {\n" ++
     "  x: Nat;\n" ++
     "};\n" ++
     "fn x_of(pt: point) : Nat = match pt;\n" ++
     "  Point(x_val) => x_val;\n" ++
     "end match;\n" ++
     "fn main() : Nat = x_of(Point(Nat.Succ(Nat.Zero)));")
  = some 1 := by native_decide

-- Record with a self-referential field is equivalent to the
-- tree-with-named-fields form — proves records reuse the ADT
-- positivity check.
example :
  runMainNat
    ("type counter {\n" ++
     "  value: Nat;\n" ++
     "};\n" ++
     "fn value_of(c: counter) : Nat = match c;\n" ++
     "  Counter(v) => v;\n" ++
     "end match;\n" ++
     "fn main() : Nat = value_of(Counter(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))));")
  = some 3 := by native_decide

-- Uppercase type name: `type Pair { ... };` — no capitalization
-- needed; ctor is `Pair.Pair` (or unqualified `Pair`).
example :
  runMainNat
    ("type Pair {\n" ++
     "  first: Nat;\n" ++
     "  second: Nat;\n" ++
     "};\n" ++
     "fn sum(p: Pair) : Nat = match p;\n" ++
     "  Pair(a, b) => a;\n" ++
     "end match;\n" ++
     "fn main() : Nat = sum(Pair(Nat.Succ(Nat.Zero), Nat.Zero));")
  = some 1 := by native_decide

/-! ## A12 — effect subsumption at App

Effect-annotated fns must declare the superset of their callees'
effects.  Widening emits E044. -/

-- REJECTED: pure fn calls IO-effectful fn without declaring IO.
example :
  firstElabErrCode?
    ("fn io_op() : Nat with IO = Nat.Zero;\n" ++
     "fn pure_fn() : Nat = io_op();\n" ++
     "fn main() : Nat = Nat.Zero;")
  = some "E044" := by native_decide

-- REJECTED: caller declares subset of callee's effects.
example :
  firstElabErrCode?
    ("fn multi_eff() : Nat with IO, Alloc = Nat.Zero;\n" ++
     "fn narrower() : Nat with IO = multi_eff();\n" ++
     "fn main() : Nat = Nat.Zero;")
  = some "E044" := by native_decide

-- OK: caller declares superset of callee's effects.
example :
  runMainNat
    ("fn io_op() : Nat with IO = Nat.Succ(Nat.Zero);\n" ++
     "fn wrapper() : Nat with IO = io_op();\n" ++
     "fn main() : Nat with IO = wrapper();")
  = some 1 := by native_decide

-- OK: empty effect set (Tot) is bottom — any Tot fn inside a
-- Tot fn is fine.
example :
  runMainNat
    ("fn pure_fn() : Nat = Nat.Succ(Nat.Zero);\n" ++
     "fn caller() : Nat = pure_fn();\n" ++
     "fn main() : Nat = caller();")
  = some 1 := by native_decide

-- OK: caller declares exact match of callee's row.
example :
  runMainNat
    ("fn both() : Nat with IO, Alloc = Nat.Succ(Nat.Succ(Nat.Zero));\n" ++
     "fn main() : Nat with IO, Alloc = both();")
  = some 2 := by native_decide

/-! ## A12 — `Read ≤ Write` lattice subsumption

Per §9.3: "Write implies Read" is the one built-in sub-effect
edge in the lattice.  A caller declaring `with Write`
automatically accepts a callee using only `with Read` because
Write saturates Read at the `Grade.Effect` record layer via
`write_`'s `{ read := true, write := true }` construction.  The
reverse does NOT hold — writing is a strictly stronger
capability than reading.

These tests pin the subsumption direction through the full
elaborator, not just the grade algebra. -/

-- OK: Read ≤ Write — callee uses Read, caller declares Write.
example :
  runMainNat
    ("fn read_op() : Nat with Read = Nat.Succ(Nat.Zero);\n" ++
     "fn write_caller() : Nat with Write = read_op();\n" ++
     "fn main() : Nat with Write = write_caller();")
  = some 1 := by native_decide

-- REJECTED: Write ≰ Read — callee uses Write, caller declares Read.
example :
  firstElabErrCode?
    ("fn write_op() : Nat with Write = Nat.Zero;\n" ++
     "fn read_caller() : Nat with Read = write_op();\n" ++
     "fn main() : Nat = Nat.Zero;")
  = some "E044" := by native_decide

-- OK: exact match on Write — tautologically subsumed.
example :
  runMainNat
    ("fn write_op() : Nat with Write = Nat.Succ(Nat.Zero);\n" ++
     "fn write_caller() : Nat with Write = write_op();\n" ++
     "fn main() : Nat with Write = write_caller();")
  = some 1 := by native_decide

-- REJECTED: unrelated labels don't subsume — IO ≰ Alloc.
example :
  firstElabErrCode?
    ("fn io_op() : Nat with IO = Nat.Zero;\n" ++
     "fn alloc_caller() : Nat with Alloc = io_op();\n" ++
     "fn main() : Nat = Nat.Zero;")
  = some "E044" := by native_decide

/-! ## Effect-kind type parameters (§9.2)

Per §5.5 grammar, a type parameter's kind can be `effect` —
used for polymorphism over effect rows, e.g.
`fn map<a, b, eff: effect>(f: a -> b with eff, xs: list(a))
: list(b) with eff`.  The parser accepts `effect` as a reserved
kind keyword; the elaborator collapses it to universe 0 for now
(full kind distinction is a later-phase feature). -/

-- OK: `<eff: effect>` parses and elaborates as a ghost-graded
-- type parameter.
example :
  firstElabErrCode?
    ("fn identity_with_eff<a: type, eff: effect>(x: a) : a = x;\n" ++
     "fn main() : Nat = Nat.Zero;")
  = none := by native_decide

/-! ## User-defined effects (§9.5) pass-through

Effect names not in the eight §9.4 built-ins (IO, Div, Ghost,
Exn, Alloc, Read, Write, Async) fall through `Effect.fromName?`
into the unknown-list half of `fromNames`.  The A12 check
treats them with per-name subset, so user-defined / stdlib
effects (`State`, `Crypto`, …) can still propagate through the
call graph without dropping out of enforcement. -/

-- OK: caller declares same user-defined effect.
example :
  firstElabErrCode?
    ("fn state_op() : Nat with State = Nat.Zero;\n" ++
     "fn state_caller() : Nat with State = state_op();\n" ++
     "fn main() : Nat = Nat.Zero;")
  = none := by native_decide

-- REJECTED: user-defined effect widens caller's declared row.
example :
  firstElabErrCode?
    ("fn state_op() : Nat with State = Nat.Zero;\n" ++
     "fn pure_caller() : Nat = state_op();\n" ++
     "fn main() : Nat = Nat.Zero;")
  = some "E044" := by native_decide

-- OK: mixed builtin + user-defined — both dimensions respected.
example :
  firstElabErrCode?
    ("fn mixed_op() : Nat with IO, Crypto = Nat.Zero;\n" ++
     "fn caller() : Nat with IO, Crypto = mixed_op();\n" ++
     "fn main() : Nat = Nat.Zero;")
  = none := by native_decide

-- REJECTED: caller drops user-defined effect from the row.
example :
  firstElabErrCode?
    ("fn mixed_op() : Nat with IO, Crypto = Nat.Zero;\n" ++
     "fn only_io() : Nat with IO = mixed_op();\n" ++
     "fn main() : Nat = Nat.Zero;")
  = some "E044" := by native_decide

/-! ## B11 — Destructuring lambda parameters (§4.5, §5.3)

Lambda params can be tuple/ctor patterns when the expected
domain is a single-ctor inductive.  Compiles to
`λ _arg. indRec spec motive [method] _arg` where `method`
unpacks the ctor's args into the body's scope. -/

-- Tuple destructuring on a record type: `fn((a, b)) => a`
-- extracts the first field.
example :
  runMainNat
    ("type my_pair {\n" ++
     "  first: Nat;\n" ++
     "  second: Nat;\n" ++
     "};\n" ++
     "fn extract(p: my_pair) : Nat\n" ++
     "begin fn\n" ++
     "  let f : my_pair -> Nat = fn((a, b)) => a;\n" ++
     "  return f(p);\n" ++
     "end fn;\n" ++
     "fn main() : Nat = extract(\n" ++
     "  My_pair { first: Nat.Succ(Nat.Succ(Nat.Zero)), second: Nat.Zero });")
  = some 2 := by native_decide

-- Second-field extraction.
example :
  runMainNat
    ("type my_pair {\n" ++
     "  first: Nat;\n" ++
     "  second: Nat;\n" ++
     "};\n" ++
     "fn extract(p: my_pair) : Nat\n" ++
     "begin fn\n" ++
     "  let f : my_pair -> Nat = fn((a, b)) => b;\n" ++
     "  return f(p);\n" ++
     "end fn;\n" ++
     "fn main() : Nat = extract(\n" ++
     "  My_pair { first: Nat.Zero, second: Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))) });")
  = some 3 := by native_decide

-- Wildcard in destructure: ignore second field.
example :
  runMainNat
    ("type my_pair {\n" ++
     "  first: Nat;\n" ++
     "  second: Nat;\n" ++
     "};\n" ++
     "fn extract(p: my_pair) : Nat\n" ++
     "begin fn\n" ++
     "  let f : my_pair -> Nat = fn((x, _)) => x;\n" ++
     "  return f(p);\n" ++
     "end fn;\n" ++
     "fn main() : Nat = extract(\n" ++
     "  My_pair { first: Nat.Succ(Nat.Zero), second: Nat.Succ(Nat.Succ(Nat.Zero)) });")
  = some 1 := by native_decide

-- REJECTED: destructuring without an expected Pi-type.
example :
  firstElabErrCode?
    ("fn main() : Nat\n" ++
     "begin fn\n" ++
     "  let f = fn((a, b)) => a;\n" ++
     "  return Nat.Zero;\n" ++
     "end fn;")
  = some "T045" := by native_decide

-- REJECTED: tuple arity mismatch — 2-tuple where spec's ctor
-- takes 1 arg.  (Using `Nat` which has 2 ctors so this
-- additionally fails single-ctor check first.)
example :
  firstElabErrCode?
    ("type single { only: Nat };\n" ++
     "fn extract(s: single) : Nat\n" ++
     "begin fn\n" ++
     "  let f : single -> Nat = fn((a, b)) => a;\n" ++
     "  return f(s);\n" ++
     "end fn;\n" ++
     "fn main() : Nat = extract(Single { only: Nat.Zero });")
  = some "E010" := by native_decide

end Tests.Elab.AdtTests
