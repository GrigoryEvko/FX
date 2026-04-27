import FX.Kernel.Grade.Effect
import FX.Kernel.Term

/-!
# Derived spec — Effect encoding (§9, D6)

Effects are a Tier-S grade dimension (§6.3 dim 4) — not a
separate monad machinery.  A function's effect row lives in its
kernel Pi's `returnEffect` field; effect composition at App is
set-union via `Effect.add`; subsumption is `Effect.LessEq`
(§9.3 bounded join-semilattice).  This module documents the
encoding and pins the shape via `example` blocks.  UNTRUSTED
(L3 per SPEC.md §5); the load-bearing work is in
`FX/Kernel/Grade/Effect.lean` (algebra), `FX/Kernel/Term.pi`
(returnEffect field), and `FX/Elab/EffectInference.lean`
(term-level effect inference per Appendix B).

## Surface syntax (§9.1)

```
fn add(a: i64, b: i64) : i64 = a + b;          -- Tot (no annotation)
fn read(path: string) : string with IO;         -- IO
fn send(m: packet) : unit with IO, Async;      -- row of two
fn loop() : never with Div;                    -- may diverge
```

## Kernel encoding

A function type `(a: A) -> T with eff_row` elaborates to:

```
Term.pi grade A T eff_row
```

`eff_row : Effect` is the kernel record with 8 Bool fields
mirroring §9.4's built-in labels:

```
structure Effect where
  io        : Bool := false
  div       : Bool := false
  ghost     : Bool := false
  exn       : Bool := false
  alloc     : Bool := false
  read      : Bool := false
  write     : Bool := false
  async     : Bool := false
```

Multi-label rows multiply the trues.  `Tot` (pure) is the all-
false `{}` record.

## Built-in labels → singleton encoding

`Effect.fromName?` maps each §9.4 surface keyword to its
singleton record.  The elaborator's `effectsFromSurface` folds
a `with IO, Alloc, ...` parse list through `fromNames`:

  * `IO`    → `{ io := true }`
  * `Div`   → `{ div := true }`
  * `Ghost` → `{ ghost := true }`
  * `Exn`   → `{ exn := true }`
  * `Alloc` → `{ alloc := true }`
  * `Read`  → `{ read := true }`
  * `Write` → `{ read := true, write := true }` ← §9.3
    `Read ≤ Write` pre-saturates: writing implies reading, so
    the `write_` singleton already carries `read := true`.
    This is the spec's one non-trivial subeffect edge — every
    other pairing of built-ins is independent.
  * `Async` → `{ async := true }`

Unknown surface names (user-defined effects per §9.5) return
`none` from `fromName?` and flow to a residual `List String`
that the elaborator handles separately via per-name subset
checks.

## Composition — `Effect.add`

At each App site, the effects of the function, arguments, and
the Pi's return-effect compose via `Effect.add` (bitwise OR
on the 8 Bool fields).  The algebra is:

  * commutative — `add a b = add b a`
  * associative — `add (add a b) c = add a (add b c)`
  * idempotent — `add a a = a`
  * `Tot` is the unit — `add Tot e = e`

A bounded join-semilattice with `Tot` as the bottom.

## Subsumption — `Effect.LessEq`

`e1 ≤ e2` iff every Bool in `e1` is `≤` the corresponding Bool
in `e2`.  Equivalently: `e1 ⊆ e2` as sets.  The A12 effect-row
check at fn-call sites verifies the callee's declared effects
are `≤` the caller's declared effects (callee can't perform
more effects than the caller advertises).

## Runtime erasure (§1.5)

Effects are erased at codegen.  An IO-performing fn compiles
to a regular call; the `IO` bit is gone from the binary.  What
survives: effect service modules linked conditionally per the
program's declared effect closure (§21.4 — a program with no
`Async` has no scheduler code).

## Spec-to-kernel crosswalk (Appendix B)

Appendix B's E-Pure, E-Sub, E-Seq, E-App, E-Handle rules are
the inference rules `FX/Elab/EffectInference.lean` implements:

  * **E-Pure**: `Γ ⊢ e : T [Tot]` — every closed expression
    inhabits the empty effect row by default.
  * **E-Sub**: `Γ ⊢ e : T [e1]` and `e1 ≤ e2` → `Γ ⊢ e : T
    [e2]`.  Wider callers subsume narrower callees.
  * **E-Seq**: sequencing `e1; e2 : T2 [e1 ∨ e2]` — join.
  * **E-App**: `f : T1 →{ef} T2` applied to `x : T1 [e2]`,
    under caller effects `e1` produces `T2 [e1 ∨ e2 ∨ ef]`.
  * **E-Handle**: `handle body with E` strips `E` from the
    body's effect row per §9.6 — deferred to E-5.

Phase-2 inference implements the first four; `handle`
(control-flow splitting for user-declared effects) lands with
E-3 (control-flow vs enabling split) and E-5 (handlers).
-/

namespace FX.Derived.Effect

open FX.Kernel

/-! ## Built-in label encoding — pin every mapping -/

/-- `Tot` = empty record = `Effect.tot`.  The identity of
    `Effect.add` and the bottom of the subeffect lattice. -/
example : Effect.tot = ({} : Effect) := rfl

-- Every built-in label produces exactly its named singleton.
example : Effect.fromName? "IO"    = some Effect.io_    := rfl
example : Effect.fromName? "Div"   = some Effect.div_   := rfl
example : Effect.fromName? "Ghost" = some Effect.ghost_ := rfl
example : Effect.fromName? "Exn"   = some Effect.exn_   := rfl
example : Effect.fromName? "Alloc" = some Effect.alloc_ := rfl
example : Effect.fromName? "Read"  = some Effect.read_  := rfl
example : Effect.fromName? "Write" = some Effect.write_ := rfl
example : Effect.fromName? "Async" = some Effect.async_ := rfl

-- Unknown names return `none`.  A fresh user-declared effect
-- name (§9.5) flows to the residual.
example : Effect.fromName? "MyCustom" = none := rfl
example : Effect.fromName? ""          = none := rfl

/-- `Write` pre-saturates `Read` per §9.3 — writing implies
    reading.  This is the only non-trivial built-in subeffect
    edge; every other label is independent.  A regression that
    dropped the pre-saturation would break callers that
    declared `Write` and relied on the auto-Read inclusion. -/
example : Effect.write_.read = true := rfl
example : Effect.write_.write = true := rfl

/-! ## Surface-row parsing — `fromNames` -/

/-- Empty name list → `Tot` + empty residual.  Matches a fn
    with no `with` clause. -/
example : Effect.fromNames [] = (Effect.tot, []) := by decide

/-- Single name folds into the singleton.  `with IO` → io_. -/
example :
    (Effect.fromNames ["IO"]).fst = Effect.io_ := by native_decide

/-- Multi-name list combines via `add` — row order doesn't
    matter per §9.3 commutativity. -/
example :
    (Effect.fromNames ["IO", "Alloc"]).fst =
    Effect.add Effect.io_ Effect.alloc_ := by native_decide

example :
    (Effect.fromNames ["Alloc", "IO"]).fst =
    Effect.add Effect.io_ Effect.alloc_ := by native_decide

/-- Unknown names flow to the residual list.  `with IO, Foo,
    Bar` splits IO into the algebraic row and {Foo, Bar} into
    the residual.  Residual is accumulated head-first (newest
    first), so `["Bar", "Foo"]` reflects the fold order —
    the elaborator treats this as a set, not an ordered list. -/
example :
    (Effect.fromNames ["IO", "Foo", "Bar"]).snd = ["Bar", "Foo"] :=
  by native_decide

/-- Residual dedups — repeating `Foo` doesn't double-add. -/
example :
    (Effect.fromNames ["Foo", "Foo"]).snd = ["Foo"] := by native_decide

/-! ## Composition — `Effect.add` lattice laws -/

-- Commutativity.
example : Effect.add Effect.io_ Effect.alloc_
        = Effect.add Effect.alloc_ Effect.io_ := Effect.add_comm _ _

-- `Tot` identity.
example : Effect.add Effect.tot Effect.io_ = Effect.io_ := Effect.tot_add _
example : Effect.add Effect.io_ Effect.tot = Effect.io_ := Effect.add_tot _

-- Idempotence (same effect combined with itself).
example : Effect.add Effect.io_ Effect.io_ = Effect.io_ :=
  Effect.add_idem _

/-! ## Subsumption — `Effect.LessEq` -/

-- `Tot ≤ e` for every `e` — the unit is the bottom.
example : Effect.LessEq Effect.tot Effect.io_ := by decide
example : Effect.LessEq Effect.tot Effect.alloc_ := by decide

-- `e ≤ e` — reflexivity.
example : Effect.LessEq Effect.io_ Effect.io_ := by decide

-- `Read ≤ Write` via the pre-saturation: `write_` has both
-- `read` and `write` true, so `read_ ≤ write_` decides true.
example : Effect.LessEq Effect.read_ Effect.write_ := by decide

-- `Write ≰ Read` — can't downgrade.
example : ¬ Effect.LessEq Effect.write_ Effect.read_ := by decide

-- Independent labels are non-related.
example : ¬ Effect.LessEq Effect.io_ Effect.alloc_ := by decide
example : ¬ Effect.LessEq Effect.alloc_ Effect.io_ := by decide

/-! ## Kernel Pi with effect — shape pinning

A function `fn f(a: i64) : i64 with IO` elaborates to:
```
Term.pi Grade.default
  (Term.ind "i64" [])
  (Term.ind "i64" [])
  Effect.io_
```

The `returnEffect` field is the Pi's 4th positional arg,
distinguishing it from `Tot` (the default on anonymous
arrows `A -> B`).  A regression that dropped the effect would
make these examples fail. -/

/-- Canonical Pi-with-IO shape. -/
def fnIO : Term :=
  Term.pi Grade.default
    (Term.ind "i64" []) (Term.ind "i64" [])
    Effect.io_

/-- Extract the returnEffect field from a Pi term, returning
    `none` on non-Pi input.  Scalar extraction avoids the
    DecidableEq-on-Term limitation (Term doesn't derive it). -/
def piEffect? (t : Term) : Option Effect :=
  match t with
  | Term.pi _ _ _ eff => some eff
  | _                 => none

example : piEffect? fnIO = some Effect.io_ := by native_decide

/-- Multi-label row flows to the Pi's returnEffect. -/
def fnIOAlloc : Term :=
  Term.pi Grade.default
    (Term.ind "i64" []) (Term.ind "i64" [])
    (Effect.add Effect.io_ Effect.alloc_)

example : piEffect? fnIOAlloc
        = some (Effect.add Effect.io_ Effect.alloc_) := by native_decide

/-- Default-Tot anonymous arrow `A -> B` keeps the empty
    effect row.  `Arrow` elaboration in `Elaborate.lean` builds
    `Term.pi _ _ _ Effect.tot` for this case. -/
def anonArrow : Term :=
  Term.pi Grade.default
    (Term.ind "i64" []) (Term.ind "i64" [])
    Effect.tot

example : piEffect? anonArrow = some Effect.tot := by native_decide

end FX.Derived.Effect
