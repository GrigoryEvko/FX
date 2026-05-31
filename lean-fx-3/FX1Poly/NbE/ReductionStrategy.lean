import FX1Poly.NbE.DesignDecision

/-! # Foundation/PolyCell/NbE/ReductionStrategy
   — committed reduction strategy for the NbE eval implementation

The reduction-strategy choice for NbE eval (the headline normalizer
feeding decidable raw Conv) as a queryable marker.  The strategy
choice has metatheoretic consequences AND performance implications.

## The choice: CALL-BY-NAME (CBN)

Against the hybrid design (eval = fold returning RawTerm in β-NF)
and the SN commitment, the committed reduction strategy is
**call-by-name** (CBN).

## Trade-off analysis

### Call-by-name (committed)

* **Termination**: terminates iff the input term is SN.  For
  well-typed terms (typed SN proof), every term is SN ⟹ eval is
  total on typed inputs.
* **Implementation simplicity**: descend into the head first,
  β-reduce on `app (lam body) arg → subst0 body arg` WITHOUT
  pre-evaluating arg.  Arg is re-evaluated wherever it appears
  in body's NF — but at full-NF that's once per occurrence,
  which is unavoidable for canonical NFs anyway.
* **Effect compatibility**: CBN never evaluates an arg that
  isn't used by the body — natural fit for FX's effect tracking
  (no spurious effects from unused args).  Aligns with the
  typed-effects extension.
* **Subsumption**: CBN reaches the same NF as CBV/full when
  both terminate; the choice is observationally invisible on
  SN inputs.
* **Reference**: Abel-Coquand-Dybjer LFMTP 2007 NbE for MLTT
  uses CBN at the meta-level evaluation.

### Call-by-value (rejected)

* Evaluates args BEFORE substituting — can diverge on terms
  that are SN under CBN but have non-SN sub-terms (the famous
  "Ω in dead branch" trap: `(lam _. unit) Ω` is CBN-SN but
  CBV-divergent).
* For FX's effect system: forces evaluation of effectful args
  even when the result is discarded — semantically WRONG for
  effect tracking unless lifted to a monadic eval.
* Requires a "values done" predicate at each substitution point,
  doubling the substrate.
* Reasonable choice for compilation but wrong for NbE.

### Lazy (CBN + memoization) (rejected)

* Same termination story as CBN.
* Adds memoization: each unique sub-term is evaluated at most
  once.
* Better PERFORMANCE for terms with shared sub-expressions, but
  requires mutable state at the meta-level — incompatible with
  Lean 4's pure structural recursion model for kernel theorems.
* Memoization can be added as a compilation optimization
  (STRICT-COMPLEXITY witness work), without changing the core
  eval semantics.

### Full structural traversal (rejected)

* "Reduce everywhere top-down" — structurally recursive on the
  AST, reducing each generator's children before applying the
  generator's reduction rule.
* Equivalent to CBN on β-redexes (you reach the redex after
  recursing into the lam's body), but evaluates structural
  children eagerly.
* Conflates iota-redex firing with arg evaluation — harder to
  reason about for the Decidable Conv proof.

## Why CBN matches the hybrid design

The hybrid design's `eval : RawTerm → RawTerm` returns β-NF.
CBN aligns naturally:

* The fold engine descends structurally, but at `gen_app
  (gen_lam body) arg`, it β-fires WITHOUT pre-evaluating arg.
* arg is substituted into body's positions, and subsequent
  fold recursion evaluates each substituted position
  individually.
* This produces canonical β-NF: every redex eventually fires;
  no work is done before substitution forces it.

## Consequences for the eval implementation

The `GenAlgebra.NbE` algebra dispatches per generator:

* `gen_app` clause:
  - If the function child is `gen_lam body`: β-fire to
    `subst0 body arg` (DON'T pre-evaluate arg).
  - Otherwise: recursively eval the function child first; if
    it reduces to a lam, retry the β-fire on the new shape.

* `gen_fst` clause:
  - If the arg child is `gen_pair a b`: iota-fire to `a`.
  - Otherwise: recursively eval the arg; if it reduces to a
    pair, retry.

* Other iota arms: analogous.

* Default (no reduction available): recursively eval all
  children then rebuild via `mkGen`.  This handles
  congruence: a closed `mkGen .gen_unit () .childNil` is a
  base case (no children to recurse into, no reduction).

## Consequences for Decidable Conv

The Decidable Conv algorithm is:
```
decide (Conv a b) := RawTerm.decEq (RawTerm.eval a) (RawTerm.eval b)
```

CBN guarantees:
* `Conv a b ⟹ RawTerm.eval a = RawTerm.eval b` (eval is sound
  for Conv).
* `RawTerm.eval a = RawTerm.eval b ⟹ Conv a b` (eval is
  complete for Conv on SN terms).

Both directions hold: soundness and completeness of eval for
Conv on SN terms.

## Consequences for typed-η

The typed η-long readback pass (`etaLongReadback : RawTerm →
Ty → RawTerm`) is APPLIED AFTER eval.  It inserts η-expansions
at typed positions but doesn't change the underlying eval's
reduction strategy.

So: typed β+η Decidable Conv is:
```
decide (Conv_typed a b : at type T) :=
  RawTerm.decEq
    (etaLongReadback (RawTerm.eval a) T)
    (etaLongReadback (RawTerm.eval b) T)
```

CBN's choice is invisible at the typed-η layer — that layer
just sees a RawTerm in β-NF as input.

## Out of scope

* **Memoization** is a STRICT-COMPLEXITY performance optimization
  on top of CBN, not part of the committed eval semantics.
* **Parallel evaluation** is likewise out of scope.

## Why CBN

* The hybrid design settles eval's RETURN TYPE (RawTerm).
* CBN is the simplest implementation strategy for full-NF eval.
* All four candidates (CBN/CBV/Lazy/Full) reach the same NF on
  SN inputs, so the choice is observationally invisible at the
  typed layer.
* CBN's simplicity avoids meta-level state.

## Audit-gated marker

A `ReductionStrategy` marker enum + a
`ReductionStrategy.committed := .callByName` value + a `rfl`-pinned
theorem, queryable by the eval implementation to specialize.

## Zero-axiom verification

Three declarations, all closing by `rfl` or direct value
construction.  No `axiom`, no `sorry`, no Classical.  Audit-gated. -/

namespace FX1Poly.NbE

/-- Marker tracking the NbE reduction strategy.

* `callByName` — the committed strategy: arg substitution
  deferred until use.
* `callByValue` — evaluates args before substituting; not chosen
  for FX (incompatible with effect tracking + can diverge on
  CBN-SN inputs with non-SN sub-terms).
* `lazy` — CBN + memoization (a performance optimization).
* `fullStructural` — top-down structural traversal; not chosen
  (conflates iota firing with arg evaluation).
* `undecided` — placeholder for an uncommitted choice. -/
inductive ReductionStrategy
  | callByName
  | callByValue
  | lazy
  | fullStructural
  | undecided
deriving DecidableEq, BEq, Repr

/-- The committed NbE reduction strategy for eval.

Call-by-name: descend into the head first, β-fire on
`app (lam body) arg → subst0 body arg` WITHOUT pre-evaluating
arg.  Matches the hybrid design and the Abel-Coquand-Dybjer
2007 NbE-for-MLTT reference. -/
def ReductionStrategy.committed : ReductionStrategy := .callByName

/-- Pinned theorem witnessing that the committed strategy is
call-by-name.  Future code that matches on
`ReductionStrategy.committed` can rely on this `rfl` to
specialize. -/
theorem ReductionStrategy.committed_is_cbn :
    ReductionStrategy.committed = .callByName := rfl

/-- Decidability instance for the committed-strategy marker.
Useful in audit checks that confirm `ReductionStrategy.committed`
has not silently regressed to `.undecided` during a refactor. -/
instance : Decidable (ReductionStrategy.committed = .callByName) :=
  decEq ReductionStrategy.committed .callByName

/-- Cross-reference theorem: the reduction strategy commitment is
compatible with the hybrid design.  Both must agree for the NbE
pipeline to be self-consistent. -/
theorem ReductionStrategy.compatible_with_hybrid_design :
    ReductionStrategy.committed = .callByName ∧
    NbEDesign.committed = .hybrid :=
  ⟨ReductionStrategy.committed_is_cbn, NbEDesign.committed_is_hybrid⟩

end FX1Poly.NbE
