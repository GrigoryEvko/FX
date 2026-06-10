import FX1Poly.Typed.CombinatoryLogic
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Typed/ChurchPairs — Church-encoded products in the λ-fragment

The shipped Church encodings cover booleans (#981) and numerals (#989).  This file adds the missing data shape —
PRODUCTS — via the Church pair, demonstrating that the Π-fragment encodes Σ-like data through polymorphism:

  `pair a b = λf. f a b`,   `fst = λp. p K`,   `snd = λp. p (λx.λy.y)`

  * **`pairFst_reduces`** — `fst (pair a b) ↝* a`: applying `fst` instantiates `f := K`, giving `K a b`, which the
    K-rule (`combinatorK_reduces`, #1015) selects to `a`.  The two stored components survive as `weaken a` /
    `weaken b` inside the pair and re-emerge via the `subst0 (weaken a) K = a` cancellation
    (`weaken_subst_singleton`).
  * **`pairSnd_reduces`** — `snd (pair a b) ↝* b`: the dual, instantiating `f` with the second-projector
    `λx.λy.y` (which discards its first argument and returns the second), selecting `b`.
  * **`secondProjector_reduces`** — `(λx.λy.y) a b ↝* b`: the second-projection rule.  `(λx.λy.y) a` discards
    `x` and reduces to `λy.y = I` (by `rfl` — the bound `x` is simply absent from the body), then the I-rule
    selects `b`.
  * **`pairProjectionsRecover` (★)** — the round-trip bundle: for every `a, b`, `fst (pair a b) ↝* a` AND
    `snd (pair a b) ↝* b`.  The Church pair faithfully STORES both components and RECOVERS each — products are
    realized in the pure Π-fragment, no primitive Σ needed.

Everything is the raw `Step` relation; no typing derivation is consulted.  The reductions hold for SYMBOLIC
`a, b` (not just concrete witnesses): the symbolic components re-emerge through the `weaken_subst_singleton`
cancellation, exactly the K-rule pattern.

## Zero-axiom verification

`secondProjector_reduces` is a function-position congruence (`Step.cong .gen_app ()` + `StepChildren.here`) into a
`rfl`-definitional `λx.λy.y → I` reduct, then `combinatorI_reduces` (#1015).  `pairFst_reduces` / `pairSnd_reduces`
chain two `Step.beta` β-steps (the second's symbolic-component contractum rewritten by named `subst0`-typed
cancellation `have`s — `RawTerm.weaken_subst_singleton`, stated at `subst0` so the `rw` matches the term) with the
K-rule / second-projection rule.  `pairProjectionsRecover` bundles the two.  No `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- `pair a b = λf. f a b` — the Church pair storing `a` and `b` (applied to a selector `f`). -/
def pairTerm (a b : RawTerm 0) : RawTerm 0 :=
  lamCell combinatorDomainAnn
    (appCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken a))
      (RawTerm.weaken b))

/-- `fst = λp. p K` — the first projection (selects the first stored component via `K`). -/
def churchFst : RawTerm 0 :=
  lamCell combinatorDomainAnn
    (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken combinatorK))

/-- `λx. λy. y` — the second projector (discards `x`, returns `y`). -/
def secondProjector : RawTerm 0 :=
  lamCell combinatorDomainAnn
    (lamCell combinatorDomainAnn (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))

/-- `snd = λp. p (λx.λy.y)` — the second projection (selects the second stored component). -/
def churchSnd : RawTerm 0 :=
  lamCell combinatorDomainAnn
    (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken secondProjector))

/-- **The second-projection rule: `(λx.λy.y) a b ↝* b`.**  `(λx.λy.y) a` discards `x` and reduces to `λy.y = I`
(`rfl`-definitional — `x` is absent from the body), then the I-rule selects `b`. -/
theorem secondProjector_reduces (a b : RawTerm 0) :
    StepStar (appCell (appCell secondProjector a) b) b := by
  have functionBeta : Step (appCell secondProjector a) combinatorI := Step.beta
  have congStep : Step (appCell (appCell secondProjector a) b) (appCell combinatorI b) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons b .childNil) functionBeta)
  exact StepStar.trans congStep (StepStar.trans (combinatorI_reduces b) (StepStar.refl _))

/-- **`fst (pair a b) ↝* a`.**  Applying `fst` instantiates the pair's selector `f := K`, yielding `K a b`,
which the K-rule selects to `a`.  The symbolic component `a` re-emerges through the `subst0 (weaken a) K = a`
cancellation. -/
theorem pairFst_reduces (a b : RawTerm 0) :
    StepStar (appCell churchFst (pairTerm a b)) a := by
  have step1 : Step (appCell churchFst (pairTerm a b)) (appCell (pairTerm a b) combinatorK) := Step.beta
  have step2 : Step (appCell (pairTerm a b) combinatorK)
      (appCell (appCell combinatorK (RawTerm.subst0 (RawTerm.weaken a) combinatorK))
        (RawTerm.subst0 (RawTerm.weaken b) combinatorK)) := Step.beta
  have cancelA : RawTerm.subst0 (RawTerm.weaken a) combinatorK = a :=
    RawTerm.weaken_subst_singleton a combinatorK
  have cancelB : RawTerm.subst0 (RawTerm.weaken b) combinatorK = b :=
    RawTerm.weaken_subst_singleton b combinatorK
  rw [cancelA, cancelB] at step2
  exact StepStar.trans step1 (StepStar.trans step2 (combinatorK_reduces a b))

/-- **`snd (pair a b) ↝* b`.**  Dual of `pairFst_reduces`: applying `snd` instantiates the selector with the
second-projector `λx.λy.y`, yielding `(λx.λy.y) a b`, which the second-projection rule selects to `b`. -/
theorem pairSnd_reduces (a b : RawTerm 0) :
    StepStar (appCell churchSnd (pairTerm a b)) b := by
  have step1 : Step (appCell churchSnd (pairTerm a b)) (appCell (pairTerm a b) secondProjector) := Step.beta
  have step2 : Step (appCell (pairTerm a b) secondProjector)
      (appCell (appCell secondProjector (RawTerm.subst0 (RawTerm.weaken a) secondProjector))
        (RawTerm.subst0 (RawTerm.weaken b) secondProjector)) := Step.beta
  have cancelA : RawTerm.subst0 (RawTerm.weaken a) secondProjector = a :=
    RawTerm.weaken_subst_singleton a secondProjector
  have cancelB : RawTerm.subst0 (RawTerm.weaken b) secondProjector = b :=
    RawTerm.weaken_subst_singleton b secondProjector
  rw [cancelA, cancelB] at step2
  exact StepStar.trans step1 (StepStar.trans step2 (secondProjector_reduces a b))

/-- ★ **The Church pair faithfully stores and recovers both components.**  For every `a, b`,
`fst (pair a b) ↝* a` AND `snd (pair a b) ↝* b` — products are realized in the pure Π-fragment via polymorphism,
no primitive Σ-type needed. -/
theorem pairProjectionsRecover (a b : RawTerm 0) :
    StepStar (appCell churchFst (pairTerm a b)) a ∧ StepStar (appCell churchSnd (pairTerm a b)) b :=
  ⟨pairFst_reduces a b, pairSnd_reduces a b⟩

end FX1Poly.Typed
