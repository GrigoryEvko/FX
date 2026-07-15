/-! # Axis/Term — the exact strong-normalization boundary: modular / persistent SN (term-19)

The term-axis mirror of `term-6` (Toyama modularity) from the SN side.  `term-6` shipped the POSITIVE
modular criterion — the union of two commuting / disjoint strongly-normalizing systems is strongly
normalizing (`fxTerm_hasModularStrongNormalizationCriterion`, in
`Core/Metatheory/Normalization/.../StrongNormalizationUnion`).  This file pins down the EXACT BOUNDARY of
that criterion (each piece zero-axiom, abstract over any step relation, with SN ≡ "the inverse step
relation is well-founded", matching `Core/.../Newman.lean`):

  * **Persistence** (`strongNorm_subrelation` ★): strong normalization RESTRICTS to subsystems — any
    sub-relation of a strongly-normalizing relation is strongly normalizing.  Hence `strongNorm_union_left`
    / `strongNorm_union_right` (★): if a union `R ∪ S` is SN then each component is SN.  So the SN-of-union
    ⟹ SN-of-components direction ALWAYS holds.
  * **Necessity** (the counterexample ★): the CONVERSE fails — two strongly-normalizing relations whose
    union is NOT strongly normalizing.  On `Bool`, `forwardStep` (`false → true`) and `backwardStep`
    (`true → false`) are each SN (one step, no cycle), but `unionStep` has the 2-cycle
    `false → true → false → ⋯` (`unionStep_notStronglyNormalizing`).  This is the minimal witness that SN
    is NOT modular without the `term-6` commutation/disjointness side conditions — it shows those
    conditions are NECESSARY, not merely sufficient.

Together: SN(R ∪ S) ⟹ SN(R) ∧ SN(S) unconditionally (persistence), but SN(R) ∧ SN(S) ⟹ SN(R ∪ S) only
under the `term-6` conditions (necessity counterexample) — the exact boundary.

## Honest scope

Shipped: the persistence direction (subsystems + the union-to-components projection) and the necessity
counterexample (SN is not modular in general).  The POSITIVE modular criterion itself is `term-6`
(`fxTerm_hasModularStrongNormalizationCriterion`), re-used not re-proved.  DEFERRED: the full Toyama
persistence theorem for first-order TRSs (SN modular for LEFT-LINEAR or layer-preserving unions) and the
finer Gramlich/Ohlebusch necessity taxonomy — those are statements about a concrete term signature, beyond
this abstract `Acc` boundary.

## Zero-axiom verification

`strongNorm_subrelation` transfers accessibility across the sub/super inverse relations by `Acc` induction;
the `Bool` SN proofs are `Acc.intro` with `Bool.noConfusion` on the impossible predecessor; the
non-termination is the standard "no element is accessible under a cycle" `Acc` induction.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/Core/Metatheory/Normalization/StrongNorm/ModularSNBoundary.lean`.
-/

namespace FX1Poly.Core

/-! ## Persistence — SN restricts to subsystems -/

/-- ★ **Persistence of strong normalization under sub-systems**: if every `sub`-step is a `super`-step and
`super` is strongly normalizing (its inverse is well-founded), then `sub` is strongly normalizing.  A
subsystem of a terminating system terminates. -/
theorem strongNorm_subrelation {Carrier : Type} {sub super : Carrier → Carrier → Prop}
    (subset : ∀ {origin reduct : Carrier}, sub origin reduct → super origin reduct)
    (superStronglyNormalizing : WellFounded (fun reduct origin => super origin reduct)) :
    WellFounded (fun reduct origin => sub origin reduct) := by
  refine WellFounded.intro (fun point => ?_)
  have accessibleUnderSuper : Acc (fun reduct origin => super origin reduct) point :=
    superStronglyNormalizing.apply point
  induction accessibleUnderSuper with
  | intro current _accessiblePredecessors inductionHypothesis =>
      exact Acc.intro current (fun reduct subStep => inductionHypothesis reduct (subset subStep))

/-- ★ If a union is strongly normalizing, its LEFT component is strongly normalizing. -/
theorem strongNorm_union_left {Carrier : Type} {leftStep rightStep : Carrier → Carrier → Prop}
    (unionStronglyNormalizing :
      WellFounded (fun reduct origin => (leftStep origin reduct ∨ rightStep origin reduct))) :
    WellFounded (fun reduct origin => leftStep origin reduct) :=
  strongNorm_subrelation (fun leftHolds => Or.inl leftHolds) unionStronglyNormalizing

/-- ★ If a union is strongly normalizing, its RIGHT component is strongly normalizing. -/
theorem strongNorm_union_right {Carrier : Type} {leftStep rightStep : Carrier → Carrier → Prop}
    (unionStronglyNormalizing :
      WellFounded (fun reduct origin => (leftStep origin reduct ∨ rightStep origin reduct))) :
    WellFounded (fun reduct origin => rightStep origin reduct) :=
  strongNorm_subrelation (fun rightHolds => Or.inr rightHolds) unionStronglyNormalizing

/-! ## Necessity — SN is not modular: two SN systems whose union loops -/

/-- The forward step on `Bool`: `false → true`. -/
def forwardStep (current next : Bool) : Prop := current = false ∧ next = true

/-- The backward step on `Bool`: `true → false`. -/
def backwardStep (current next : Bool) : Prop := current = true ∧ next = false

/-- The union of the two single steps — it has the 2-cycle `false → true → false → ⋯`. -/
def unionStep (current next : Bool) : Prop := forwardStep current next ∨ backwardStep current next

/-- ★ The forward step alone is strongly normalizing (one step `false → true`, no cycle). -/
theorem forwardStep_isStronglyNormalizing :
    WellFounded (fun reduct origin => forwardStep origin reduct) := by
  have accessibleTrue : Acc (fun reduct origin => forwardStep origin reduct) true :=
    Acc.intro true (fun reduct step => Bool.noConfusion step.1)
  refine WellFounded.intro (fun origin => ?_)
  cases origin with
  | true => exact accessibleTrue
  | false =>
      refine Acc.intro false (fun reduct step => ?_)
      have reductIsTrue : reduct = true := step.2
      subst reductIsTrue
      exact accessibleTrue

/-- ★ The backward step alone is strongly normalizing (one step `true → false`, no cycle). -/
theorem backwardStep_isStronglyNormalizing :
    WellFounded (fun reduct origin => backwardStep origin reduct) := by
  have accessibleFalse : Acc (fun reduct origin => backwardStep origin reduct) false :=
    Acc.intro false (fun reduct step => Bool.noConfusion step.1)
  refine WellFounded.intro (fun origin => ?_)
  cases origin with
  | false => exact accessibleFalse
  | true =>
      refine Acc.intro true (fun reduct step => ?_)
      have reductIsFalse : reduct = false := step.2
      subst reductIsFalse
      exact accessibleFalse

/-- ★ **Necessity** — the union is NOT strongly normalizing: the 2-cycle `false → true → false → ⋯` makes
every element inaccessible.  So the union of two strongly-normalizing relations need NOT be strongly
normalizing — SN is not modular without the `term-6` side conditions. -/
theorem unionStep_notStronglyNormalizing :
    ¬ WellFounded (fun reduct origin => unionStep origin reduct) := by
  intro wellFounded
  have noElementAccessible :
      ∀ {point : Bool}, Acc (fun reduct origin => unionStep origin reduct) point → False := by
    intro point accessiblePoint
    induction accessiblePoint with
    | intro current _accessiblePredecessors inductionHypothesis =>
        cases current with
        | false => exact inductionHypothesis true (Or.inl ⟨rfl, rfl⟩)
        | true => exact inductionHypothesis false (Or.inr ⟨rfl, rfl⟩)
  exact noElementAccessible (wellFounded.apply false)

/-! ## Sharpening the necessity — no normal form + the explicit infinite reduction -/

/-- Every `Bool` takes a `unionStep` to its negation (the cycle generator). -/
theorem unionStep_negation (current : Bool) : unionStep current (! current) := by
  cases current with
  | false => exact Or.inl ⟨rfl, rfl⟩
  | true => exact Or.inr ⟨rfl, rfl⟩

/-- ★ The union has NO normal form: every element can take a `unionStep`.  So the union is not even WEAKLY
normalizing — no terminating reduction exists at all, a strictly stronger failure than `¬ SN`. -/
theorem unionStep_hasNoNormalForm (point : Bool) : ∃ next : Bool, unionStep point next :=
  ⟨! point, unionStep_negation point⟩

/-- The explicit non-terminating reduction sequence: `false`, `true`, `false`, … forever. -/
def unionCycle : Nat → Bool
  | 0 => false
  | index + 1 => ! (unionCycle index)

/-- ★ The cycle is a genuine infinite `unionStep` reduction sequence — `unionCycle index` reduces to
`unionCycle (index + 1)` at EVERY step.  This is the constructive witness of non-termination: an explicit
function `Nat → Bool` realizing the infinite descent, not merely the negation `¬ WellFounded`. -/
theorem unionCycle_steps (index : Nat) :
    unionStep (unionCycle index) (unionCycle (index + 1)) :=
  unionStep_negation (unionCycle index)

end FX1Poly.Core
