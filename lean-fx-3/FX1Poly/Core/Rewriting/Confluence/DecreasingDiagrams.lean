import FX1Poly.Core.Rewriting.Confluence.DiamondConfluence

/-! # Core/Rewriting/Confluence — decreasing diagrams: the universal confluence framework

Van Oostrom's **decreasing diagrams** is the universal confluence criterion for abstract rewriting: label
each step by an element of a well-founded order, and if every LOCAL PEAK `b ←(α) a →(β) c` can be joined by
a "decreasing" valley (steps bounded by the peak labels), then the whole relation is confluent.  It
SUBSUMES essentially every standard confluence proof — the diamond property, Newman's lemma, Hindley-Rosen
commutation — each is a decreasing-diagram instance under a suitable labeling.

This file ships the FRAMEWORK and the UNIVERSALITY demonstration over the diamond property: a labeled
rewrite system (`labeledUnion` / `labeledBelow`), the locally-decreasing condition (`LocallyDecreasing`,
the sum-bounded valley form), and the proof that a relation with the DIAMOND PROPERTY is the degenerate
SINGLE-LABEL decreasing diagram (`diamondProperty_isLocallyDecreasing`) whose union confluence is recovered
(`labeledUnion_diamond_isConfluent`).

## Honest scope

The deep van Oostrom THEOREM itself — `LocallyDecreasing ⟹ Confluent` for a genuine well-founded label
order, proved by well-founded multiset induction over conversions — is NOT here; it is the deferred
capstone, and it is what makes the criterion "universal".  What is shipped is the framework plus the
demonstration that the shipped diamond criterion is a decreasing-diagram instance (the universality
direction); the commutation criterion `confluentOfUnionDiamonds` is a further two-label instance (deferred).
The label order here is `Nat` (concrete); the bound is the SUM `labelLeft + labelRight` (the propext-clean
two-label coordination, avoiding `Nat.max`'s lemmas).

## Zero-axiom verification

`ReflTransClosure` / `DiamondProperty` over the shipped diamond layer, `Nat.succ_pos` for the label bound.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditCoreTerminationOrders.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Carrier : Type carrierUniverse}

/-- The **union** of a `Nat`-labeled rewrite system — the step relation with labels forgotten. -/
def labeledUnion (step : Nat → Carrier → Carrier → Prop) (source target : Carrier) : Prop :=
  ∃ label, step label source target

/-- The steps of a labeled system whose label is **strictly below** a bound. -/
def labeledBelow (step : Nat → Carrier → Carrier → Prop) (bound : Nat)
    (source target : Carrier) : Prop :=
  ∃ label, label < bound ∧ step label source target

/-- A below-bound step is a union step (forget the bound). -/
theorem labeledBelow.toUnion {step : Nat → Carrier → Carrier → Prop} {bound : Nat}
    {source target : Carrier} (belowStep : labeledBelow step bound source target) :
    labeledUnion step source target := by
  obtain ⟨label, _bounded, stepLabel⟩ := belowStep
  exact ⟨label, stepLabel⟩

/-- The **locally-decreasing** (decreasing-diagram) condition, sum-bounded valley form: every local peak
`b ←(labelLeft) a →(labelRight) c` joins to a common reduct by valleys whose every step has label
`≤ labelLeft + labelRight` (i.e. strictly below `labelLeft + labelRight + 1`).  The full van Oostrom
conversion form (with the optional peak-label steps and the interleaved `↔` conversion) and the
`LocallyDecreasing ⟹ Confluent` theorem are deferred. -/
def LocallyDecreasing (step : Nat → Carrier → Carrier → Prop) : Prop :=
  ∀ {source leftReduct rightReduct : Carrier} {labelLeft labelRight : Nat},
    step labelLeft source leftReduct → step labelRight source rightReduct →
    ∃ common,
      ReflTransClosure (labeledBelow step (Nat.succ (labelLeft + labelRight))) leftReduct common ∧
      ReflTransClosure (labeledBelow step (Nat.succ (labelLeft + labelRight))) rightReduct common

/-! ## Universality — the diamond property is the degenerate decreasing diagram -/

/-- ★ **The diamond property is a decreasing-diagram instance.**  A relation with the `DiamondProperty`,
labeled label-blindly (every label carries the whole relation), is `LocallyDecreasing` — the degenerate
SINGLE-label decreasing diagram, where each local peak closes in one step each (label `0`, below every
positive bound).  This is the universality direction: decreasing diagrams generalize the diamond. -/
theorem diamondProperty_isLocallyDecreasing {rel : Carrier → Carrier → Prop}
    (diamond : DiamondProperty rel) : LocallyDecreasing (fun _label => rel) := by
  intro source leftReduct rightReduct labelLeft labelRight stepLeft stepRight
  obtain ⟨common, leftToCommon, rightToCommon⟩ := diamond stepLeft stepRight
  exact ⟨common,
    ReflTransClosure.single ⟨0, Nat.succ_pos (labelLeft + labelRight), leftToCommon⟩,
    ReflTransClosure.single ⟨0, Nat.succ_pos (labelLeft + labelRight), rightToCommon⟩⟩

/-- ★ **The decreasing-diagram framework recovers the diamond's confluence.**  The union of the diamond's
label-blind labeling is confluent (via `diamondConfluence`) — the framework reproduces, in the degenerate
single-label case, the confluence the diamond criterion already delivers. -/
theorem labeledUnion_diamond_isConfluent {rel : Carrier → Carrier → Prop}
    (diamond : DiamondProperty rel) : Confluent (labeledUnion (fun _label => rel)) := by
  apply diamondConfluence
  intro _source _leftStep _rightStep stepLeftUnion stepRightUnion
  obtain ⟨_labelLeft, stepLeft⟩ := stepLeftUnion
  obtain ⟨_labelRight, stepRight⟩ := stepRightUnion
  obtain ⟨common, leftToCommon, rightToCommon⟩ := diamond stepLeft stepRight
  exact ⟨common, ⟨0, leftToCommon⟩, ⟨0, rightToCommon⟩⟩

end FX1Poly.Core
