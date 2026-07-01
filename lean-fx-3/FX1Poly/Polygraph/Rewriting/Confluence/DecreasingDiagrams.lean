import FX1Poly.Polygraph.Rewriting.Confluence.DiamondConfluence

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

## What this file ships

The framework + the universality over the diamond + the **single-label theorem** (`StronglyConfluent`,
Huet's strong confluence ⟹ confluence — a sound, non-degenerate decreasing-diagrams confluence theorem,
strictly more general than the diamond, so `diamondConfluence` is its corollary).

## Honest scope

The deep MULTI-label van Oostrom THEOREM — `LocallyDecreasing ⟹ Confluent` for a genuine well-founded label
order, proved by well-founded multiset induction over conversions — is NOT here; it is the deferred capstone,
and it is what makes the criterion FULLY "universal".  The single-label case (strong confluence) IS proved.
The commutation criterion `confluentOfUnionDiamonds` is a further two-label instance (deferred).  The label
order here is `Nat` (concrete); the bound is the SUM `labelLeft + labelRight` (the propext-clean two-label
coordination, avoiding `Nat.max`'s lemmas).

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

/-! ## The single-label decreasing-diagrams theorem — Huet's strong confluence

The deep multi-label van Oostrom theorem is deferred, but its SINGLE-LABEL case is a genuine, sound
confluence theorem provable here: Huet's **strong confluence** (every local peak `b ← a → c` closes with
`b →* d` and `c →= d` — the latter in at most one step) implies confluence.  This subsumes the diamond
property (the diamond closes with `c → d`, a one-step `c →= d`) and is the sound core that decreasing
diagrams generalizes to many labels. -/

/-- The **at-most-one-step** relation `→=` (a single step, or equality). -/
def reflStep (rel : Carrier → Carrier → Prop) (source target : Carrier) : Prop :=
  rel source target ∨ source = target

/-- **Strong confluence** (Huet): every local peak `b ← a → c` joins with `b →* common` and `c →= common`
(the right side in at most one step). -/
def StronglyConfluent (rel : Carrier → Carrier → Prop) : Prop :=
  ∀ {start leftStep rightStep : Carrier}, rel start leftStep → rel start rightStep →
    ∃ common, ReflTransClosure rel leftStep common ∧ reflStep rel rightStep common

/-- **The strong-confluence strip lemma**: a single step strips against a many-step reduction, the single
side reaching the join in `→*`, the many side in `→=`.  By induction on the many chain, using strong
confluence on each first step. -/
theorem stronglyConfluent_strip {rel : Carrier → Carrier → Prop} (sc : StronglyConfluent rel)
    {start manyTarget : Carrier} (manyChain : ReflTransClosure rel start manyTarget) :
    ∀ {oneTarget : Carrier}, rel start oneTarget →
      ∃ common, ReflTransClosure rel oneTarget common ∧ reflStep rel manyTarget common := by
  induction manyChain with
  | refl _ =>
      intro oneTarget oneStep
      exact ⟨oneTarget, ReflTransClosure.refl oneTarget, Or.inl oneStep⟩
  | head first rest ihRest =>
      intro oneTarget oneStep
      obtain ⟨meet, oneToMeet, reflMidMeet⟩ := sc oneStep first
      cases reflMidMeet with
      | inl midToMeet =>
          obtain ⟨common, meetToCommon, reflManyCommon⟩ := ihRest midToMeet
          exact ⟨common, oneToMeet.trans meetToCommon, reflManyCommon⟩
      | inr midEqMeet =>
          subst midEqMeet
          exact ⟨_, oneToMeet.trans rest, Or.inr rfl⟩

/-- The confluence core for strong confluence (right chain kept quantified): strip each left first step
against the whole right chain, recurse on the left remainder, compose. -/
theorem stronglyConfluent_confluentAux {rel : Carrier → Carrier → Prop} (sc : StronglyConfluent rel)
    {start leftTarget : Carrier} (leftChain : ReflTransClosure rel start leftTarget) :
    ∀ {rightTarget : Carrier}, ReflTransClosure rel start rightTarget →
      Joinable rel leftTarget rightTarget := by
  induction leftChain with
  | refl _ =>
      intro rightTarget rightChain
      exact ⟨rightTarget, rightChain, ReflTransClosure.refl rightTarget⟩
  | head first _rest ihRest =>
      intro rightTarget rightChain
      obtain ⟨common, middleToCommon, rightReflCommon⟩ := stronglyConfluent_strip sc rightChain first
      obtain ⟨joinPoint, leftToJoin, commonToJoin⟩ := ihRest middleToCommon
      refine ⟨joinPoint, leftToJoin, ?_⟩
      cases rightReflCommon with
      | inl rightToCommon => exact (ReflTransClosure.single rightToCommon).trans commonToJoin
      | inr rightEqCommon => subst rightEqCommon; exact commonToJoin

/-- ★ **Strong confluence ⟹ confluence** (Huet) — the SINGLE-LABEL decreasing-diagrams theorem.  A
strongly confluent relation has confluent reflexive-transitive closure, no termination needed. -/
theorem stronglyConfluent_implies_confluent {rel : Carrier → Carrier → Prop}
    (sc : StronglyConfluent rel) : Confluent rel := by
  intro _source _leftReduct _rightReduct leftChain rightChain
  exact stronglyConfluent_confluentAux sc leftChain rightChain

/-- ★ **The diamond property is strongly confluent** — so `diamondConfluence` is a corollary of Huet's
theorem (the diamond closes each peak with one step on each side, a fortiori `→* / →=`). -/
theorem diamondProperty_implies_stronglyConfluent {rel : Carrier → Carrier → Prop}
    (diamond : DiamondProperty rel) : StronglyConfluent rel := by
  intro _start _leftStep _rightStep stepLeft stepRight
  obtain ⟨common, leftToCommon, rightToCommon⟩ := diamond stepLeft stepRight
  exact ⟨common, ReflTransClosure.single leftToCommon, Or.inl rightToCommon⟩

/-- ★ **Strong confluence is the single-label decreasing diagram.**  A strongly confluent relation, labeled
label-blindly, is `LocallyDecreasing` — its peaks close by valleys whose steps are below every positive
bound — tying Huet's theorem into the decreasing-diagram framework. -/
theorem stronglyConfluent_isLocallyDecreasing {rel : Carrier → Carrier → Prop}
    (sc : StronglyConfluent rel) : LocallyDecreasing (fun _label => rel) := by
  intro source leftReduct rightReduct labelLeft labelRight stepLeft stepRight
  obtain ⟨common, leftToCommon, rightReflCommon⟩ := sc stepLeft stepRight
  refine ⟨common,
    ReflTransClosure.monotone (fun step => ⟨0, Nat.succ_pos (labelLeft + labelRight), step⟩) leftToCommon,
    ?_⟩
  cases rightReflCommon with
  | inl rightToCommon =>
      exact ReflTransClosure.single ⟨0, Nat.succ_pos (labelLeft + labelRight), rightToCommon⟩
  | inr rightEqCommon => subst rightEqCommon; exact ReflTransClosure.refl _

end FX1Poly.Core
