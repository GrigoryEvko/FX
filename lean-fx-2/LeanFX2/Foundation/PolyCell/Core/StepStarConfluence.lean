import LeanFX2.Foundation.PolyCell.Core.CdLemma

/-! # Foundation/PolyCell/Core/StepStarConfluence
    - M8 confluence bridge over the v2 raw substrate

M7 ships the local one-step join theorem `cd_lemma`.  This file pins the
M8 bridge shape without overclaiming global Church-Rosser: local confluence
alone does not imply global confluence for an arbitrary non-terminating rewrite
system.  The global theorem is therefore factored through the standard strip
property, and raw `Conv` transitivity is derived from global confluence.
-/

namespace LeanFX2.Foundation.PolyCell.Core

namespace StepStar

/-- Two raw terms join when they reduce to a common reduct by `StepStar`. -/
def Join {scope : Nat} (leftTerm rightTerm : RawTerm scope) : Prop :=
  ∃ commonTerm : RawTerm scope,
    StepStar leftTerm commonTerm ∧ StepStar rightTerm commonTerm

/-- Global Church-Rosser for the v2 raw `StepStar` relation. -/
def HasConfluence : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    StepStar sourceTerm leftReduct →
    StepStar sourceTerm rightReduct →
    Join leftReduct rightReduct

/-- Strip property: a single step can be joined against an arbitrary
`StepStar` chain from the same source. -/
def HasStrip : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    Step sourceTerm leftReduct →
    StepStar sourceTerm rightReduct →
    Join leftReduct rightReduct

/-- M7's `cd_lemma` gives the one-step/one-step local join, not global
confluence by itself. -/
theorem localJoin_of_cdLemma {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct) :
    Join leftReduct rightReduct :=
  cd_lemma leftStep rightStep

/-- A single step joins with the reflexive right chain. -/
theorem joinStepWithReflRight {scope : Nat}
    {sourceTerm leftReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct) :
    Join leftReduct sourceTerm :=
  ⟨leftReduct, StepStar.refl _, StepStar.single leftStep⟩

/-- A single step joins with a single-step right chain by M7. -/
theorem joinStepWithSingleRight {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct) :
    Join leftReduct rightReduct :=
  localJoin_of_cdLemma leftStep rightStep

/-- The standard strip-to-Church-Rosser lift.

This is the exact reusable M8 spine: once the strip property is supplied
(from a parallel-reduction diamond or a Newman-style Noetherian argument),
arbitrary diverging `StepStar` chains join. -/
theorem confluence_of_strip (hasStrip : HasStrip) :
    HasConfluence := by
  intro scope sourceTerm leftReduct rightReduct leftChain rightChain
  induction leftChain generalizing rightReduct with
  | refl _ =>
      exact ⟨rightReduct, rightChain, StepStar.refl _⟩
  | trans headStep tailChain tailIH =>
      obtain ⟨stripReduct, headChain, rightToStrip⟩ :=
        hasStrip headStep rightChain
      obtain ⟨commonReduct, leftToCommon, stripToCommon⟩ :=
        tailIH headChain
      exact
        ⟨ commonReduct
        , leftToCommon
        , StepStar.trans_compose rightToStrip stripToCommon ⟩

end StepStar

/-- Raw conversion on the v2 substrate: symmetric closure of `StepStar` via a
shared common reduct. -/
def Conv {scope : Nat} (sourceTerm targetTerm : RawTerm scope) : Prop :=
  StepStar.Join sourceTerm targetTerm

namespace Conv

/-- Reflexivity of raw conversion. -/
theorem refl {scope : Nat} (sourceTerm : RawTerm scope) :
    Conv sourceTerm sourceTerm :=
  ⟨sourceTerm, StepStar.refl _, StepStar.refl _⟩

/-- Symmetry of raw conversion. -/
theorem sym {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (convertibility : Conv sourceTerm targetTerm) :
    Conv targetTerm sourceTerm :=
  Exists.elim convertibility
    (fun commonTerm chains =>
      ⟨commonTerm, chains.2, chains.1⟩)

/-- A `StepStar` chain induces raw conversion, using its target as the common
reduct. -/
theorem fromStepStar {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : StepStar sourceTerm targetTerm) :
    Conv sourceTerm targetTerm :=
  ⟨targetTerm, chain, StepStar.refl _⟩

/-- A single `Step` induces raw conversion. -/
theorem fromStep {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (step : Step sourceTerm targetTerm) :
    Conv sourceTerm targetTerm :=
  fromStepStar (StepStar.single step)

/-- Raw conversion transitivity follows from global `StepStar` confluence. -/
theorem trans_of_confluence
    (hasConfluence : StepStar.HasConfluence)
    {scope : Nat} {firstTerm middleTerm lastTerm : RawTerm scope}
    (firstMiddle : Conv firstTerm middleTerm)
    (middleLast : Conv middleTerm lastTerm) :
    Conv firstTerm lastTerm := by
  obtain ⟨firstMiddleReduct, firstToReduct, middleToFirstReduct⟩ :=
    firstMiddle
  obtain ⟨middleLastReduct, middleToLastReduct, lastToReduct⟩ :=
    middleLast
  obtain ⟨commonReduct, firstReductToCommon, lastReductToCommon⟩ :=
    hasConfluence middleToFirstReduct middleToLastReduct
  exact
    ⟨ commonReduct
    , StepStar.trans_compose firstToReduct firstReductToCommon
    , StepStar.trans_compose lastToReduct lastReductToCommon ⟩

/-- Raw conversion transitivity follows from the strip property. -/
theorem trans_of_strip
    (hasStrip : StepStar.HasStrip)
    {scope : Nat} {firstTerm middleTerm lastTerm : RawTerm scope}
    (firstMiddle : Conv firstTerm middleTerm)
    (middleLast : Conv middleTerm lastTerm) :
    Conv firstTerm lastTerm :=
  trans_of_confluence
    (StepStar.confluence_of_strip hasStrip)
    firstMiddle middleLast

end Conv

end LeanFX2.Foundation.PolyCell.Core
