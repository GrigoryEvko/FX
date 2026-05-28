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

/-- The one-step-successor relation used for accessibility/termination:
`laterTerm` is below `earlierTerm` when `earlierTerm` takes one `Step`
to `laterTerm`. -/
def StepSuccessor {scope : Nat} (laterTerm earlierTerm : RawTerm scope) :
    Prop :=
  Step earlierTerm laterTerm

/-- A raw term is strongly normalizing when there is no infinite chain of
successive one-step reducts below it. -/
def IsStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Prop :=
  Acc StepSuccessor sourceTerm

/-- Strong normalization for the v2 raw `Step` relation at every scope. -/
def HasStrongNormalization : Prop :=
  ∀ {scope : Nat} (sourceTerm : RawTerm scope),
    IsStronglyNormalizing sourceTerm

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

/-- Newman's lift from local one-step confluence plus accessibility to
global Church-Rosser, specialized to the v2 raw `Step` relation.

This is the honest SN route for M8: M7 supplies local joins, while a future
SN theorem supplies `IsStronglyNormalizing sourceTerm`. -/
theorem confluence_of_localJoin_and_accessible {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (sourceTerminates : IsStronglyNormalizing sourceTerm)
    (leftChain : StepStar sourceTerm leftReduct)
    (rightChain : StepStar sourceTerm rightReduct) :
    Join leftReduct rightReduct := by
  exact
    (Acc.ndrec
      (r := StepSuccessor)
      (C := fun currentTerm =>
        ∀ {leftReduct rightReduct : RawTerm scope},
          StepStar currentTerm leftReduct →
          StepStar currentTerm rightReduct →
          Join leftReduct rightReduct)
      (m := fun currentTerm _ currentIH => by
        intro leftReduct rightReduct leftChain rightChain
        cases leftChain with
        | refl _ =>
            exact ⟨rightReduct, rightChain, StepStar.refl _⟩
        | trans leftHeadStep leftTailChain =>
            cases rightChain with
            | refl _ =>
                exact
                  ⟨ leftReduct
                  , StepStar.refl _
                  , StepStar.trans leftHeadStep leftTailChain ⟩
            | trans rightHeadStep rightTailChain =>
                obtain
                  ⟨localReduct, leftHeadToLocal, rightHeadToLocal⟩ :=
                    localJoin_of_cdLemma leftHeadStep rightHeadStep
                obtain
                  ⟨leftCommon, leftTailToCommon, localToLeftCommon⟩ :=
                    currentIH _ leftHeadStep leftTailChain leftHeadToLocal
                obtain
                  ⟨finalCommon, rightTailToCommon, leftCommonToFinal⟩ :=
                    currentIH _ rightHeadStep rightTailChain
                      (StepStar.trans_compose rightHeadToLocal
                        localToLeftCommon)
                exact
                  ⟨ finalCommon
                  , StepStar.trans_compose leftTailToCommon leftCommonToFinal
                  , rightTailToCommon ⟩)
      sourceTerminates)
      leftChain
      rightChain

/-- Strong normalization plus M7's local join theorem gives global
Church-Rosser. -/
theorem confluence_of_strongNormalization
    (hasStrongNormalization : HasStrongNormalization) :
    HasConfluence := by
  intro scope sourceTerm leftReduct rightReduct leftChain rightChain
  exact
    confluence_of_localJoin_and_accessible
      (hasStrongNormalization sourceTerm)
      leftChain
      rightChain

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

/-- Raw conversion transitivity follows from strong normalization plus M7's
local join theorem. -/
theorem trans_of_strongNormalization
    (hasStrongNormalization : StepStar.HasStrongNormalization)
    {scope : Nat} {firstTerm middleTerm lastTerm : RawTerm scope}
    (firstMiddle : Conv firstTerm middleTerm)
    (middleLast : Conv middleTerm lastTerm) :
    Conv firstTerm lastTerm :=
  trans_of_confluence
    (StepStar.confluence_of_strongNormalization hasStrongNormalization)
    firstMiddle middleLast

end Conv

end LeanFX2.Foundation.PolyCell.Core
