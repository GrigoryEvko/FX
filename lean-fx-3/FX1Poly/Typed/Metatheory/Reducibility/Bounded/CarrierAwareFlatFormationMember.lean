import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedCarrierAwareArm
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CumulativeFreeLevelsSupport

/-! # FX1Poly/Typed/CarrierAwareFlatFormationMember
    — the generic carrier-aware flat formation FT member (product / either / equiv) (TYTAB-4 step 4)

The cumulative members (`fundamentalCumulative{Pi,Sigma}MemberAtBoundedSucc`) discharge the binder-crossing
dependent formers.  This file discharges the CARRIER-AWARE flat formers — product / either / equiv — in ONE generic
theorem over the 3-tag `CarrierCombinator` (the bounded twin of the denote-layer
`carrierAwareFormerFundamentalFromCarriers`).  These formers are NON-dependent (both children typed at `context`,
no binder crossing), so there is no telescope re-assembly; the member is built directly through
`universeMembershipIntroAtBounded`.

## The construction

From the two obligation IHs (each a universe MEMBER at its own component level), under any closing substitution:

  * the component bounds `denote firstLevel env < bound` / `… secondLevel …` come off each member's candidate
    (`universeCodeReducibleAtBounded_belowBound`);
  * each component's SN (`stronglyNormalizing_of_universeMemberAtBounded`) and reducible-as-type at its OWN decoded
    level (`universeMemberReducibleAsTypeAtDecodedLevelBounded`) are projected;
  * each component's reducible-as-type is lifted to the JOIN level `denote (lmaxAll [firstLevel, secondLevel]) env`
    by free bounded cumulativity (`isReducibleBounded_cumulative` + `levelMax_le_left` / `levelMax_le_right`);
  * the carrier-aware builder `carrierAwareReducibleAtLevelFromComponentsBounded` assembles the two lifted
    reducibilities into the cell's reducibility-as-type at the join level;
  * `CarrierCombinator.cell_isStronglyNormalizing_of_carriers` gives the cell's SN from the components' SN;
  * `universeMembershipIntroAtBounded` re-packages everything at `Type@(lmaxAll [firstLevel, secondLevel])` (the
    output bound `denote (lmaxAll …) env < bound` is `levelMax_lt` of the two component bounds).

## Zero-axiom verification

`subst_universeCodeCell` / `CarrierCombinator.cell_subst` rewrites + the shipped universe-member projections /
cumulativity lift / carrier-aware builder + elementary `levelMax` bounds.  No induction, no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The generic carrier-aware flat formation FT member (TYTAB-4 step 4).**  From the first/second obligation IHs
(each a universe member at its component level), `combinator.cell firstCode secondCode` (product / either / equiv) is
a bound-reducible member of `Type@(lmaxAll [firstLevel, secondLevel])` under any closing substitution.  The
non-dependent flat twin of `fundamentalCumulativePiMemberAtBoundedSucc`: built directly (no telescope) by lifting
both components to the join level and assembling via the carrier-aware builder. -/
theorem fundamentalCarrierAwareFlatMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (combinator : CarrierCombinator) (firstLevel secondLevel : LevelExpr) (flag : UniverseFlag)
    {firstCode secondCode : RawTerm scope}
    (firstFundamental :
      FundamentalConclusionAtBoundedSucc env bound context firstCode (universeCodeCell firstLevel flag))
    (secondFundamental :
      FundamentalConclusionAtBoundedSucc env bound context secondCode (universeCodeCell secondLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context (combinator.cell firstCode secondCode)
      (universeCodeCell (lmaxAll [firstLevel, secondLevel]) flag) := by
  intro _targetScope substitution envReducible
  have firstMember := firstFundamental substitution envReducible
  rw [subst_universeCodeCell] at firstMember
  have secondMember := secondFundamental substitution envReducible
  rw [subst_universeCodeCell] at secondMember
  have firstBelowBound : LevelExpr.denote firstLevel env < bound := by
    obtain ⟨_firstCand, firstCandReducible, _firstIn⟩ := firstMember
    exact universeCodeReducibleAtBounded_belowBound firstCandReducible
  have secondBelowBound : LevelExpr.denote secondLevel env < bound := by
    obtain ⟨_secondCand, secondCandReducible, _secondIn⟩ := secondMember
    exact universeCodeReducibleAtBounded_belowBound secondCandReducible
  have firstSN : IsStronglyNormalizing (RawTerm.subst substitution firstCode) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound firstLevel flag _ firstBelowBound firstMember
  have secondSN : IsStronglyNormalizing (RawTerm.subst substitution secondCode) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound secondLevel flag _ secondBelowBound secondMember
  have firstReducibleAtFirst :
      IsReducibleTypeAtBounded env (LevelExpr.denote firstLevel env) (RawTerm.subst substitution firstCode) :=
    universeMemberReducibleAsTypeAtDecodedLevelBounded firstMember firstBelowBound
  have secondReducibleAtSecond :
      IsReducibleTypeAtBounded env (LevelExpr.denote secondLevel env) (RawTerm.subst substitution secondCode) :=
    universeMemberReducibleAsTypeAtDecodedLevelBounded secondMember secondBelowBound
  have firstReducibleAtJoin :
      IsReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [firstLevel, secondLevel]) env)
        (RawTerm.subst substitution firstCode) := by
    refine isReducibleBounded_cumulative firstReducibleAtFirst ?_
    rw [lmaxAll_pair, LevelExpr.denote_lmax]
    exact levelMax_le_left _ _
  have secondReducibleAtJoin :
      IsReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [firstLevel, secondLevel]) env)
        (RawTerm.subst substitution secondCode) := by
    refine isReducibleBounded_cumulative secondReducibleAtSecond ?_
    rw [lmaxAll_pair, LevelExpr.denote_lmax]
    exact levelMax_le_right _ _
  have cellReducibleAtJoin :
      IsReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [firstLevel, secondLevel]) env)
        (combinator.cell (RawTerm.subst substitution firstCode) (RawTerm.subst substitution secondCode)) :=
    carrierAwareReducibleAtLevelFromComponentsBounded env
      (LevelExpr.denote (lmaxAll [firstLevel, secondLevel]) env) combinator
      firstReducibleAtJoin secondReducibleAtJoin
  have outputBelowBound : LevelExpr.denote (lmaxAll [firstLevel, secondLevel]) env < bound := by
    rw [lmaxAll_pair, LevelExpr.denote_lmax]
    exact levelMax_lt firstBelowBound secondBelowBound
  have cellSN :
      IsStronglyNormalizing
        (combinator.cell (RawTerm.subst substitution firstCode) (RawTerm.subst substitution secondCode)) :=
    CarrierCombinator.cell_isStronglyNormalizing_of_carriers combinator firstSN secondSN
  rw [subst_universeCodeCell, CarrierCombinator.cell_subst]
  exact universeMembershipIntroAtBounded env (lmaxAll [firstLevel, secondLevel]) flag bound
    (combinator.cell (RawTerm.subst substitution firstCode) (RawTerm.subst substitution secondCode))
    outputBelowBound cellSN cellReducibleAtJoin

end FX1Poly.Typed
