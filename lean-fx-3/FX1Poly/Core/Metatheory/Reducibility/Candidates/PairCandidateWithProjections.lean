import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.SigmaProjectionReducibleMembers

/-! # FX1Poly/Core/PairCandidateWithProjections
    — the full product candidate: normal-pair canonicity AND forward-closure projection membership

`carrierAwarePairCandidate` (the `dataTaitCandidate` at the carrier-aware pair-value predicate) records
component reducibility only at the NORMAL components of a reached pair.  That is exactly enough for the
constructor / canonicity side, but it is NOT enough for the native `fst` / `snd` elimination fundamental-
theorem arms: those need `firstCandidate first` whenever the scrutinee reaches `pairCell first second` at an
ARBITRARY (possibly non-normal) `first`, because the projection ι fires at any pair-constructor head.  The
weak normal-form record cannot supply that without full backward closure (= Conv-closure), which no Girard
candidate has.

`sigmaProjectionMembers` (the projection clause, sibling file) supplies precisely that missing fact by
FORWARD closure: it reads membership off `fstCell` / `sndCell` and carries it across the lifted reduction.
But on its own it does not record the normal-pair value structure the constructor / canonicity side needs.

This file conjoins the two into the genuine product reducibility candidate

  `pairCandidateWithProjections firstCandidate secondCandidate
     := carrierAwarePairCandidate firstCandidate secondCandidate ∧ sigmaProjectionMembers firstCandidate secondCandidate`

which carries BOTH:

  * the carrier-aware normal-pair value structure (`*.memberOfNormalPair`, `*_toWeakPairCandidate`), and
  * the reached-pair component residue resolvers at arbitrary components
    (`*_firstComponentOfReachesPair` / `*_secondComponentOfReachesPair`), with NO backward closure.

The conjunction is itself a Girard reducibility candidate (CR1 from either conjunct, CR2 / CR3 conjoined
componentwise) and is β-spine head-expansion-closed given the carriers' general weak-head expansion — the
carrier-aware conjunct's closure is unconditional (`dataTaitCandidate`), the projection conjunct's closure is
`sigmaProjectionMembers_headExpansionClosed`.  At the Typed denote level both carrier general-WHE hypotheses
are supplied STANDALONE by `ReducibleTypeAtBounded.memberWeakHeadExpansion`, so the conjoined candidate is
exactly the object the `dataFlat` product arm should denote to discharge the native projection elim rows.

## Zero-axiom verification

Each property is a componentwise pairing of the two conjuncts' shipped properties.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The full product reducibility candidate.**  The conjunction of the carrier-aware normal-pair candidate
with the forward-closure projection clause: a term is a member when it is a carrier-aware product member AND
its projections are reducible.  This is the genuine Σ / product candidate — it carries both the canonicity
structure (normal-pair values) and the projection-eliminator behaviour (membership at any reached pair). -/
def pairCandidateWithProjections {scope : Nat}
    (firstCandidate secondCandidate : RawTerm scope → Prop) (term : RawTerm scope) : Prop :=
  carrierAwarePairCandidate firstCandidate secondCandidate term ∧
    sigmaProjectionMembers firstCandidate secondCandidate term

/-- **★ The full product candidate is a Girard reducibility candidate.**  CR1 is the carrier-aware conjunct's
strong normalization; CR2 and CR3 pair the two conjuncts' closures — forward closure carries each conjunct,
and neutral expansion feeds each conjunct the corresponding projection of the reducts' membership. -/
theorem pairCandidateWithProjections_isReducibilityCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    (secondIsCandidate : IsReducibilityCandidate secondCandidate) :
    IsReducibilityCandidate (pairCandidateWithProjections firstCandidate secondCandidate) where
  stronglyNormalizing := fun members =>
    (carrierAwarePairCandidate_isReducibilityCandidate firstCandidate secondCandidate).stronglyNormalizing
      members.1
  closedUnderStep := fun members step =>
    ⟨(carrierAwarePairCandidate_isReducibilityCandidate firstCandidate secondCandidate).closedUnderStep
       members.1 step,
     (sigmaProjectionMembers_isReducibilityCandidate firstIsCandidate secondIsCandidate).closedUnderStep
       members.2 step⟩
  neutralExpansion := fun neutral reductsMembers =>
    ⟨(carrierAwarePairCandidate_isReducibilityCandidate firstCandidate secondCandidate).neutralExpansion
       neutral (fun reduct step => (reductsMembers reduct step).1),
     (sigmaProjectionMembers_isReducibilityCandidate firstIsCandidate secondIsCandidate).neutralExpansion
       neutral (fun reduct step => (reductsMembers reduct step).2)⟩

/-- **★ The full product candidate is β-spine head-expansion-closed** (the Π-codomain-ready property), given
the carriers' general weak-head expansion.  The carrier-aware conjunct closes unconditionally
(`carrierAwarePairCandidate_headExpansionClosed`, an instance of `dataTaitCandidate`); the projection conjunct
closes by `sigmaProjectionMembers_headExpansionClosed`, which consumes the carriers' general weak-head
expansion (supplied standalone at the Typed denote level by `ReducibleTypeAtBounded.memberWeakHeadExpansion`).
The two closures are paired componentwise on the same spined β-redex. -/
theorem pairCandidateWithProjections_headExpansionClosed {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    (firstHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → firstCandidate contractum →
        IsStronglyNormalizing redex → firstCandidate redex)
    (secondHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → secondCandidate contractum →
        IsStronglyNormalizing redex → secondCandidate redex) :
    HeadExpansionClosed (pairCandidateWithProjections firstCandidate secondCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  exact ⟨carrierAwarePairCandidate_headExpansionClosed firstCandidate secondCandidate
      domainAnnSN argumentSN contractumMember.1,
    sigmaProjectionMembers_headExpansionClosed firstIsCandidate firstHeadExpand secondHeadExpand
      domainAnnSN argumentSN contractumMember.2⟩

/-- **The full product candidate's introduction: reducible components give a member at a normal pair.**  The
carrier-aware conjunct is `carrierAwarePairCandidate.memberOfNormalPair`; the projection conjunct is
`sigmaProjectionMembers_ofReducibleComponents`, with the component strong-normalization derived from the
carriers' CR1.  The data-intro shape the dependent-pair constructor FT row produces. -/
theorem pairCandidateWithProjections.memberOfNormalPair {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    (secondIsCandidate : IsReducibilityCandidate secondCandidate)
    (firstHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → firstCandidate contractum →
        IsStronglyNormalizing redex → firstCandidate redex)
    (secondHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → secondCandidate contractum →
        IsStronglyNormalizing redex → secondCandidate redex)
    {first second : RawTerm scope}
    (pairIsNormal : RawTerm.isStepNormalForm (pairCell first second))
    (firstNormal : RawTerm.isStepNormalForm first) (secondNormal : RawTerm.isStepNormalForm second)
    (firstMember : firstCandidate first) (secondMember : secondCandidate second) :
    pairCandidateWithProjections firstCandidate secondCandidate (pairCell first second) :=
  ⟨carrierAwarePairCandidate.memberOfNormalPair pairIsNormal firstNormal secondNormal firstMember secondMember,
   sigmaProjectionMembers_ofReducibleComponents firstHeadExpand secondHeadExpand
     (firstIsCandidate.stronglyNormalizing firstMember) (secondIsCandidate.stronglyNormalizing secondMember)
     firstMember secondMember⟩

/-- **★ Reached-pair FIRST component membership — the residue resolver.**  Projects the projection conjunct
and applies its forward-closure resolver: when a member reaches `pairCell first second`, the first component
is a `firstCandidate` member at an ARBITRARY (possibly non-normal) `first`.  The exact discharge the native
`fst` elim FT row's `firstMemberIfReachesPair` residue needs. -/
theorem pairCandidateWithProjections_firstComponentOfReachesPair {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    {term first second : RawTerm scope}
    (members : pairCandidateWithProjections firstCandidate secondCandidate term)
    (reachesPair : StepStar term (pairCell first second)) :
    firstCandidate first :=
  sigmaProjectionMembers_firstComponentOfReachesPair firstIsCandidate members.2 reachesPair

/-- **★ Reached-pair SECOND component membership — the residue resolver.**  Symmetric to the first-component
resolver, discharging the native `snd` elim FT row's `secondMemberIfReachesPair` residue. -/
theorem pairCandidateWithProjections_secondComponentOfReachesPair {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (secondIsCandidate : IsReducibilityCandidate secondCandidate)
    {term first second : RawTerm scope}
    (members : pairCandidateWithProjections firstCandidate secondCandidate term)
    (reachesPair : StepStar term (pairCell first second)) :
    secondCandidate second :=
  sigmaProjectionMembers_secondComponentOfReachesPair secondIsCandidate members.2 reachesPair

/-- **The full product member is a (weak) `dataTaitCandidate isPairValue` member.**  Projects the carrier-
aware conjunct and forgets the projection clause — the refinement the content-free flat-product candidate's
consumers (`fstDataTaitMember` / `sndDataTaitMember`) still accept. -/
theorem pairCandidateWithProjections_toWeakPairCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : pairCandidateWithProjections firstCandidate secondCandidate term) :
    dataTaitCandidate isPairValue term :=
  carrierAwarePairCandidate_toWeakPairCandidate member.1

/-- **★ The full product candidate is congruent in its carriers.**  Pointwise-equivalent carriers yield
pointwise-equivalent full product candidates — both conjuncts swap under the carrier-aware congruence and the
projection-clause congruence respectively.  The determinism finisher the `dataFlat` product arm consumes. -/
theorem pairCandidateWithProjections_congr {scope : Nat}
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (pairCandidateWithProjections firstCandidate1 secondCandidate1)
      (pairCandidateWithProjections firstCandidate2 secondCandidate2) := by
  intro term
  constructor
  · rintro ⟨carrierAwareMember, projectionMember⟩
    exact ⟨(carrierAwarePairCandidate_congr firstIff secondIff term).mp carrierAwareMember,
      (sigmaProjectionMembers_congr firstIff secondIff term).mp projectionMember⟩
  · rintro ⟨carrierAwareMember, projectionMember⟩
    exact ⟨(carrierAwarePairCandidate_congr firstIff secondIff term).mpr carrierAwareMember,
      (sigmaProjectionMembers_congr firstIff secondIff term).mpr projectionMember⟩

end FX1Poly.Core
