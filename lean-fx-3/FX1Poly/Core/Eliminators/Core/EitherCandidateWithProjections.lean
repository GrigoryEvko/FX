import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareEitherCandidate
import FX1Poly.Core.Eliminators.Core.OptionEitherProjectionMembers

/-! # FX1Poly/Core/EitherCandidateWithProjections
    — the full coproduct candidate: carrier-aware injection canonicity AND forward-closure projection membership

The either analogue of `pairCandidateWithProjections` (sibling product file).  `carrierAwareEitherCandidate`
(the `dataTaitCandidate` at the carrier-aware injection predicate) records payload reducibility only at the
NORMAL payload of a reached injection — enough for the constructor / canonicity side, but NOT enough for the
native `eitherMatch` elimination fundamental-theorem row, which needs `firstCandidate payload` whenever the
scrutinee reaches `eitherInl payload` at an ARBITRARY (possibly non-normal) payload (the left-ι fires the left
branch at any inl head), and symmetrically `secondCandidate payload` at a reached `eitherInr payload`.  The weak
normal-form record cannot supply that without full backward closure (= Conv-closure), which no Girard candidate
has.

The two projection clauses (`eitherProjectionMembers` for inl / `eitherProjectionMembersRight` for inr, sibling
`OptionEitherProjectionMembers` file) supply precisely those missing facts by FORWARD closure through the
CONSTRUCTED projector `eitherProject` / `eitherProjectRight`.  This file conjoins the three into the genuine
coproduct reducibility candidate

  `eitherCandidateWithProjections firstC secondC
     := carrierAwareEitherCandidate firstC secondC ∧ eitherProjectionMembers firstC ∧ eitherProjectionMembersRight secondC`

which carries BOTH the carrier-aware normal-injection value structure AND the reached-injection payload residue
resolvers at arbitrary payloads (`*_componentOfReachesInl` / `*_componentOfReachesInr`), with NO backward
closure.  The conjunction is itself a Girard reducibility candidate (CR1 from the carrier-aware conjunct, CR2 /
CR3 conjoined three-way) and is β-spine head-expansion-closed and general-member-weak-head-expansion-closed
given the carriers' general weak-head expansion — the carrier-aware conjunct's closures are unconditional
(`dataTaitCandidate`), the projection conjuncts' closures are `eitherProjectionMembers{,Right}_headExpansionClosed`
/ `_memberWeakHeadExpansion`.  At the Typed denote level both carrier general-WHE hypotheses are supplied
STANDALONE by `ReducibleTypeAtBounded.memberWeakHeadExpansion`, so the conjoined candidate is exactly the object
the `dataFlat` coproduct arm should denote to discharge the native `eitherMatch` reach residues.

LAYERING NOTE: unlike `pairCandidateWithProjections` (Candidates/, built on the built-in `fst`/`snd` projections),
the either projection clauses ride the CONSTRUCTED `eitherProject` (which needs the match-eliminator neutrality /
SN lemmas in `Eliminators/`), so this conjoined object lives one layer ABOVE `CarrierCombinatorTable`
(Candidates/).  Wiring `assemble coproductLike` to this object therefore requires resolving that layer gap (move
the projection-clause layer down, or a coproduct-specific assemble variant at this layer) — a flip-wiring concern
tracked separately; this file ships the proven candidate object.

## Zero-axiom verification

Each property is a componentwise pairing of the three conjuncts' shipped properties.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The full coproduct reducibility candidate.**  The conjunction of the carrier-aware normal-injection
candidate with the two forward-closure projection clauses (inl carries `firstCandidate`, inr carries
`secondCandidate`): a term is a member when it is a carrier-aware coproduct member AND both injection
projections are reducible.  Carries both the canonicity structure (normal-injection values) and the
match-eliminator behaviour (payload membership at any reached injection). -/
def eitherCandidateWithProjections {scope : Nat}
    (firstCandidate secondCandidate : RawTerm scope → Prop) (term : RawTerm scope) : Prop :=
  carrierAwareEitherCandidate firstCandidate secondCandidate term ∧
    eitherProjectionMembers firstCandidate term ∧
    eitherProjectionMembersRight secondCandidate term

/-- **★ The full coproduct candidate is a Girard reducibility candidate.**  CR1 is the carrier-aware conjunct's
strong normalization; CR2 and CR3 triple the three conjuncts' closures — forward closure carries each conjunct,
and neutral expansion feeds each conjunct the corresponding component of the reducts' membership. -/
theorem eitherCandidateWithProjections_isReducibilityCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    (secondIsCandidate : IsReducibilityCandidate secondCandidate) :
    IsReducibilityCandidate (eitherCandidateWithProjections firstCandidate secondCandidate) where
  stronglyNormalizing := fun members =>
    (carrierAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate).stronglyNormalizing
      members.1
  closedUnderStep := fun members step =>
    ⟨(carrierAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate).closedUnderStep
       members.1 step,
     (eitherProjectionMembers_isReducibilityCandidate firstIsCandidate).closedUnderStep members.2.1 step,
     (eitherProjectionMembersRight_isReducibilityCandidate secondIsCandidate).closedUnderStep members.2.2 step⟩
  neutralExpansion := fun neutral reductsMembers =>
    ⟨(carrierAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate).neutralExpansion
       neutral (fun reduct step => (reductsMembers reduct step).1),
     (eitherProjectionMembers_isReducibilityCandidate firstIsCandidate).neutralExpansion
       neutral (fun reduct step => (reductsMembers reduct step).2.1),
     (eitherProjectionMembersRight_isReducibilityCandidate secondIsCandidate).neutralExpansion
       neutral (fun reduct step => (reductsMembers reduct step).2.2)⟩

/-- **★ The full coproduct candidate is β-spine head-expansion-closed** (the Π-codomain-ready property), given
ONLY the carriers' general weak-head expansion — NO carrier reducibility candidacy or SN-extraction.  The
carrier-aware conjunct closes unconditionally (`carrierAwareEitherCandidate_headExpansionClosed`) AND supplies the
β-spine redex's source SN for free (its unconditional CR1 gives `SN contractum`, lifted by
`betaSpineHeadExpansion`); both projection conjuncts then close by
`eitherProjectionMembers{,Right}_memberWeakHeadExpansion` at `WeakHeadStep.betaSpine` fed that source SN,
consuming only the carriers' WHE.  Dropping the carrier-SN requirement is what lets the `assemble`-flip discharge
this at the SCOPE-0 denote head-expansion arm (carrier WHE is scope-general; carrier CR1 is scope+1-bound). -/
theorem eitherCandidateWithProjections_headExpansionClosed {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → firstCandidate contractum →
        IsStronglyNormalizing redex → firstCandidate redex)
    (secondHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → secondCandidate contractum →
        IsStronglyNormalizing redex → secondCandidate redex) :
    HeadExpansionClosed (eitherCandidateWithProjections firstCandidate secondCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  have sourceStronglyNormalizing := betaSpineHeadExpansion domainAnnSN argumentSN
    ((carrierAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate).stronglyNormalizing
      contractumMember.1)
  exact ⟨carrierAwareEitherCandidate_headExpansionClosed firstCandidate secondCandidate
      domainAnnSN argumentSN contractumMember.1,
    eitherProjectionMembers_memberWeakHeadExpansion firstHeadExpand WeakHeadStep.betaSpine
      sourceStronglyNormalizing contractumMember.2.1,
    eitherProjectionMembersRight_memberWeakHeadExpansion secondHeadExpand WeakHeadStep.betaSpine
      sourceStronglyNormalizing contractumMember.2.2⟩

/-- **★ The full coproduct candidate is closed under GENERAL member weak-head expansion** (the saturated-set
property the denote layer's `memberWeakHeadExpansion` consumer needs).  The carrier-aware conjunct closes by
`dataTaitCandidate_memberWeakHeadExpansion` (unconditional — `carrierAwareEitherCandidate` IS a
`dataTaitCandidate`); the projection conjuncts close by `eitherProjectionMembers{,Right}_memberWeakHeadExpansion`,
each consuming its carrier's general weak-head expansion.  The three closures are tupled componentwise on the
same weak-head step. -/
theorem eitherCandidateWithProjections_memberWeakHeadExpansion {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → firstCandidate contractum →
        IsStronglyNormalizing redex → firstCandidate redex)
    (secondHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → secondCandidate contractum →
        IsStronglyNormalizing redex → secondCandidate redex)
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : eitherCandidateWithProjections firstCandidate secondCandidate reduct) :
    eitherCandidateWithProjections firstCandidate secondCandidate source :=
  ⟨dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing reductMember.1,
   eitherProjectionMembers_memberWeakHeadExpansion firstHeadExpand weakHeadStep sourceStronglyNormalizing
     reductMember.2.1,
   eitherProjectionMembersRight_memberWeakHeadExpansion secondHeadExpand weakHeadStep sourceStronglyNormalizing
     reductMember.2.2⟩

/-- **★ The full coproduct candidate is forward-closed under one `Step`, LEG-FREE** (needs only the carriers'
forward-star closure, NOT full reducibility candidacy).  The coproduct twin of
`pairCandidateWithProjections_closedUnderStep`: the closure the type-denote `memberForwardClosed` consumer
needs post-flip, where the carrier induction hypothesis is exactly CR2 (forward-star closure), so a
full-candidacy requirement would be unsatisfiable.  The carrier-aware conjunct closes by
`dataTaitCandidate.closedUnderStep` (unconditional — `carrierAwareEitherCandidate` IS a `dataTaitCandidate`);
the two projection conjuncts by the (CR2-only) `eitherProjectionMembers{,Right}_closedUnderStep`. -/
theorem eitherCandidateWithProjections_closedUnderStep {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstForwardStar : ∀ {origin destination : RawTerm scope},
        StepStar origin destination → firstCandidate origin → firstCandidate destination)
    (secondForwardStar : ∀ {origin destination : RawTerm scope},
        StepStar origin destination → secondCandidate origin → secondCandidate destination)
    {term reduct : RawTerm scope}
    (members : eitherCandidateWithProjections firstCandidate secondCandidate term) (step : Step term reduct) :
    eitherCandidateWithProjections firstCandidate secondCandidate reduct :=
  ⟨dataTaitCandidate.closedUnderStep members.1 step,
   eitherProjectionMembers_closedUnderStep firstForwardStar members.2.1 step,
   eitherProjectionMembersRight_closedUnderStep secondForwardStar members.2.2 step⟩

/-- **★ Reached-`inl` payload membership — the residue resolver.**  Projects the inl projection conjunct and
applies its forward-closure resolver: when a member reaches `eitherInl value`, the payload is a `firstCandidate`
member at an ARBITRARY (possibly non-normal) `value`.  The exact discharge the native `eitherMatch` elim FT
row's `leftBranchMemberIfReachesInl` residue needs. -/
theorem eitherCandidateWithProjections_componentOfReachesInl {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    {term value : RawTerm scope}
    (members : eitherCandidateWithProjections firstCandidate secondCandidate term)
    (reachesInl : StepStar term (.mkGen .gen_eitherInl () (.childCons value .childNil))) :
    firstCandidate value :=
  eitherProjectionMembers_componentOfReachesInl firstIsCandidate members.2.1 reachesInl

/-- **★ Reached-`inr` payload membership — the residue resolver.**  Symmetric to the inl resolver over the inr
projection conjunct, discharging the native `eitherMatch` elim FT row's `rightBranchMemberIfReachesInr` residue. -/
theorem eitherCandidateWithProjections_componentOfReachesInr {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (secondIsCandidate : IsReducibilityCandidate secondCandidate)
    {term value : RawTerm scope}
    (members : eitherCandidateWithProjections firstCandidate secondCandidate term)
    (reachesInr : StepStar term (.mkGen .gen_eitherInr () (.childCons value .childNil))) :
    secondCandidate value :=
  eitherProjectionMembersRight_componentOfReachesInr secondIsCandidate members.2.2 reachesInr

/-- **The full coproduct member is a (weak) `dataTaitCandidate isEitherValue` member.**  Projects the
carrier-aware conjunct and forgets the projection clauses — the refinement the content-free flat-coproduct
candidate's consumers still accept. -/
theorem eitherCandidateWithProjections_toWeakEitherCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : eitherCandidateWithProjections firstCandidate secondCandidate term) :
    dataTaitCandidate isEitherValue term :=
  carrierAwareEitherCandidate_toWeakEitherCandidate member.1

/-- **★ The full coproduct candidate is congruent in its carriers.**  Pointwise-equivalent carriers yield
pointwise-equivalent full coproduct candidates — all three conjuncts swap under the carrier-aware congruence and
the two projection-clause congruences respectively.  The determinism finisher the `dataFlat` coproduct arm
consumes. -/
theorem eitherCandidateWithProjections_congr {scope : Nat}
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (eitherCandidateWithProjections firstCandidate1 secondCandidate1)
      (eitherCandidateWithProjections firstCandidate2 secondCandidate2) := by
  intro term
  constructor
  · rintro ⟨carrierAwareMember, inlMember, inrMember⟩
    exact ⟨(carrierAwareEitherCandidate_congr firstIff secondIff term).mp carrierAwareMember,
      (eitherProjectionMembers_congr firstIff term).mp inlMember,
      (eitherProjectionMembersRight_congr secondIff term).mp inrMember⟩
  · rintro ⟨carrierAwareMember, inlMember, inrMember⟩
    exact ⟨(carrierAwareEitherCandidate_congr firstIff secondIff term).mpr carrierAwareMember,
      (eitherProjectionMembers_congr firstIff term).mpr inlMember,
      (eitherProjectionMembersRight_congr secondIff term).mpr inrMember⟩

end FX1Poly.Core
