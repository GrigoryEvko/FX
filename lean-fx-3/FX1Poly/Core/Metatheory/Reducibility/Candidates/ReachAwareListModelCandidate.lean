import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareListCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.EitherMatchCandidate
import FX1Poly.Core.Metatheory.Canonicity.CarrierAwareReducibleComponentMembers

/-! # FX1Poly/Core/ReachAwareListModelCandidate
    — the reach-aware LIST candidate: the RECURSIVE Ω-fork-free list model candidate (GATE1-SWAP4 substrate)

`carrierAwareListCandidate` (`CarrierAwareListCandidate.lean`) records the cons head's carrier membership at every
reachable NORMAL FORM.  The dependent `listElim` engine needs more: at every REACHED `cons head tail` (not merely
the normal form) it must read off `head ∈ ⟦A⟧` (for the cons-branch's head Π argument) AND `tail ∈ ⟦List A⟧` (for
the cons-branch's tail Π argument).  This file strengthens the carrier-aware candidate with forward-closed reach
clauses recording exactly that — the list twin of `reachAwareOptionCandidate`, but RECURSIVE: the tail's
reach-aware membership is itself a `reachAwareListCandidate` member.

It is the FIRST recursive reducibility candidate in the kernel.  The recursion is tamed by carrying the recursive
member in the CONCLUSION of a reach clause (a `→`-codomain, strictly-positive position), so CR1/CR2/CR3 mirror the
option twin's argument VERBATIM — the recursive member is supplied by the clause, never re-derived.

## The reach clause as a self-referential inductive

`IsReachAwareListMember carrierCandidate term` holds when `term` is a carrier-aware list member, every reached
`cons head tail` records `carrierCandidate head` (`reachHead`), AND every reached `cons head tail` records
`IsReachAwareListMember carrierCandidate tail` (`reachTail`).  The recursive occurrence in `reachTail` sits in the
CODOMAIN of `∀ head tail, StepStar … →` — strictly positive and UNNESTED (kept out of the `∧` that nested it,
which Lean rejects as a nested-inductive parameter with a local variable).

## Zero-axiom verification

CR1 rides the carrier-aware conjunct's SN; CR2 forward because the reached-`cons` clauses only lose reached
injections under reduction (`term ↝ reduct` prepends a step to any `reduct ↝* cons`); CR3 because a neutral term is
never `listCons` (`isNeutral_rootGenerator_ne_listCons`) so any `term ↝* cons` factors through a first step into a
reduct already carrying the clauses.  Exactly the option twin's argument, recursion carried through `reachTail`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **The reach-aware list membership** — the RECURSIVE Ω-fork-free list model candidate.  `term` is a
carrier-aware list member, every reached `cons head tail` records the head's carrier membership (`reachHead`), and
every reached `cons head tail` records the tail's recursive reach-aware membership (`reachTail`).  The list twin of
`reachAwareOptionCandidate`, with the recursive `reachTail` clause replacing option's single `some` payload clause.
The two reach clauses are kept SEPARATE (not `∧`-joined) so the recursive `reachTail` occurrence is an unnested
`→`-codomain, which Lean's strict-positivity checker accepts. -/
inductive IsReachAwareListMember {scope : Nat} (carrierCandidate : RawTerm scope → Prop) :
    RawTerm scope → Prop where
  | mk {term : RawTerm scope}
      (carrierAware : carrierAwareListCandidate carrierCandidate term)
      (reachHead : ∀ head tail : RawTerm scope,
        StepStar term (listConsCell head tail) → carrierCandidate head)
      (reachTail : ∀ head tail : RawTerm scope,
        StepStar term (listConsCell head tail) → IsReachAwareListMember carrierCandidate tail) :
      IsReachAwareListMember carrierCandidate term

/-- **The reach-aware list candidate** — the strengthened recursive list model candidate (`assembleModel`'s
`listLike` target). -/
def reachAwareListCandidate {scope : Nat} (carrierCandidate : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  IsReachAwareListMember carrierCandidate term

/-- **The carrier-aware conjunct of a reach-aware list member.**  Definitional projection. -/
theorem reachAwareListCandidate.carrierAwareConjunct {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : reachAwareListCandidate carrierCandidate term) :
    carrierAwareListCandidate carrierCandidate term := by
  cases member with
  | mk carrierAware _ _ => exact carrierAware

/-- **★ The reach-aware list reach-projection (HEAD) — the Ω-fork-free `listElim` cons head-residue content.**  A
reach-aware member that reaches `listConsCell head tail` yields the head's carrier membership at the LITERAL
reached head, for ANY carrier.  Definitional.  The cons-head twin of
`reachAwareOptionCandidate.reachableSomeMember`. -/
theorem reachAwareListCandidate.reachableConsHeadMember {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {source head tail : RawTerm scope}
    (member : reachAwareListCandidate carrierCandidate source)
    (reaches : StepStar source (listConsCell head tail)) :
    carrierCandidate head := by
  cases member with
  | mk _ reachHead _ => exact reachHead head tail reaches

/-- **★ The reach-aware list reach-projection (TAIL) — the recursive `listElim` cons tail-residue content.**  A
reach-aware member that reaches `listConsCell head tail` yields the tail's RECURSIVE reach-aware membership at the
LITERAL reached tail.  The recursive clause the cons-branch's tail Π argument consumes — the content option's
non-recursive `some` clause has no analogue of. -/
theorem reachAwareListCandidate.reachableConsTailMember {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {source head tail : RawTerm scope}
    (member : reachAwareListCandidate carrierCandidate source)
    (reaches : StepStar source (listConsCell head tail)) :
    reachAwareListCandidate carrierCandidate tail := by
  cases member with
  | mk _ _ reachTail => exact reachTail head tail reaches

/-- **The reach-aware list candidate is a reducibility candidate.**  CR1 rides the carrier-aware member's SN; CR2
forward because the reached-`cons` clauses only lose reached injections under reduction; CR3 because a neutral term
is never `listCons` so any `term ↝* cons` factors through a first step into a reduct already carrying the clauses.
Exactly the option twin's argument, with the recursive `reachTail` clause carried through unchanged. -/
theorem reachAwareListCandidate_isReducibilityCandidate {scope : Nat}
    (carrierCandidate : RawTerm scope → Prop) :
    IsReducibilityCandidate (reachAwareListCandidate carrierCandidate) := by
  refine ⟨?stronglyNormalizing, ?closedUnderStep, ?neutralExpansion⟩
  case stronglyNormalizing =>
    intro term member
    exact (carrierAwareListCandidate_isReducibilityCandidate carrierCandidate).stronglyNormalizing
      member.carrierAwareConjunct
  case closedUnderStep =>
    intro term reduct member step
    refine IsReachAwareListMember.mk
      ((carrierAwareListCandidate_isReducibilityCandidate carrierCandidate).closedUnderStep
        member.carrierAwareConjunct step) ?reachHead ?reachTail
    case reachHead =>
      intro head tail reaches
      exact member.reachableConsHeadMember (StepStar.trans step reaches)
    case reachTail =>
      intro head tail reaches
      exact member.reachableConsTailMember (StepStar.trans step reaches)
  case neutralExpansion =>
    intro term neutralTerm reductsMembers
    refine IsReachAwareListMember.mk
      ((carrierAwareListCandidate_isReducibilityCandidate carrierCandidate).neutralExpansion
        neutralTerm (fun reduct step => (reductsMembers reduct step).carrierAwareConjunct))
      ?reachHead ?reachTail
    case reachHead =>
      intro head tail reaches
      cases reaches with
      | refl => exact absurd rfl (isNeutral_rootGenerator_ne_listCons neutralTerm)
      | trans firstStep restChain =>
          exact (reductsMembers _ firstStep).reachableConsHeadMember restChain
    case reachTail =>
      intro head tail reaches
      cases reaches with
      | refl => exact absurd rfl (isNeutral_rootGenerator_ne_listCons neutralTerm)
      | trans firstStep restChain =>
          exact (reductsMembers _ firstStep).reachableConsTailMember restChain

/-- **A reach-aware list member is a (weak) `dataTaitCandidate IsListStructured` member.**  The carrier-aware
conjunct forgets to the content-free flat-list candidate via `carrierAwareListCandidate_toWeakListCandidate` — the
scrutinee bridge the dependent `listElim` engine consumes.  Preserves the existing eliminator engine. -/
theorem reachAwareListCandidate_toWeakListCandidate {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {term : RawTerm scope}
    (member : reachAwareListCandidate carrierCandidate term) :
    dataTaitCandidate IsListStructured term :=
  carrierAwareListCandidate_toWeakListCandidate member.carrierAwareConjunct

/-- **A no-drift weak-head strip to a reached `cons` injection.**  A `cons` cell admits no weak-head step
(`WeakHeadStep.not_from_listCons`), so it is the `weakHeadStripToNormal` instance — the list twin of
`weakHeadStripToReachedSome`.  A `source` reach to `listConsCell head tail` strips across a weak-head step
`source ↝ʰ reduct` to a `reduct` reach at the SAME `head`/`tail`. -/
theorem weakHeadStripToReachedCons {scope : Nat} {source reduct head tail : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (reaches : StepStar source (listConsCell head tail)) :
    StepStar reduct (listConsCell head tail) :=
  weakHeadStripToNormal weakHeadStep reaches (fun _ => WeakHeadStep.not_from_listCons)

/-- **★ The reach-aware list candidate is closed under member weak-head expansion.**  For any `WeakHeadStep source
reduct` with `source` strongly normalizing and `reduct` a reach-aware member, `source` is a reach-aware member.
The carrier-aware conjunct lifts by `dataTaitCandidate_memberWeakHeadExpansion`; the reach clauses lift by the
NO-DRIFT strip (`weakHeadStripToReachedCons`): a `source` reach to `cons head tail` strips across the weak-head
step to a `reduct` reach at the SAME head/tail, whence the reduct's clauses supply the carrier head membership and
the recursive tail membership.  The recursive twin of `reachAwareOptionCandidate_memberWeakHeadExpansion`. -/
theorem reachAwareListCandidate_memberWeakHeadExpansion {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : reachAwareListCandidate carrierCandidate reduct) :
    reachAwareListCandidate carrierCandidate source := by
  refine IsReachAwareListMember.mk
    (dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing
      reductMember.carrierAwareConjunct) ?reachHead ?reachTail
  case reachHead =>
    intro head tail sourceReaches
    exact reductMember.reachableConsHeadMember (weakHeadStripToReachedCons weakHeadStep sourceReaches)
  case reachTail =>
    intro head tail sourceReaches
    exact reductMember.reachableConsTailMember (weakHeadStripToReachedCons weakHeadStep sourceReaches)

/-- **★★★ THE CRUX: the reach-aware list candidate is APP-SPINE head-expansion-closed.**  A spined β-redex
inherits membership from its contractum — `HeadExpansionClosed`.  A β-redex weak-head-steps to its contractum
(`WeakHeadStep.betaSpine`), so head-expansion closure is the DERIVED special case of member weak-head expansion at
that step, with the redex SN supplied by `betaSpineHeadExpansion` from the contractum SN (the carrier-aware
conjunct's CR1).  The recursive twin of `reachAwareOptionCandidate_headExpansionClosed`. -/
theorem reachAwareListCandidate_headExpansionClosed {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} :
    HeadExpansionClosed (reachAwareListCandidate carrierCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  have contractumStronglyNormalizing : IsStronglyNormalizing
      (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) :=
    (carrierAwareListCandidate_isReducibilityCandidate carrierCandidate).stronglyNormalizing
      contractumMember.carrierAwareConjunct
  exact reachAwareListCandidate_memberWeakHeadExpansion WeakHeadStep.betaSpine
    (betaSpineHeadExpansion domainAnnSN argumentSN contractumStronglyNormalizing) contractumMember

/-- **The reach-aware list candidate is forward-closed under one `Step`** (member CR2) — surfaced from the
candidacy bundle for the model interface's `closedUnderStep` dispatch. -/
theorem reachAwareListCandidate_closedUnderStep {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {term reduct : RawTerm scope}
    (member : reachAwareListCandidate carrierCandidate term) (step : Step term reduct) :
    reachAwareListCandidate carrierCandidate reduct :=
  (reachAwareListCandidate_isReducibilityCandidate carrierCandidate).closedUnderStep member step

/-- **The reach-aware list candidate is forward-closed under a whole reduction chain** (member CR2 iterated) — the
recursive `listElim` engine threads it to propagate the scrutinee's reach-aware membership to every reached focus
and structured value (the dependent-recursor re-key's forward-closure leg).  Iterates `closedUnderStep`. -/
theorem reachAwareListCandidate_closedUnderStepStar {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} {term reduct : RawTerm scope}
    (member : reachAwareListCandidate carrierCandidate term) (chain : StepStar term reduct) :
    reachAwareListCandidate carrierCandidate reduct :=
  (reachAwareListCandidate_isReducibilityCandidate carrierCandidate).closedUnderStepStar chain member

/-- **The `nil` cell is a reach-aware list member** for ANY carrier.  The carrier-aware conjunct is the carrier-aware
`nil` intro; the reach clauses are VACUOUS — `nil` is a normal form that never reduces to a `listCons` cell
(`StepStar.eq_of_noStep` forces the reach target back to `nil`, contradicting the `listCons` head via
`Generator.noConfusion`).  The reach-aware nil-branch SN supplier the recursive `listElim` engine reads. -/
theorem reachAwareListCandidate_memberOfNormalNil {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop} :
    reachAwareListCandidate carrierCandidate (listNilCell (scope := scope)) := by
  refine IsReachAwareListMember.mk (carrierAwareListCandidate.memberOfNormalNil rfl) ?reachHead ?reachTail
  case reachHead =>
    intro head tail reaches
    have consEqualsNil : listConsCell head tail = listNilCell :=
      StepStar.eq_of_noStep
        (fun reduct step =>
          RawTerm.isStepNormalForm_blocks_step
            (show RawTerm.isStepNormalForm (listNilCell (scope := scope)) from rfl) reduct step)
        reaches
    exact Generator.noConfusion (congrArg RawTerm.rootGenerator consEqualsNil)
  case reachTail =>
    intro head tail reaches
    have consEqualsNil : listConsCell head tail = listNilCell :=
      StepStar.eq_of_noStep
        (fun reduct step =>
          RawTerm.isStepNormalForm_blocks_step
            (show RawTerm.isStepNormalForm (listNilCell (scope := scope)) from rfl) reduct step)
        reaches
    exact Generator.noConfusion (congrArg RawTerm.rootGenerator consEqualsNil)

/-- **★ The reach-aware list cons introduction — FORWARD construction from a reducible head and a reach-aware tail.**
`cons head tail` is a reach-aware member: the carrier-aware conjunct by `carrierAwareListCandidate.\
memberOfReducibleCons`, and the two reach clauses by forward CR2 — a reached `cons reachedHead reachedTail`
decomposes (`stepStar_under_binaryCell`) into reducts of `head`/`tail`, so `reachedHead` lies in the carrier (CR2
along the head chain) and `reachedTail` is reach-aware (CR2 along the tail chain).  The recursive twin of
`reachAwareOptionCandidate.memberOfReducibleSome`; the intro the `listCons` constructor FT row produces. -/
theorem reachAwareListCandidate.memberOfReducibleCons {scope : Nat}
    {carrierCandidate : RawTerm scope → Prop}
    (carrierCandidateIsCandidate : IsReducibilityCandidate carrierCandidate)
    {head tail : RawTerm scope} (headMember : carrierCandidate head)
    (tailMember : reachAwareListCandidate carrierCandidate tail) :
    reachAwareListCandidate carrierCandidate (listConsCell head tail) := by
  refine IsReachAwareListMember.mk
    (carrierAwareListCandidate.memberOfReducibleCons carrierCandidateIsCandidate headMember
      tailMember.carrierAwareConjunct) ?reachHead ?reachTail
  case reachHead =>
    intro reachedHead reachedTail reaches
    obtain ⟨headAfter, _tailAfter, targetEq, headChain, _tailChain⟩ :=
      stepStar_under_binaryCell listConsCell Step.from_listCons reaches head tail rfl
    injection targetEq with _eqOne _eqTwo _eqThree childrenEq
    injection childrenEq with _scopeEq _shiftEq _restShiftsEq headEq _restEq
    subst headEq
    exact carrierCandidateIsCandidate.closedUnderStepStar headChain headMember
  case reachTail =>
    intro reachedHead reachedTail reaches
    obtain ⟨_headAfter, tailAfter, targetEq, _headChain, tailChain⟩ :=
      stepStar_under_binaryCell listConsCell Step.from_listCons reaches head tail rfl
    injection targetEq with _eqOne _eqTwo _eqThree childrenEq
    injection childrenEq with _scopeEq _shiftEq _restShiftsEq _headEq restEq
    injection restEq with _scopeEqTwo _shiftEqTwo _restShiftsEqTwo tailEq
    subst tailEq
    exact reachAwareListCandidate_closedUnderStepStar tailMember tailChain

/-- **★ The reach-aware list candidate is congruent in its carrier** (the model's `assemble_congr` analogue) — and
RECURSIVELY so.  A pointwise-equivalent carrier yields pointwise-equivalent reach-aware list candidates: the
carrier-aware conjunct transports by `carrierAwareListCandidate_congr`; the `reachHead` clause transports its head
membership by the carrier iff; the `reachTail` clause transports its RECURSIVE tail membership by the induction
hypothesis (the W-type-shaped recursion in the `mk` constructor's `reachTail` premise supplies the IH directly).
Both directions by induction on `IsReachAwareListMember`. -/
theorem reachAwareListCandidate_congr {scope : Nat}
    {carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : PointwiseIff carrierCandidate1 carrierCandidate2) :
    PointwiseIff (reachAwareListCandidate carrierCandidate1)
      (reachAwareListCandidate carrierCandidate2) := by
  have carrierAwareIff := carrierAwareListCandidate_congr carrierIff
  intro term
  constructor
  · intro member
    induction member with
    | mk carrierAware reachHead _reachTail reachTailIH =>
        exact IsReachAwareListMember.mk
          ((carrierAwareIff _).mp carrierAware)
          (fun head tail reaches => (carrierIff head).mp (reachHead head tail reaches))
          (fun head tail reaches => reachTailIH head tail reaches)
  · intro member
    induction member with
    | mk carrierAware reachHead _reachTail reachTailIH =>
        exact IsReachAwareListMember.mk
          ((carrierAwareIff _).mpr carrierAware)
          (fun head tail reaches => (carrierIff head).mpr (reachHead head tail reaches))
          (fun head tail reaches => reachTailIH head tail reaches)

end FX1Poly.Core
