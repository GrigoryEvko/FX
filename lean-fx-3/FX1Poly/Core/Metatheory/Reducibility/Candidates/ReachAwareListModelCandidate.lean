import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareListCandidate

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

end FX1Poly.Core
