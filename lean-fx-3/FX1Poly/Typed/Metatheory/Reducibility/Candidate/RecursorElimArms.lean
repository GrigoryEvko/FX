import FX1Poly.Typed.Metatheory.Reducibility.Candidate.DataElimArm
import FX1Poly.Core.Eliminators.Recursor.RecursorReducibleScrutineeMember

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/RecursorElimArms
    — the recursive-eliminator FT arms (FTGEN-11): natElim / natRec / listElim

The companion to `DataElimArm` (`twoBranchMatchElim`, the bool case).  These are the THREE recursive
eliminators whose general-scrutinee reducibility — the genuinely hard Tait keystone, proved by Acc-induction on
the scrutinee's strong normalization with the recursive call as a structural sub-term — is already shipped in
Core (`natElimReducibleScrutineeMember` / `natRecReducibleScrutineeMember` /
`listElimReducibleScrutineeMember`).  This file integrates each at the arc, keyed to the `inductiveSaturated`
shape's recursive-elim role, over the elim-native `canonicalDataCandidate` (= `CanonicalFormsPredicate`, the
candidate the Core eliminator theorems consume; see `DataElimArm` for the dataTaitCandidate-vs-
CanonicalFormsPredicate reconciliation note).

## Why these and not fst/snd/idJ

The OPEN general-scrutinee `…ReducibleScrutineeMember` form — the keystone where the scrutinee is an arbitrary
candidate member, NOT a closed value — is proven in Core for exactly four eliminators: `boolElim` (in
`DataElimArm`), `natElim`, `natRec`, `listElim`.  Projection (`fst`/`snd`) and path-induction (`idJ`) have only
the CLOSED scope-0 `…ClosedIsMember` form in Core; their general-scrutinee versions remain Core work, so they
are wired separately and honestly scoped (a later arc file), not folded in here.

## The shared shape

Each arm carries the honest Tait INTERFACE hypotheses exactly as Core states them: `headExpand` (the weak-head
expansion of the result candidate — genuinely fails for the neutral case, hence a contextual parameter), the
motive/branch SN + membership premises, and the per-recursor substituted-reduct membership + termination
premises (the succ / cons contractum interfaces).  The body is a direct application of the Core theorem; the
conclusion's `canonicalDataCandidate` is definitionally `CanonicalFormsPredicate`.

## Zero-axiom verification

Each arm is a direct application of a shipped, audited Core `…ReducibleScrutineeMember` theorem.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- The `natElim` succ-iota substituted reduct, mirroring the Core (private) abbreviation byte-for-byte so the
arc-level premise types read cleanly and stay definitionally equal to what the Core theorem expects. -/
private abbrev natElimSuccContractumOn {scope : Nat} (motive : RawTerm (scope + 1))
    (succBranch : RawTerm (scope + 2)) (predecessor zeroBranch : RawTerm scope) : RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- The `natRec` succ-iota substituted reduct — the `gen_natRec` mirror of `natElimSuccContractumOn`. -/
private abbrev natRecSuccContractumOn {scope : Nat} (motive : RawTerm (scope + 1))
    (succBranch : RawTerm (scope + 2)) (predecessor zeroBranch : RawTerm scope) : RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **★ FTGEN-11 — the `natElim` recursive-elimination arm.**  A `natElim` over a reducible (Nat-candidate)
scrutinee, with SN motive, reducible zero-branch, and the honest succ-contractum interface, is a member of the
result candidate.  The genuine general-scrutinee reducibility (NEUTRAL → CR3, numeral → ι + head-expansion
lifted through the scrutinee congruence) via the Core `natElimReducibleScrutineeMember`. -/
theorem natElimRecursiveElim {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : canonicalDataCandidate IsNatValue scrutinee)
    (zeroBranchMember : canonicalDataCandidate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (substitutedReductMember : ∀ {predecessor : RawTerm scope},
        IsNatValue predecessor →
        canonicalDataCandidate isValue (natElimSuccContractumOn motive succBranch predecessor zeroBranch))
    (substitutedReductTerminates :
        ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
          (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (natElimSuccContractumOn currentMotive currentSucc predecessor currentZero)) :
    canonicalDataCandidate isValue (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  natElimReducibleScrutineeMember headExpand motiveStronglyNormalizing scrutineeMember
    zeroBranchMember succBranchTerminates substitutedReductMember substitutedReductTerminates

/-- **★ FTGEN-11 — the `natRec` recursive-elimination arm** (the dependent-recursor twin of
`natElimRecursiveElim`), via the Core `natRecReducibleScrutineeMember`. -/
theorem natRecRecursiveElim {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : canonicalDataCandidate IsNatValue scrutinee)
    (zeroBranchMember : canonicalDataCandidate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (substitutedReductMember : ∀ {predecessor : RawTerm scope},
        IsNatValue predecessor →
        canonicalDataCandidate isValue (natRecSuccContractumOn motive succBranch predecessor zeroBranch))
    (substitutedReductTerminates :
        ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
          (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (natRecSuccContractumOn currentMotive currentSucc predecessor currentZero)) :
    canonicalDataCandidate isValue (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  natRecReducibleScrutineeMember headExpand motiveStronglyNormalizing scrutineeMember
    zeroBranchMember succBranchTerminates substitutedReductMember substitutedReductTerminates

/-- **★ FTGEN-11 — the `listElim` recursive-elimination arm** (the list twin), via the Core
`listElimReducibleScrutineeMember`.  Carries the 3-argument cons-branch application interface and the
cons-contractum termination interface as Core states them. -/
theorem listElimRecursiveElim {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : canonicalDataCandidate IsListValue scrutinee)
    (nilBranchMember : canonicalDataCandidate isValue nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm scope},
        RawTerm.isStepNormalForm head → IsListValue tail → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons result .childNil))))
    (consContractumTerminates : ∀ head tail : RawTerm scope,
        IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons (listElimCellSpine motive tail nilBranch consBranch) .childNil)))) :
    canonicalDataCandidate isValue (listElimCellSpine motive scrutinee nilBranch consBranch) :=
  listElimReducibleScrutineeMember headExpand motiveStronglyNormalizing scrutineeMember
    nilBranchMember consBranchTerminates consBranchApplication consContractumTerminates

end FX1Poly.Typed
