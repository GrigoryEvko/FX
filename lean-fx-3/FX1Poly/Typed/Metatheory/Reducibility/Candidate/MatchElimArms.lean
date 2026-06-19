import FX1Poly.Typed.Metatheory.Reducibility.Candidate.DataElimArm
import FX1Poly.Core.Eliminators.Match.MatchClosedMembership

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/MatchElimArms
    — the option / either match FT arms (FTGEN-11), CLOSED layer

Completes the descriptor's two-branch `match` role.  `boolElim` already has the OPEN general-scrutinee arm
(`DataElimArm.twoBranchMatchElim`); `optionMatch` and `eitherMatch` have only the CLOSED scope-0
`…ClosedIsMember` reducibility in Core, wired here to the arc over `canonicalDataCandidate`.  Their OPEN
general-scrutinee versions remain Core work (honest scope, stated at file level).

  * **optionMatchClosedArm** — a closed `optionMatch` on an option-candidate-member scrutinee, with a member
    none-branch and a some-branch mapping SN arguments to result-candidate members, lands in the result
    candidate (Core `optionMatchClosedIsMember`).
  * **eitherMatchClosedArm** — the sum twin: both branches apply (no passive base), so both branch-respect-SN
    hypotheses are consumed (Core `eitherMatchClosedIsMember`).

## Zero-axiom verification

Each arm is a direct application of a shipped, audited Core `…ClosedIsMember` theorem.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- **★ FTGEN-11 — the closed `optionMatch` arm.**  A closed `optionMatch` on an option-candidate-member
scrutinee, with SN motive, a member none-branch, and a some-branch sending SN arguments to result-candidate
members, is a member of the result candidate, via the Core `optionMatchClosedIsMember`. -/
theorem optionMatchClosedArm {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee noneBranch someBranch : RawTerm 0}
    (scrutineeMember : canonicalDataCandidate isOptionValue scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (noneBranchMember : canonicalDataCandidate isValue noneBranch)
    (someBranchTerminates : IsStronglyNormalizing someBranch)
    (someBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      canonicalDataCandidate isValue (applicationCell someBranch value)) :
    canonicalDataCandidate isValue
      (.mkGen .gen_optionMatch ()
        (.childCons motive
          (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))) :=
  optionMatchClosedIsMember scrutineeMember motiveTerminates noneBranchMember
    someBranchTerminates someBranchRespectsSN

/-- **★ FTGEN-11 — the closed `eitherMatch` arm**, the sum twin of `optionMatchClosedArm` (both branches
apply, both respect-SN hypotheses consumed), via the Core `eitherMatchClosedIsMember`. -/
theorem eitherMatchClosedArm {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee leftBranch rightBranch : RawTerm 0}
    (scrutineeMember : canonicalDataCandidate isEitherValue scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (leftBranchTerminates : IsStronglyNormalizing leftBranch)
    (rightBranchTerminates : IsStronglyNormalizing rightBranch)
    (leftBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      canonicalDataCandidate isValue (applicationCell leftBranch value))
    (rightBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      canonicalDataCandidate isValue (applicationCell rightBranch value)) :
    canonicalDataCandidate isValue
      (.mkGen .gen_eitherMatch ()
        (.childCons motive
          (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))) :=
  eitherMatchClosedIsMember scrutineeMember motiveTerminates leftBranchTerminates
    rightBranchTerminates leftBranchRespectsSN rightBranchRespectsSN

end FX1Poly.Typed
