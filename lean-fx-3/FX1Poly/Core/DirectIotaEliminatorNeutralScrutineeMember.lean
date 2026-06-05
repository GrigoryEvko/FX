import FX1Poly.Core.NatElimNeutralScrutineeMember
import FX1Poly.Core.BoolElimStrongNormalization
import FX1Poly.Core.IdentityEliminatorStrongNormalization
import FX1Poly.Core.StrongNormalizationIotaRedexes

/-! # FX1Poly/Core/DirectIotaEliminatorNeutralScrutineeMember
    — the neutral-scrutinee regime of the DIRECT-ι eliminators (boolElim / fst / snd / idJ / idStrictRec)

The non-recursive companion to `NatElimNeutralScrutineeMember` / `ListElimNeutralScrutineeMember`.  Those built
a bespoke triple-accessibility cell-SN because the RECURSIVE recursors' ι-reduct (`natElim (succ n) … ↝ app (app
s n) (natElim n …)`) is an application whose SN needs the branch-application interface.  The eliminators here are
DIRECT-ι: each ι-reduct is a branch or a structural component, NOT an application —

  * `boolElim true t e ↝ t`  /  `boolElim false t e ↝ e`     (branch selected directly)
  * `fst (pair a b) ↝ a`     /  `snd (pair a b) ↝ b`         (component projected directly)
  * `idJ d (refl w) ↝ d`     /  `idStrictRec d (refl w) ↝ d` (base case selected directly)

so their cell-SN-from-children is already shipped with NO extra interface
(`boolElim_isStronglyNormalizing_of_strongly_normalizing_branches`,
`fst/snd_isStronglyNormalizing_of_argument`, `idJ/idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base`).
Hence each neutral member is a pure compose: the cell is neutral (its principal child is neutral, the relevant
`IsNeutral` arm) and strongly normalizing (the shipped cell-SN on the children's SN), so it inhabits EVERY
reducibility candidate by `IsReducibilityCandidate.memberOfStronglyNormalizingNeutral`.

This brings the direct-ι eliminators to the neutral-coverage parity already held by the three recursive recursors.
The remaining two eliminators — `optionMatch` / `eitherMatch` — are application-ι
(`optionMatch (some v) … ↝ app someBranch v`), so they need a bespoke neutral-scrutinee cell-SN (the `natElim`
pattern) and are deferred to a follow-up; with those, all twelve `IsNeutral` eliminators are reducible over a
neutral principal child.

`#672`-independent (fixed result candidate, the pure Tait neutral-eliminator argument).

## Zero-axiom verification

Each member is `candidate.memberOfStronglyNormalizingNeutral cellSN (IsNeutral.X principalNeutral)`, where
`cellSN` is the shipped cell-SN fed the children's SN (CR1 on the member hypotheses).  No new induction, no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **`boolElim` over a neutral SN scrutinee with reducible branches is a member of the result candidate.**  The
cell is neutral (`IsNeutral.boolElim`) and SN (`boolElim_isStronglyNormalizing_of_strongly_normalizing_branches`
on the branches' SN via CR1), so it inhabits the candidate by the abstract neutral bridge. -/
theorem boolElimNeutralScrutineeMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop) (candidate : IsReducibilityCandidate resultCandidate)
    {scrutinee : RawTerm scope}
    (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {thenBranch elseBranch : RawTerm scope}
    (thenBranchMember : resultCandidate thenBranch) (elseBranchMember : resultCandidate elseBranch) :
    resultCandidate
      (.mkGen .gen_boolElim ()
        (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))) :=
  candidate.memberOfStronglyNormalizingNeutral
    (boolElim_isStronglyNormalizing_of_strongly_normalizing_branches scrutineeStronglyNormalizing
      (candidate.stronglyNormalizing thenBranchMember)
      (candidate.stronglyNormalizing elseBranchMember))
    (IsNeutral.boolElim scrutineeNeutral)

/-- **`fst` over a neutral SN argument is a member of the result candidate.**  The projection is neutral
(`IsNeutral.fst`) and SN (`fst_isStronglyNormalizing_of_argument`), so it inhabits the candidate by the abstract
neutral bridge. -/
theorem fstNeutralArgumentMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop) (candidate : IsReducibilityCandidate resultCandidate)
    {argument : RawTerm scope}
    (argumentStronglyNormalizing : IsStronglyNormalizing argument) (argumentNeutral : IsNeutral argument) :
    resultCandidate (.mkGen .gen_fst () (.childCons argument .childNil)) :=
  candidate.memberOfStronglyNormalizingNeutral
    (fst_isStronglyNormalizing_of_argument argumentStronglyNormalizing)
    (IsNeutral.fst argumentNeutral)

/-- **`snd` over a neutral SN argument is a member of the result candidate** (the second-projection dual of
`fstNeutralArgumentMember`). -/
theorem sndNeutralArgumentMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop) (candidate : IsReducibilityCandidate resultCandidate)
    {argument : RawTerm scope}
    (argumentStronglyNormalizing : IsStronglyNormalizing argument) (argumentNeutral : IsNeutral argument) :
    resultCandidate (.mkGen .gen_snd () (.childCons argument .childNil)) :=
  candidate.memberOfStronglyNormalizingNeutral
    (snd_isStronglyNormalizing_of_argument argumentStronglyNormalizing)
    (IsNeutral.snd argumentNeutral)

/-- **`idJ` over a neutral SN witness with a reducible base case is a member of the result candidate.**  The
identity eliminator is neutral on its WITNESS child (`IsNeutral.idJ`); with the base case reducible and the
witness SN the cell is SN (`idJ_isStronglyNormalizing_of_strongly_normalizing_base`), so it inhabits the
candidate by the abstract neutral bridge. -/
theorem idJNeutralWitnessMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop) (candidate : IsReducibilityCandidate resultCandidate)
    {baseCase witness : RawTerm scope}
    (baseCaseMember : resultCandidate baseCase)
    (witnessStronglyNormalizing : IsStronglyNormalizing witness) (witnessNeutral : IsNeutral witness) :
    resultCandidate (.mkGen .gen_idJ () (.childCons baseCase (.childCons witness .childNil))) :=
  candidate.memberOfStronglyNormalizingNeutral
    (idJ_isStronglyNormalizing_of_strongly_normalizing_base
      (candidate.stronglyNormalizing baseCaseMember) witnessStronglyNormalizing)
    (IsNeutral.idJ witnessNeutral)

/-- **`idStrictRec` over a neutral SN witness with a reducible base case is a member of the result candidate**
(the strict-identity dual of `idJNeutralWitnessMember`). -/
theorem idStrictRecNeutralWitnessMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop) (candidate : IsReducibilityCandidate resultCandidate)
    {baseCase witness : RawTerm scope}
    (baseCaseMember : resultCandidate baseCase)
    (witnessStronglyNormalizing : IsStronglyNormalizing witness) (witnessNeutral : IsNeutral witness) :
    resultCandidate (.mkGen .gen_idStrictRec () (.childCons baseCase (.childCons witness .childNil))) :=
  candidate.memberOfStronglyNormalizingNeutral
    (idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base
      (candidate.stronglyNormalizing baseCaseMember) witnessStronglyNormalizing)
    (IsNeutral.idStrictRec witnessNeutral)

end FX1Poly.Core
