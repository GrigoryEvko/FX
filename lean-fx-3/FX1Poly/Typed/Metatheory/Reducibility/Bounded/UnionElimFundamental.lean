import FX1Poly.Typed.Metatheory.Reducibility.Bounded.DependentDataElimRows
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.GeneralElimRows

/-! # FX1Poly/Typed/UnionElimFundamental
    — the native `elimFundamental` premise glued at the elim table (TYTAB-4 step 4, DEP-GLUE #1733)

`HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms` (`BoundedUnionFundamental.lean`) takes three explicit
table-arm FT premises; this file glues the THIRD — the `elimFundamental` premise — for ANY generator whose
elim rule comes from `elimRuleOf` (the `fxTypingBundle.elim` table).  It is the eliminator twin of
`fundamentalIntroRowAtBoundedSucc` (`UnionIntroFundamental.lean`), the SECOND premise's glue.

## The eleven-row `elimRuleOf_cases` assembly + the per-row computation residue

`elimRuleOf` tags every eliminator generator with one of eleven `ElimRule` rows, each shipped as a per-row
bounded-member FT theorem (the DEP-* chain).  Unlike INTRODUCERS (which never compute, so the intro glue is
residue-free), ELIMINATORS compute on their canonical scrutinee, and that ι-computation member is — per the
per-row files' own ledger — "NOT dischargeable at the open/bounded level" (the scrutinee arrives as a variable
/ neutral; it reduces to a constructor only after the CLOSING substitution).  So those ι residues are THREADED
at the bounded level, exactly as the per-row theorems and the `BoundedNatElimFundamental` /
`BoundedListElimFundamental` / eitherMatch / optionMatch bridges thread them; this glue carries them as explicit
premises feeding the computing arms, and they are discharged at the CLOSED instance (DEP-3PREMISE #1734), where
the closed scrutinee reduces to a canonical value.

The residue inventory, by tier:

  * FOUR uniform arms — `app` / `pathApp` (`GeneralElimRows.lean`) and `boolElim` / `idJ`
    (`DependentDataElimRows.lean`) — take ONLY the obligation IHs (`premisesFundamental`).  `boolElim` lands its
    branches directly in the result candidate; `idJ`'s Paulin-Mohring base-case transfer is discharged inside
    its engine.
  * FOUR reach-conditioned arms (Tier-1, #1755): `fst` / `snd` (one pair-reach residue each), `optionMatch` (a
    branch-application SN + a some-reach residue), `eitherMatch` (a branch-application SN + inl-reach +
    inr-reach).
  * THREE recursive arms (Tier-2, #1754): `natElim` / `natRec` are now SELF-CONTAINED (residue-free — whole-cell SN
    is derived from the in-recursion contractum MEMBERSHIP through the scrutinee-reducing four-fold engine, with no
    SN-of-branches obligation); `listElim` carries only the recursive cons-branch-application MEMBER (a
    reach-conditioned member residue exactly like the Tier-1 arms, discharged at the closed leg).  The earlier bare
    succ-contractum / cons-contractum SN residues were universally false and have been eliminated (FTGEN-13.1).

`elimRuleOf_cases` reverse-extracts the eleven-way `(generator = gen_X ∧ rule = XElimRule)` disjunction; each
arm substitutes the pinned `XElimRule` (so the goal's `memberCell` / `outputType` and the obligation premise
reduce to the per-row theorem's by construction) and feeds the matching row its obligation IHs plus the
matching threaded residues.  A future eliminator row (a `ProfileExtension` eliminator) adds one disjunct here.

## Zero-axiom verification

`rcases elimRuleOf_cases` (11 arms) feeding the per-row theorems (themselves zero-axiom), threading each row's
ι-computation residue.  No new members, no induction.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- The `listElim` cons-ι contractum — byte-for-byte identical to `DependentDataElimRows.lean`'s own private
copy (each consuming file replicates it because that copy is `private`), so the threaded
`consBranchApplicationClosed` member residue's premise type is DEFEQ (reducible `abbrev`) to what
`fundamentalListElimRowAtBoundedSucc` expects. -/
private abbrev listElimConsContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (consBranch head tail nilBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
          (.childCons tail .childNil)))
      (.childCons
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons tail .childNil)))))
        .childNil))

/-- **The native `elimFundamental` premise glue (TYTAB-4 step 4, DEP-GLUE).**  Every generator carrying an
`elimRuleOf` elim rule makes its eliminator member cell a bound-reducible member of the rule's output type,
given the obligation IHs (`premisesFundamental`) and the eleven per-row ι-computation residues (threaded,
dischargeable only at the closed instance).  The eleven-row `elimRuleOf_cases` assembly: each arm substitutes
the pinned `ElimRule` and feeds the shipped per-row theorem, whose obligation premise / output match the glue's
by construction; the computing arms additionally receive the matching threaded residues.  The eliminator twin
of `fundamentalIntroRowAtBoundedSucc`. -/
theorem fundamentalElimRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} {context : TypingContext profile scope} {generator : Generator} {rule : ElimRule}
    {args : RawTermChildren rule.argShifts scope} {params : RawTermChildren rule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (isElim : elimRuleOf generator = some rule)
    (premisesFundamental : ∀ obligation,
        obligation ∈ rule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier)
    (optionSomeBranchMemberIfReachesSome : ∀ (currentMotive : RawTerm (scope + 1))
        (currentScrutinee currentSomeBranch : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ payload : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentScrutinee) (optionSomeCell payload) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (RawTerm.subst substitution currentScrutinee))
            (applicationCell (RawTerm.subst substitution currentSomeBranch) payload))
    (eitherLeftBranchMemberIfReachesInl : ∀ (currentMotive : RawTerm (scope + 1))
        (currentScrutinee currentLeftBranch : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ payload : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentScrutinee) (eitherInlCell payload) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (RawTerm.subst substitution currentScrutinee))
            (applicationCell (RawTerm.subst substitution currentLeftBranch) payload))
    (eitherRightBranchMemberIfReachesInr : ∀ (currentMotive : RawTerm (scope + 1))
        (currentScrutinee currentRightBranch : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ payload : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentScrutinee) (eitherInrCell payload) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (RawTerm.subst substitution currentScrutinee))
            (applicationCell (RawTerm.subst substitution currentRightBranch) payload))
    (fstFirstMemberIfReachesPair : ∀ (currentPairTerm currentFirstType : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ first second : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentPairTerm) (pairCell first second) →
          IsReducibleMemberAtBounded env bound (RawTerm.subst substitution currentFirstType) first)
    (sndSecondMemberIfReachesPair : ∀ (currentPairTerm currentSecondType : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ first second : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentPairTerm) (pairCell first second) →
          IsReducibleMemberAtBounded env bound (RawTerm.subst substitution currentSecondType) second)
    (listElimConsBranchApplicationClosed : ∀ (currentMotive : RawTerm (scope + 1))
        (currentNil currentCons : RawTerm scope)
        {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ {head tail : RawTerm (targetScope + 1)},
          IsStronglyNormalizing head →
          dataTaitCandidate IsListStructured tail →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive) tail)
            (listElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) currentMotive) tail
              (RawTerm.subst substitution currentNil) (RawTerm.subst substitution currentCons)) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (listConsCell head tail))
            (listElimConsContractum (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (RawTerm.subst substitution currentCons) head tail (RawTerm.subst substitution currentNil))) :
    FundamentalConclusionAtBoundedSucc env bound context (rule.memberCell scope args)
      (rule.outputType scope args params) := by
  rcases elimRuleOf_cases isElim with
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact fundamentalAppElimRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalPathAppElimRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalNatElimRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalNatRecRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalBoolElimRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalOptionMatchRowAtBoundedSucc env bound context premisesFundamental
      optionSomeBranchMemberIfReachesSome
  · exact fundamentalEitherMatchRowAtBoundedSucc env bound context premisesFundamental
      eitherLeftBranchMemberIfReachesInl
      eitherRightBranchMemberIfReachesInr
  · exact fundamentalIdJRowAtBoundedSucc env bound context premisesFundamental
  · exact fundamentalFstRowAtBoundedSucc env bound context premisesFundamental
      fstFirstMemberIfReachesPair
  · exact fundamentalSndRowAtBoundedSucc env bound context premisesFundamental
      sndSecondMemberIfReachesPair
  · exact fundamentalListElimRowAtBoundedSucc env bound context premisesFundamental
      listElimConsBranchApplicationClosed

end FX1Poly.Typed
