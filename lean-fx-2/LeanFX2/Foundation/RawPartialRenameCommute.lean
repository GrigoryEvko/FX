import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.RawSubst

/-! # Foundation/RawPartialRenameCommute — `unweaken?` commutes with `rename`.

Headline lemma:
```
RawTerm.unweaken?_rename_lift_commute :
    unweaken? (term.rename rho.lift) = (unweaken? term).map (·.rename rho)
```

Why we need it.  The cd cascade extension that ships
`RawStep.par.transpReflBeta` (D2.5.4) requires `RawTerm.cd`'s transp
arm to recognise a syntactically-constant developed path
`pathLam (typeRaw.weaken)` and fire β.  The recogniser is
`RawTerm.unweaken?` applied under the `pathLam` binder.  For that
recognition to commute with `rename` (so that `cd_rename` and
`RawCdDominates`' transp arms close), `unweaken?` itself must commute
with the renaming-after-lift.

Proof shape.  Generic compat lemma `partialRename?_rename_compat`:
`partialRename? (term.rename rhoVar) partialB =
    (partialRename? term partialA).map (·.rename rhoTerm)` whenever
`∀ pos, partialB (rhoVar pos) = (partialA pos).map rhoTerm` holds at
the variable level.  Structural induction on `term` over all 67 raw
ctors; binder cases (lam, pathLam, piTyCode, sigmaTyCode) lift the
compat hypothesis under the binder via
`PartialRawRenaming.lift_compat`.  Every match in this file uses full
ctor enumeration, keeping the match compiler propext-clean per
`feedback_lean_zero_axiom_match.md`.

Specialisation: with `rhoVar = rho.lift`, `partialA = partialB =
PartialRawRenaming.dropNewest`, `rhoTerm = rho`, the variable-level
compat reduces to `dropNewest_rename_lift_compat`, immediate from Fin
case analysis.
-/

namespace LeanFX2

/-! ## Variable-level lift compat. -/

/-- Lift a variable-level compat hypothesis under a binder.  If
`partialB ∘ rhoVar = (·.map rhoTerm) ∘ partialA` pointwise, then the
same equation holds after lifting both sides under one new binder. -/
theorem PartialRawRenaming.lift_compat
    {srcA tgtA srcB tgtB : Nat}
    (rhoVar : RawRenaming srcA tgtA)
    (rhoTerm : RawRenaming srcB tgtB)
    (partialA : PartialRawRenaming srcA srcB)
    (partialB : PartialRawRenaming tgtA tgtB)
    (compat : ∀ pos, partialB (rhoVar pos) = (partialA pos).map rhoTerm) :
    ∀ pos : Fin (srcA + 1),
      partialB.lift (rhoVar.lift pos) = (partialA.lift pos).map rhoTerm.lift
  | ⟨0, _⟩ => rfl
  | ⟨index + 1, indexLt⟩ => by
      simp only [PartialRawRenaming.lift, RawRenaming.lift, Fin.succ]
      rw [compat ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩]
      cases partialA ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩ <;> rfl

/-! ## Term-level commute.

Generic compatibility commute for `RawTerm.partialRename?` with a
total `rename` applied first.  Whenever the variable-level compat
`∀ pos, partialB (rhoVar pos) = (partialA pos).map rhoTerm` holds, the
same compat lifts to whole raw terms with the result mapped via
`rhoTerm`.

Headline driver lemma for `unweaken?_rename_lift_commute`.
Structural induction on `term`; 67 ctors total.

Each ctor has the same rhythm: unfold `partialRename?` and `rename`
on both sides, apply the IHs (with `lift` arguments under binders via
`PartialRawRenaming.lift_compat`), and close by `rfl` after the
Option.mapTwo/Option.mapThree distribution. -/
set_option linter.unusedVariables false in
theorem RawTerm.partialRename?_rename_compat :
    ∀ {scopeT srcB tgtA tgtB : Nat}
      (term : RawTerm scopeT)
      (rhoVar : RawRenaming scopeT tgtA)
      (rhoTerm : RawRenaming srcB tgtB)
      (partialA : PartialRawRenaming scopeT srcB)
      (partialB : PartialRawRenaming tgtA tgtB)
      (compat : ∀ pos, partialB (rhoVar pos) = (partialA pos).map rhoTerm),
      RawTerm.partialRename? (term.rename rhoVar) partialB =
        (RawTerm.partialRename? term partialA).map (·.rename rhoTerm) := by
  intro scopeT srcB tgtA tgtB term
  induction term generalizing srcB tgtA tgtB with
  | var position =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [compat position]
      cases partialA position <;> rfl
  | unit => intros; rfl
  | lam body bodyIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [bodyIH rhoVar.lift rhoTerm.lift partialA.lift partialB.lift
        (PartialRawRenaming.lift_compat rhoVar rhoTerm partialA partialB compat)]
      cases RawTerm.partialRename? body partialA.lift <;> rfl
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [functionIH rhoVar rhoTerm partialA partialB compat,
        argumentIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? functionTerm partialA <;>
        cases RawTerm.partialRename? argumentTerm partialA <;> rfl
  | pair firstValue secondValue firstIH secondIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH rhoVar rhoTerm partialA partialB compat,
        secondIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? firstValue partialA <;>
        cases RawTerm.partialRename? secondValue partialA <;> rfl
  | fst pairTerm pairIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [pairIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? pairTerm partialA <;> rfl
  | snd pairTerm pairIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [pairIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? pairTerm partialA <;> rfl
  | boolTrue => intros; rfl
  | boolFalse => intros; rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH rhoVar rhoTerm partialA partialB compat,
        thenIH rhoVar rhoTerm partialA partialB compat,
        elseIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? thenBranch partialA <;>
        cases RawTerm.partialRename? elseBranch partialA <;> rfl
  | natZero => intros; rfl
  | natSucc predecessor predecessorIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [predecessorIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? predecessor partialA <;> rfl
  | natElim scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH rhoVar rhoTerm partialA partialB compat,
        zeroIH rhoVar rhoTerm partialA partialB compat,
        succIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? zeroBranch partialA <;>
        cases RawTerm.partialRename? succBranch partialA <;> rfl
  | natRec scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH rhoVar rhoTerm partialA partialB compat,
        zeroIH rhoVar rhoTerm partialA partialB compat,
        succIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? zeroBranch partialA <;>
        cases RawTerm.partialRename? succBranch partialA <;> rfl
  | listNil => intros; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [headIH rhoVar rhoTerm partialA partialB compat,
        tailIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? headTerm partialA <;>
        cases RawTerm.partialRename? tailTerm partialA <;> rfl
  | listElim scrutinee nilBranch consBranch scrutineeIH nilIH consIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH rhoVar rhoTerm partialA partialB compat,
        nilIH rhoVar rhoTerm partialA partialB compat,
        consIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? nilBranch partialA <;>
        cases RawTerm.partialRename? consBranch partialA <;> rfl
  | optionNone => intros; rfl
  | optionSome valueTerm valueIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [valueIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? valueTerm partialA <;> rfl
  | optionMatch scrutinee noneBranch someBranch scrutineeIH noneIH someIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH rhoVar rhoTerm partialA partialB compat,
        noneIH rhoVar rhoTerm partialA partialB compat,
        someIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? noneBranch partialA <;>
        cases RawTerm.partialRename? someBranch partialA <;> rfl
  | eitherInl valueTerm valueIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [valueIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? valueTerm partialA <;> rfl
  | eitherInr valueTerm valueIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [valueIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? valueTerm partialA <;> rfl
  | eitherMatch scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH rhoVar rhoTerm partialA partialB compat,
        leftIH rhoVar rhoTerm partialA partialB compat,
        rightIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? leftBranch partialA <;>
        cases RawTerm.partialRename? rightBranch partialA <;> rfl
  | refl witness witnessIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [witnessIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? witness partialA <;> rfl
  | idJ baseCase witness baseIH witnessIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH rhoVar rhoTerm partialA partialB compat,
        witnessIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? baseCase partialA <;>
        cases RawTerm.partialRename? witness partialA <;> rfl
  | modIntro innerTerm innerIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? innerTerm partialA <;> rfl
  | modElim innerTerm innerIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? innerTerm partialA <;> rfl
  | subsume innerTerm innerIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? innerTerm partialA <;> rfl
  | interval0 => intros; rfl
  | interval1 => intros; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [intervalIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? intervalTerm partialA <;> rfl
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH rhoVar rhoTerm partialA partialB compat,
        rightIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? leftInterval partialA <;>
        cases RawTerm.partialRename? rightInterval partialA <;> rfl
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH rhoVar rhoTerm partialA partialB compat,
        rightIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? leftInterval partialA <;>
        cases RawTerm.partialRename? rightInterval partialA <;> rfl
  | pathLam body bodyIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [bodyIH rhoVar.lift rhoTerm.lift partialA.lift partialB.lift
        (PartialRawRenaming.lift_compat rhoVar rhoTerm partialA partialB compat)]
      cases RawTerm.partialRename? body partialA.lift <;> rfl
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [pathIH rhoVar rhoTerm partialA partialB compat,
        intervalIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? pathTerm partialA <;>
        cases RawTerm.partialRename? intervalArg partialA <;> rfl
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH rhoVar rhoTerm partialA partialB compat,
        partialIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? baseValue partialA <;>
        cases RawTerm.partialRename? partialValue partialA <;> rfl
  | glueElim gluedValue gluedIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [gluedIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? gluedValue partialA <;> rfl
  | transp pathTerm sourceTerm pathIH sourceIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [pathIH rhoVar rhoTerm partialA partialB compat,
        sourceIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? pathTerm partialA <;>
        cases RawTerm.partialRename? sourceTerm partialA <;> rfl
  | hcomp sidesTerm capTerm sidesIH capIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [sidesIH rhoVar rhoTerm partialA partialB compat,
        capIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? sidesTerm partialA <;>
        cases RawTerm.partialRename? capTerm partialA <;> rfl
  | oeqRefl witness witnessIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [witnessIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? witness partialA <;> rfl
  | oeqJ baseCase witness baseIH witnessIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH rhoVar rhoTerm partialA partialB compat,
        witnessIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? baseCase partialA <;>
        cases RawTerm.partialRename? witness partialA <;> rfl
  | oeqFunext pointwise pointwiseIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [pointwiseIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? pointwise partialA <;> rfl
  | idStrictRefl witness witnessIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [witnessIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? witness partialA <;> rfl
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH rhoVar rhoTerm partialA partialB compat,
        witnessIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? baseCase partialA <;>
        cases RawTerm.partialRename? witness partialA <;> rfl
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [forwardIH rhoVar rhoTerm partialA partialB compat,
        backwardIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? forwardFn partialA <;>
        cases RawTerm.partialRename? backwardFn partialA <;> rfl
  | equivApp equivTerm argument equivIH argumentIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [equivIH rhoVar rhoTerm partialA partialB compat,
        argumentIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? equivTerm partialA <;>
        cases RawTerm.partialRename? argument partialA <;> rfl
  | refineIntro rawValue predicateProof valueIH proofIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [valueIH rhoVar rhoTerm partialA partialB compat,
        proofIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? rawValue partialA <;>
        cases RawTerm.partialRename? predicateProof partialA <;> rfl
  | refineElim refinedValue refinedIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [refinedIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? refinedValue partialA <;> rfl
  | recordIntro firstField firstIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [firstIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? firstField partialA <;> rfl
  | recordProj recordValue recordIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [recordIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? recordValue partialA <;> rfl
  | codataUnfold initialState transition stateIH transitionIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [stateIH rhoVar rhoTerm partialA partialB compat,
        transitionIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? initialState partialA <;>
        cases RawTerm.partialRename? transition partialA <;> rfl
  | codataDest codataValue codataIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [codataIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? codataValue partialA <;> rfl
  | sessionSend channel payload channelIH payloadIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [channelIH rhoVar rhoTerm partialA partialB compat,
        payloadIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? channel partialA <;>
        cases RawTerm.partialRename? payload partialA <;> rfl
  | sessionRecv channel channelIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [channelIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? channel partialA <;> rfl
  | effectPerform operationTag arguments tagIH argumentsIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [tagIH rhoVar rhoTerm partialA partialB compat,
        argumentsIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? operationTag partialA <;>
        cases RawTerm.partialRename? arguments partialA <;> rfl
  | universeCode innerLevel => intros; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH rhoVar rhoTerm partialA partialB compat,
        codomainIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? domainCode partialA <;>
        cases RawTerm.partialRename? codomainCode partialA <;> rfl
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH rhoVar rhoTerm partialA partialB compat,
        codomainIH rhoVar.lift rhoTerm.lift partialA.lift partialB.lift
          (PartialRawRenaming.lift_compat rhoVar rhoTerm partialA partialB compat)]
      cases RawTerm.partialRename? domainCode partialA <;>
        cases RawTerm.partialRename? codomainCode partialA.lift <;> rfl
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH rhoVar rhoTerm partialA partialB compat,
        codomainIH rhoVar.lift rhoTerm.lift partialA.lift partialB.lift
          (PartialRawRenaming.lift_compat rhoVar rhoTerm partialA partialB compat)]
      cases RawTerm.partialRename? domainCode partialA <;>
        cases RawTerm.partialRename? codomainCode partialA.lift <;> rfl
  | productCode firstCode secondCode firstIH secondIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH rhoVar rhoTerm partialA partialB compat,
        secondIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? firstCode partialA <;>
        cases RawTerm.partialRename? secondCode partialA <;> rfl
  | sumCode leftCode rightCode leftIH rightIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH rhoVar rhoTerm partialA partialB compat,
        rightIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? leftCode partialA <;>
        cases RawTerm.partialRename? rightCode partialA <;> rfl
  | listCode elementCode elementIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [elementIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? elementCode partialA <;> rfl
  | optionCode elementCode elementIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [elementIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? elementCode partialA <;> rfl
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH rhoVar rhoTerm partialA partialB compat,
        rightIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? leftCode partialA <;>
        cases RawTerm.partialRename? rightCode partialA <;> rfl
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [typeIH rhoVar rhoTerm partialA partialB compat,
        leftIH rhoVar rhoTerm partialA partialB compat,
        rightIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? typeCode partialA <;>
        cases RawTerm.partialRename? leftRaw partialA <;>
        cases RawTerm.partialRename? rightRaw partialA <;> rfl
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH rhoVar rhoTerm partialA partialB compat,
        rightIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? leftTypeCode partialA <;>
        cases RawTerm.partialRename? rightTypeCode partialA <;> rfl
  | cumulUpMarker innerCode innerIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? innerCode partialA <;> rfl
  | uaToEquiv proofRaw proofIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [proofIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? proofRaw partialA <;> rfl
  | equivApply equivRaw argRaw equivIH argIH =>
      intro rhoVar rhoTerm partialA partialB compat
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [equivIH rhoVar rhoTerm partialA partialB compat,
        argIH rhoVar rhoTerm partialA partialB compat]
      cases RawTerm.partialRename? equivRaw partialA <;>
        cases RawTerm.partialRename? argRaw partialA <;> rfl

/-! ## Specialisation: `unweaken?` commutes with `rename` after `lift`. -/

/-- Variable-level compat used to derive `unweaken?_rename_lift_commute`
from the generic `partialRename?_rename_compat`.  Specialises both
partial-renamings to `dropNewest`, the source-rename to `rho.lift`,
and the result-rename to `rho`. -/
theorem PartialRawRenaming.dropNewest_rename_lift_compat
    {srcA tgtA : Nat} (rho : RawRenaming srcA tgtA) :
    ∀ (pos : Fin (srcA + 1)),
      PartialRawRenaming.dropNewest (RawRenaming.lift rho pos) =
        (PartialRawRenaming.dropNewest pos).map rho
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- `RawTerm.unweaken?` commutes with `rename` after lifting under one
binder.  Specialisation of the generic `partialRename?_rename_compat`
with both partial-renamings set to `PartialRawRenaming.dropNewest`,
the source-rename to `rho.lift`, and the result-rename to `rho`.

This is the headline lemma the cd cascade extension for
`RawStep.par.transpReflBeta` (D2.5.4) needs.  It lets `cdTranspCase`'s
inner `Option.match` on `unweaken? pathBody` align with the same match
on `unweaken? (pathBody.rename rho.lift)` after applying the rename. -/
theorem RawTerm.unweaken?_rename_lift_commute {srcA tgtA : Nat}
    (term : RawTerm (srcA + 1)) (rho : RawRenaming srcA tgtA) :
    RawTerm.unweaken? (term.rename rho.lift) =
      (RawTerm.unweaken? term).map (·.rename rho) := by
  unfold RawTerm.unweaken?
  exact RawTerm.partialRename?_rename_compat term rho.lift rho
    PartialRawRenaming.dropNewest PartialRawRenaming.dropNewest
    (PartialRawRenaming.dropNewest_rename_lift_compat rho)

end LeanFX2
