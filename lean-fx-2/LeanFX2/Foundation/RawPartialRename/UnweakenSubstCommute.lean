import LeanFX2.Foundation.RawPartialRenameCommute
import LeanFX2.Foundation.RawPartialRename.VarLemmas

/-! # Foundation/RawPartialRename/UnweakenSubstCommute —
`unweaken?` commutes with `subst` after `lift`.

Headline lemma:
```
RawTerm.unweaken?_subst_lift_commute :
    unweaken? (term.subst sigma.lift) = (unweaken? term).map (·.subst sigma)
```

Why we need it.  The D2.5.5 propositional-premise architecture
(unblocker #1947) for `transpPiBetaSimple` carries a negative premise
`unweaken? (piTyCode dC cC.weaken) = none`.  For the subst-compat
cascade of that rule to close, `unweaken?` itself must commute with
substitution-after-lift — analog of `unweaken?_rename_lift_commute`
shipped in the sibling file `Foundation/RawPartialRenameCommute.lean`.

Proof shape.  Generic compat lemma `partialRename?_subst_compat`:
`partialRename? (term.subst sigma) partialB =
    (partialRename? term partialA).map (·.subst sigmaResult)` whenever
`∀ pos, partialRename? (sigma pos) partialB = (partialA pos).map sigmaResult`
holds at the variable level.  Structural induction on `term` over all
73 raw ctors; binder cases (lam, pathLam, piTyCode, sigmaTyCode) lift
the compat hypothesis under the binder via
`PartialRawRenaming.lift_subst_compat`.  Every match uses full ctor
enumeration, keeping the match compiler propext-clean per
`feedback_lean_zero_axiom_match.md`.

Specialisation: with `sigma = sigmaOriginal.lift`, `sigmaResult =
sigmaOriginal`, `partialA = partialB = PartialRawRenaming.dropNewest`,
the variable-level compat reduces to `dropNewest_subst_lift_compat`,
immediate from Fin case analysis using `RawTerm.unweaken?_weaken`.
-/

namespace LeanFX2

/-! ## Variable-level lift compat for subst. -/

/-- `partialRenaming.lift` commutes with `RawRenaming.weaken` at the
variable level — needed to discharge the binder lift compat for the
subst-flavoured driver below. -/
private theorem PartialRawRenaming.lift_weaken_pointwise
    {sourceScope targetScope : Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope) :
    ∀ pos : Fin sourceScope,
      partialRenaming.lift (RawRenaming.weaken pos) =
        (partialRenaming pos).map RawRenaming.weaken
  | ⟨val, isLt⟩ => by
      show partialRenaming.lift ⟨val + 1, Nat.succ_lt_succ isLt⟩ =
        Option.map RawRenaming.weaken (partialRenaming ⟨val, isLt⟩)
      simp only [PartialRawRenaming.lift]
      cases partialRenaming ⟨val, isLt⟩ <;> rfl

/-- Lift a variable-level subst-compat hypothesis under a binder.  If
`partialRename? (sigma pos) partialB = (partialA pos).map sigmaResult`
pointwise, then the same equation holds after lifting both
partial-renamings + the substitution + the result-substitution under
one new binder. -/
theorem PartialRawRenaming.lift_subst_compat
    {scopeA tgtA srcB tgtB : Nat}
    (sigma : RawTermSubst scopeA tgtA)
    (sigmaResult : RawTermSubst srcB tgtB)
    (partialA : PartialRawRenaming scopeA srcB)
    (partialB : PartialRawRenaming tgtA tgtB)
    (compat : ∀ pos,
      RawTerm.partialRename? (sigma pos) partialB =
        (partialA pos).map sigmaResult) :
    ∀ pos : Fin (scopeA + 1),
      RawTerm.partialRename? (sigma.lift pos) partialB.lift =
        (partialA.lift pos).map sigmaResult.lift
  | ⟨0, _⟩ => rfl
  | ⟨index + 1, indexLt⟩ => by
      simp only [RawTermSubst.lift, PartialRawRenaming.lift]
      rw [RawTerm.partialRename?_rename_compat
            (sigma ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩)
            RawRenaming.weaken RawRenaming.weaken partialB partialB.lift
            (PartialRawRenaming.lift_weaken_pointwise partialB),
          compat ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩]
      cases partialA ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩ <;> rfl

/-! ## Term-level commute.

Generic compatibility commute for `RawTerm.partialRename?` with a
total `subst` applied first.  Whenever the variable-level compat
`∀ pos, partialRename? (sigma pos) partialB = (partialA pos).map sigmaResult`
holds, the same compat lifts to whole raw terms with the result mapped
via `(·.subst sigmaResult)`.

Headline driver lemma for `unweaken?_subst_lift_commute`.
Structural induction on `term`; 73 ctors total.

Each ctor has the same rhythm: unfold `partialRename?` and `subst` on
both sides, apply the IHs (with `lift` arguments under binders via
`PartialRawRenaming.lift_subst_compat`), and close by `rfl` after the
Option.mapTwo/Option.mapThree distribution. -/
set_option linter.unusedVariables false in
theorem RawTerm.partialRename?_subst_compat :
    ∀ {scopeT srcB tgtA tgtB : Nat}
      (term : RawTerm scopeT)
      (sigma : RawTermSubst scopeT tgtA)
      (sigmaResult : RawTermSubst srcB tgtB)
      (partialA : PartialRawRenaming scopeT srcB)
      (partialB : PartialRawRenaming tgtA tgtB)
      (compat : ∀ pos,
        RawTerm.partialRename? (sigma pos) partialB =
          (partialA pos).map sigmaResult),
      RawTerm.partialRename? (term.subst sigma) partialB =
        (RawTerm.partialRename? term partialA).map (·.subst sigmaResult) := by
  intro scopeT srcB tgtA tgtB term
  induction term generalizing srcB tgtA tgtB with
  | var position =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [compat position]
      cases partialA position <;> rfl
  | unit => intros; rfl
  | lam body bodyIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [bodyIH sigma.lift sigmaResult.lift partialA.lift partialB.lift
        (PartialRawRenaming.lift_subst_compat sigma sigmaResult partialA
          partialB compat)]
      cases RawTerm.partialRename? body partialA.lift <;> rfl
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [functionIH sigma sigmaResult partialA partialB compat,
        argumentIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? functionTerm partialA <;>
        cases RawTerm.partialRename? argumentTerm partialA <;> rfl
  | pair firstValue secondValue firstIH secondIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sigma sigmaResult partialA partialB compat,
        secondIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? firstValue partialA <;>
        cases RawTerm.partialRename? secondValue partialA <;> rfl
  | fst pairTerm pairIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [pairIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? pairTerm partialA <;> rfl
  | snd pairTerm pairIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [pairIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? pairTerm partialA <;> rfl
  | boolTrue => intros; rfl
  | boolFalse => intros; rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sigma sigmaResult partialA partialB compat,
        thenIH sigma sigmaResult partialA partialB compat,
        elseIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? thenBranch partialA <;>
        cases RawTerm.partialRename? elseBranch partialA <;> rfl
  | natZero => intros; rfl
  | natSucc predecessor predecessorIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [predecessorIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? predecessor partialA <;> rfl
  | natElim scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sigma sigmaResult partialA partialB compat,
        zeroIH sigma sigmaResult partialA partialB compat,
        succIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? zeroBranch partialA <;>
        cases RawTerm.partialRename? succBranch partialA <;> rfl
  | natRec scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sigma sigmaResult partialA partialB compat,
        zeroIH sigma sigmaResult partialA partialB compat,
        succIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? zeroBranch partialA <;>
        cases RawTerm.partialRename? succBranch partialA <;> rfl
  | listNil => intros; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [headIH sigma sigmaResult partialA partialB compat,
        tailIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? headTerm partialA <;>
        cases RawTerm.partialRename? tailTerm partialA <;> rfl
  | listElim scrutinee nilBranch consBranch scrutineeIH nilIH consIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sigma sigmaResult partialA partialB compat,
        nilIH sigma sigmaResult partialA partialB compat,
        consIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? nilBranch partialA <;>
        cases RawTerm.partialRename? consBranch partialA <;> rfl
  | optionNone => intros; rfl
  | optionSome valueTerm valueIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [valueIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? valueTerm partialA <;> rfl
  | optionMatch scrutinee noneBranch someBranch scrutineeIH noneIH someIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sigma sigmaResult partialA partialB compat,
        noneIH sigma sigmaResult partialA partialB compat,
        someIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? noneBranch partialA <;>
        cases RawTerm.partialRename? someBranch partialA <;> rfl
  | eitherInl valueTerm valueIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [valueIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? valueTerm partialA <;> rfl
  | eitherInr valueTerm valueIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [valueIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? valueTerm partialA <;> rfl
  | eitherMatch scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sigma sigmaResult partialA partialB compat,
        leftIH sigma sigmaResult partialA partialB compat,
        rightIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? scrutinee partialA <;>
        cases RawTerm.partialRename? leftBranch partialA <;>
        cases RawTerm.partialRename? rightBranch partialA <;> rfl
  | refl witness witnessIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [witnessIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? witness partialA <;> rfl
  | idJ baseCase witness baseIH witnessIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sigma sigmaResult partialA partialB compat,
        witnessIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? baseCase partialA <;>
        cases RawTerm.partialRename? witness partialA <;> rfl
  | modIntro innerTerm innerIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [innerIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? innerTerm partialA <;> rfl
  | modElim innerTerm innerIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [innerIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? innerTerm partialA <;> rfl
  | subsume innerTerm innerIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [innerIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? innerTerm partialA <;> rfl
  | interval0 => intros; rfl
  | interval1 => intros; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [intervalIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? intervalTerm partialA <;> rfl
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sigma sigmaResult partialA partialB compat,
        rightIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? leftInterval partialA <;>
        cases RawTerm.partialRename? rightInterval partialA <;> rfl
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sigma sigmaResult partialA partialB compat,
        rightIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? leftInterval partialA <;>
        cases RawTerm.partialRename? rightInterval partialA <;> rfl
  | pathLam body bodyIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [bodyIH sigma.lift sigmaResult.lift partialA.lift partialB.lift
        (PartialRawRenaming.lift_subst_compat sigma sigmaResult partialA
          partialB compat)]
      cases RawTerm.partialRename? body partialA.lift <;> rfl
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [pathIH sigma sigmaResult partialA partialB compat,
        intervalIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? pathTerm partialA <;>
        cases RawTerm.partialRename? intervalArg partialA <;> rfl
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sigma sigmaResult partialA partialB compat,
        partialIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? baseValue partialA <;>
        cases RawTerm.partialRename? partialValue partialA <;> rfl
  | glueElim gluedValue gluedIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [gluedIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? gluedValue partialA <;> rfl
  | transp pathTerm sourceTerm pathIH sourceIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [pathIH sigma sigmaResult partialA partialB compat,
        sourceIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? pathTerm partialA <;>
        cases RawTerm.partialRename? sourceTerm partialA <;> rfl
  | transpFill pathTerm intervalTerm sourceTerm pathIH intervalIH sourceIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapThree]
      rw [pathIH sigma sigmaResult partialA partialB compat,
        intervalIH sigma sigmaResult partialA partialB compat,
        sourceIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? pathTerm partialA <;>
        cases RawTerm.partialRename? intervalTerm partialA <;>
        cases RawTerm.partialRename? sourceTerm partialA <;> rfl
  | hcomp sidesTerm capTerm sidesIH capIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [sidesIH sigma sigmaResult partialA partialB compat,
        capIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? sidesTerm partialA <;>
        cases RawTerm.partialRename? capTerm partialA <;> rfl
  | oeqRefl witness witnessIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [witnessIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? witness partialA <;> rfl
  | oeqJ baseCase witness baseIH witnessIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sigma sigmaResult partialA partialB compat,
        witnessIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? baseCase partialA <;>
        cases RawTerm.partialRename? witness partialA <;> rfl
  | oeqFunext pointwise pointwiseIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [pointwiseIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? pointwise partialA <;> rfl
  | idStrictRefl witness witnessIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [witnessIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? witness partialA <;> rfl
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sigma sigmaResult partialA partialB compat,
        witnessIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? baseCase partialA <;>
        cases RawTerm.partialRename? witness partialA <;> rfl
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [forwardIH sigma sigmaResult partialA partialB compat,
        backwardIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? forwardFn partialA <;>
        cases RawTerm.partialRename? backwardFn partialA <;> rfl
  | equivApp equivTerm argument equivIH argumentIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [equivIH sigma sigmaResult partialA partialB compat,
        argumentIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? equivTerm partialA <;>
        cases RawTerm.partialRename? argument partialA <;> rfl
  | refineIntro rawValue predicateProof valueIH proofIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [valueIH sigma sigmaResult partialA partialB compat,
        proofIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? rawValue partialA <;>
        cases RawTerm.partialRename? predicateProof partialA <;> rfl
  | refineElim refinedValue refinedIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [refinedIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? refinedValue partialA <;> rfl
  | recordIntro firstField firstIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [firstIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? firstField partialA <;> rfl
  | recordProj recordValue recordIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [recordIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? recordValue partialA <;> rfl
  | codataUnfold initialState transition stateIH transitionIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [stateIH sigma sigmaResult partialA partialB compat,
        transitionIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? initialState partialA <;>
        cases RawTerm.partialRename? transition partialA <;> rfl
  | codataDest codataValue codataIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [codataIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? codataValue partialA <;> rfl
  | sessionSend channel payload channelIH payloadIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [channelIH sigma sigmaResult partialA partialB compat,
        payloadIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? channel partialA <;>
        cases RawTerm.partialRename? payload partialA <;> rfl
  | sessionRecv channel channelIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [channelIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? channel partialA <;> rfl
  | effectPerform operationTag arguments tagIH argumentsIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [tagIH sigma sigmaResult partialA partialB compat,
        argumentsIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? operationTag partialA <;>
        cases RawTerm.partialRename? arguments partialA <;> rfl
  | universeCode innerLevel => intros; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH sigma sigmaResult partialA partialB compat,
        codomainIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? domainCode partialA <;>
        cases RawTerm.partialRename? codomainCode partialA <;> rfl
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH sigma sigmaResult partialA partialB compat,
        codomainIH sigma.lift sigmaResult.lift partialA.lift partialB.lift
          (PartialRawRenaming.lift_subst_compat sigma sigmaResult partialA
            partialB compat)]
      cases RawTerm.partialRename? domainCode partialA <;>
        cases RawTerm.partialRename? codomainCode partialA.lift <;> rfl
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH sigma sigmaResult partialA partialB compat,
        codomainIH sigma.lift sigmaResult.lift partialA.lift partialB.lift
          (PartialRawRenaming.lift_subst_compat sigma sigmaResult partialA
            partialB compat)]
      cases RawTerm.partialRename? domainCode partialA <;>
        cases RawTerm.partialRename? codomainCode partialA.lift <;> rfl
  | productCode firstCode secondCode firstIH secondIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sigma sigmaResult partialA partialB compat,
        secondIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? firstCode partialA <;>
        cases RawTerm.partialRename? secondCode partialA <;> rfl
  | sumCode leftCode rightCode leftIH rightIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sigma sigmaResult partialA partialB compat,
        rightIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? leftCode partialA <;>
        cases RawTerm.partialRename? rightCode partialA <;> rfl
  | listCode elementCode elementIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [elementIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? elementCode partialA <;> rfl
  | optionCode elementCode elementIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [elementIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? elementCode partialA <;> rfl
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sigma sigmaResult partialA partialB compat,
        rightIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? leftCode partialA <;>
        cases RawTerm.partialRename? rightCode partialA <;> rfl
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapThree]
      rw [typeIH sigma sigmaResult partialA partialB compat,
        leftIH sigma sigmaResult partialA partialB compat,
        rightIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? typeCode partialA <;>
        cases RawTerm.partialRename? leftRaw partialA <;>
        cases RawTerm.partialRename? rightRaw partialA <;> rfl
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sigma sigmaResult partialA partialB compat,
        rightIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? leftTypeCode partialA <;>
        cases RawTerm.partialRename? rightTypeCode partialA <;> rfl
  | cumulUpMarker innerCode innerIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [innerIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? innerCode partialA <;> rfl
  | uaToEquiv proofRaw proofIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [proofIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? proofRaw partialA <;> rfl
  | equivApply equivRaw argRaw equivIH argIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [equivIH sigma sigmaResult partialA partialB compat,
        argIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? equivRaw partialA <;>
        cases RawTerm.partialRename? argRaw partialA <;> rfl
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sigma sigmaResult partialA partialB compat,
        rightIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? leftPathRaw partialA <;>
        cases RawTerm.partialRename? rightPathRaw partialA <;> rfl
  | idToEquiv proofRaw proofIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?]
      rw [proofIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? proofRaw partialA <;> rfl
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sigma sigmaResult partialA partialB compat,
        secondIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? firstProof partialA <;>
        cases RawTerm.partialRename? secondProof partialA <;> rfl
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro sigma sigmaResult partialA partialB compat
      dsimp only [RawTerm.subst, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sigma sigmaResult partialA partialB compat,
        secondIH sigma sigmaResult partialA partialB compat]
      cases RawTerm.partialRename? firstEquiv partialA <;>
        cases RawTerm.partialRename? secondEquiv partialA <;> rfl

/-! ## Specialisation: `unweaken?` commutes with `subst` after `lift`. -/

/-- Variable-level compat used to derive `unweaken?_subst_lift_commute`
from the generic `partialRename?_subst_compat`.  Specialises both
partial-renamings to `dropNewest`, the source-substitution to
`sigma.lift`, and the result-substitution to `sigma`. -/
theorem PartialRawRenaming.dropNewest_subst_lift_compat
    {srcA tgtA : Nat} (sigma : RawTermSubst srcA tgtA) :
    ∀ (pos : Fin (srcA + 1)),
      RawTerm.partialRename? (sigma.lift pos)
          PartialRawRenaming.dropNewest =
        (PartialRawRenaming.dropNewest pos).map sigma
  | ⟨0, _⟩ => rfl
  | ⟨index + 1, indexLt⟩ => by
      let posIdx : Fin srcA := ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩
      show RawTerm.partialRename?
              ((sigma posIdx).rename RawRenaming.weaken)
              PartialRawRenaming.dropNewest =
            some (sigma posIdx)
      exact RawTerm.unweaken?_weaken (sigma posIdx)

/-- `RawTerm.unweaken?` commutes with `subst` after lifting under one
binder.  Specialisation of the generic `partialRename?_subst_compat`
with both partial-renamings set to `PartialRawRenaming.dropNewest`,
the source-substitution to `sigma.lift`, and the result-substitution
to `sigma`.

This is the headline lemma the D2.5.5 Blocker-A (#1945) addresses,
unblocking the propositional-premise architecture of #1947 for the
`transpPiBetaSimple` subst-compat cascade. -/
theorem RawTerm.unweaken?_subst_lift_commute {srcA tgtA : Nat}
    (term : RawTerm (srcA + 1)) (sigma : RawTermSubst srcA tgtA) :
    RawTerm.unweaken? (term.subst sigma.lift) =
      (RawTerm.unweaken? term).map (·.subst sigma) := by
  unfold RawTerm.unweaken?
  exact RawTerm.partialRename?_subst_compat term sigma.lift sigma
    PartialRawRenaming.dropNewest PartialRawRenaming.dropNewest
    (PartialRawRenaming.dropNewest_subst_lift_compat sigma)

end LeanFX2
