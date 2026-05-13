import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.Polygraph.PolyTerm

/-! # LeanFX2.Foundation.Polygraph.PolyTermAction.RawPolyTermRename

K11.13 Phase A — raw-layer rename + commute.

* `RawPolyTerm.rename` (73-case structural recursion mirroring
  `RawTerm.rename`).
* `@[reducible] RawPolyTerm.weaken` single-binder weakening shim.
* `RawTerm.rename_toRawPoly_commute` headline commute lemma
  (the K11.13 Phase A workhorse).
* `RawTerm.weaken_toRawPoly_commute` weakening corollary.

## Root status

Zero-axiom. Verified by the shipping audit gates on the parent file. -/

namespace LeanFX2.Foundation.Polygraph

open LeanFX2

/-- Apply a raw renaming to a `RawPolyTerm`.  Mirrors `RawTerm.rename`
(73 cases) constructor-for-constructor; binder constructors (`lam`,
`pathLam`, `piTyCode`, `sigmaTyCode`) recurse with `rawRenaming.lift`
on the body.  Structural recursion is total since every recursive
call descends on a constructor argument. -/
def RawPolyTerm.rename : ∀ {sourceScope targetScope : Nat},
    RawPolyTerm sourceScope → RawRenaming sourceScope targetScope →
    RawPolyTerm targetScope
  | _, _, .var position, rawRenaming => .var (rawRenaming position)
  | _, _, .unit, _ => .unit
  | _, _, .lam body, rawRenaming =>
      .lam (body.rename rawRenaming.lift)
  | _, _, .app functionTerm argumentTerm, rawRenaming =>
      .app (functionTerm.rename rawRenaming)
           (argumentTerm.rename rawRenaming)
  | _, _, .pair firstValue secondValue, rawRenaming =>
      .pair (firstValue.rename rawRenaming)
            (secondValue.rename rawRenaming)
  | _, _, .fst pairTerm, rawRenaming => .fst (pairTerm.rename rawRenaming)
  | _, _, .snd pairTerm, rawRenaming => .snd (pairTerm.rename rawRenaming)
  | _, _, .boolTrue, _ => .boolTrue
  | _, _, .boolFalse, _ => .boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch, rawRenaming =>
      .boolElim (scrutinee.rename rawRenaming)
                (thenBranch.rename rawRenaming)
                (elseBranch.rename rawRenaming)
  | _, _, .natZero, _ => .natZero
  | _, _, .natSucc predecessor, rawRenaming =>
      .natSucc (predecessor.rename rawRenaming)
  | _, _, .natElim scrutinee zeroBranch succBranch, rawRenaming =>
      .natElim (scrutinee.rename rawRenaming)
               (zeroBranch.rename rawRenaming)
               (succBranch.rename rawRenaming)
  | _, _, .natRec scrutinee zeroBranch succBranch, rawRenaming =>
      .natRec (scrutinee.rename rawRenaming)
              (zeroBranch.rename rawRenaming)
              (succBranch.rename rawRenaming)
  | _, _, .listNil, _ => .listNil
  | _, _, .listCons headTerm tailTerm, rawRenaming =>
      .listCons (headTerm.rename rawRenaming)
                (tailTerm.rename rawRenaming)
  | _, _, .listElim scrutinee nilBranch consBranch, rawRenaming =>
      .listElim (scrutinee.rename rawRenaming)
                (nilBranch.rename rawRenaming)
                (consBranch.rename rawRenaming)
  | _, _, .optionNone, _ => .optionNone
  | _, _, .optionSome valueTerm, rawRenaming =>
      .optionSome (valueTerm.rename rawRenaming)
  | _, _, .optionMatch scrutinee noneBranch someBranch, rawRenaming =>
      .optionMatch (scrutinee.rename rawRenaming)
                   (noneBranch.rename rawRenaming)
                   (someBranch.rename rawRenaming)
  | _, _, .eitherInl valueTerm, rawRenaming =>
      .eitherInl (valueTerm.rename rawRenaming)
  | _, _, .eitherInr valueTerm, rawRenaming =>
      .eitherInr (valueTerm.rename rawRenaming)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch, rawRenaming =>
      .eitherMatch (scrutinee.rename rawRenaming)
                   (leftBranch.rename rawRenaming)
                   (rightBranch.rename rawRenaming)
  | _, _, .refl rawWitness, rawRenaming =>
      .refl (rawWitness.rename rawRenaming)
  | _, _, .idJ baseCase witness, rawRenaming =>
      .idJ (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  | _, _, .modIntro raw, rawRenaming =>
      .modIntro (raw.rename rawRenaming)
  | _, _, .modElim raw, rawRenaming =>
      .modElim (raw.rename rawRenaming)
  | _, _, .subsume raw, rawRenaming =>
      .subsume (raw.rename rawRenaming)
  | _, _, .interval0, _ => .interval0
  | _, _, .interval1, _ => .interval1
  | _, _, .intervalOpp intervalTerm, rawRenaming =>
      .intervalOpp (intervalTerm.rename rawRenaming)
  | _, _, .intervalMeet leftInterval rightInterval, rawRenaming =>
      .intervalMeet (leftInterval.rename rawRenaming)
                    (rightInterval.rename rawRenaming)
  | _, _, .intervalJoin leftInterval rightInterval, rawRenaming =>
      .intervalJoin (leftInterval.rename rawRenaming)
                    (rightInterval.rename rawRenaming)
  | _, _, .pathLam body, rawRenaming =>
      .pathLam (body.rename rawRenaming.lift)
  | _, _, .pathApp pathTerm intervalArg, rawRenaming =>
      .pathApp (pathTerm.rename rawRenaming)
               (intervalArg.rename rawRenaming)
  | _, _, .glueIntro baseValue partialValue, rawRenaming =>
      .glueIntro (baseValue.rename rawRenaming)
                 (partialValue.rename rawRenaming)
  | _, _, .glueElim gluedValue, rawRenaming =>
      .glueElim (gluedValue.rename rawRenaming)
  | _, _, .transp path source, rawRenaming =>
      .transp (path.rename rawRenaming) (source.rename rawRenaming)
  | _, _, .hcomp sides cap, rawRenaming =>
      .hcomp (sides.rename rawRenaming) (cap.rename rawRenaming)
  | _, _, .oeqRefl witness, rawRenaming =>
      .oeqRefl (witness.rename rawRenaming)
  | _, _, .oeqJ baseCase witness, rawRenaming =>
      .oeqJ (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  | _, _, .oeqFunext pointwiseEquality, rawRenaming =>
      .oeqFunext (pointwiseEquality.rename rawRenaming)
  | _, _, .idStrictRefl witness, rawRenaming =>
      .idStrictRefl (witness.rename rawRenaming)
  | _, _, .idStrictRec baseCase witness, rawRenaming =>
      .idStrictRec (baseCase.rename rawRenaming)
                   (witness.rename rawRenaming)
  | _, _, .equivIntro forwardFn backwardFn, rawRenaming =>
      .equivIntro (forwardFn.rename rawRenaming)
                  (backwardFn.rename rawRenaming)
  | _, _, .equivApp equivTerm argument, rawRenaming =>
      .equivApp (equivTerm.rename rawRenaming)
                (argument.rename rawRenaming)
  | _, _, .refineIntro rawValue predicateProof, rawRenaming =>
      .refineIntro (rawValue.rename rawRenaming)
                   (predicateProof.rename rawRenaming)
  | _, _, .refineElim refinedValue, rawRenaming =>
      .refineElim (refinedValue.rename rawRenaming)
  | _, _, .recordIntro firstField, rawRenaming =>
      .recordIntro (firstField.rename rawRenaming)
  | _, _, .recordProj recordValue, rawRenaming =>
      .recordProj (recordValue.rename rawRenaming)
  | _, _, .codataUnfold initialState transition, rawRenaming =>
      .codataUnfold (initialState.rename rawRenaming)
                    (transition.rename rawRenaming)
  | _, _, .codataDest codataValue, rawRenaming =>
      .codataDest (codataValue.rename rawRenaming)
  | _, _, .sessionSend channel payload, rawRenaming =>
      .sessionSend (channel.rename rawRenaming)
                   (payload.rename rawRenaming)
  | _, _, .sessionRecv channel, rawRenaming =>
      .sessionRecv (channel.rename rawRenaming)
  | _, _, .effectPerform operationTag arguments, rawRenaming =>
      .effectPerform (operationTag.rename rawRenaming)
                     (arguments.rename rawRenaming)
  -- Universe code carries a level Nat only, no Fin-indexed payload.
  | _, _, .universeCode innerLevel, _ => .universeCode innerLevel
  -- Per-shape type codes (CUMUL-2.1).
  | _, _, .arrowCode domainCode codomainCode, rawRenaming =>
      .arrowCode (domainCode.rename rawRenaming)
                 (codomainCode.rename rawRenaming)
  | _, _, .piTyCode domainCode codomainCode, rawRenaming =>
      .piTyCode (domainCode.rename rawRenaming)
                (codomainCode.rename rawRenaming.lift)
  | _, _, .sigmaTyCode domainCode codomainCode, rawRenaming =>
      .sigmaTyCode (domainCode.rename rawRenaming)
                   (codomainCode.rename rawRenaming.lift)
  | _, _, .productCode firstCode secondCode, rawRenaming =>
      .productCode (firstCode.rename rawRenaming)
                   (secondCode.rename rawRenaming)
  | _, _, .sumCode leftCode rightCode, rawRenaming =>
      .sumCode (leftCode.rename rawRenaming)
               (rightCode.rename rawRenaming)
  | _, _, .listCode elementCode, rawRenaming =>
      .listCode (elementCode.rename rawRenaming)
  | _, _, .optionCode elementCode, rawRenaming =>
      .optionCode (elementCode.rename rawRenaming)
  | _, _, .eitherCode leftCode rightCode, rawRenaming =>
      .eitherCode (leftCode.rename rawRenaming)
                  (rightCode.rename rawRenaming)
  | _, _, .idCode typeCode leftRaw rightRaw, rawRenaming =>
      .idCode (typeCode.rename rawRenaming)
              (leftRaw.rename rawRenaming)
              (rightRaw.rename rawRenaming)
  | _, _, .equivCode leftTypeCode rightTypeCode, rawRenaming =>
      .equivCode (leftTypeCode.rename rawRenaming)
                 (rightTypeCode.rename rawRenaming)
  | _, _, .cumulUpMarker innerCodeRaw, rawRenaming =>
      .cumulUpMarker (innerCodeRaw.rename rawRenaming)
  -- D3.6-P1 uaToEquiv.
  | _, _, .uaToEquiv proofRaw, rawRenaming =>
      .uaToEquiv (proofRaw.rename rawRenaming)
  -- D3.6-P2 equivApply.
  | _, _, .equivApply equivRaw argRaw, rawRenaming =>
      .equivApply (equivRaw.rename rawRenaming)
                  (argRaw.rename rawRenaming)
  -- D3.6-S3 pathCompose.
  | _, _, .pathCompose leftPathRaw rightPathRaw, rawRenaming =>
      .pathCompose (leftPathRaw.rename rawRenaming)
                   (rightPathRaw.rename rawRenaming)
  -- D3.6-S4 idToEquiv.
  | _, _, .idToEquiv proofRaw, rawRenaming =>
      .idToEquiv (proofRaw.rename rawRenaming)
  -- D3.6-S5 oeqTrans.
  | _, _, .oeqTrans firstProof secondProof, rawRenaming =>
      .oeqTrans (firstProof.rename rawRenaming)
                (secondProof.rename rawRenaming)
  -- D3.6-S5 equivCompose.
  | _, _, .equivCompose firstEquiv secondEquiv, rawRenaming =>
      .equivCompose (firstEquiv.rename rawRenaming)
                    (secondEquiv.rename rawRenaming)

/-- Single-binder weakening on a `RawPolyTerm`.  Mirrors
`RawTerm.weaken`.  Marked `@[reducible]` for the same reason
`RawTerm.weaken` is — downstream Term-level ctor signatures may
reference this through definitional equalities. -/
@[reducible] def RawPolyTerm.weaken {scope : Nat}
    (polyRaw : RawPolyTerm scope) : RawPolyTerm (scope + 1) :=
  polyRaw.rename RawRenaming.weaken

end LeanFX2.Foundation.Polygraph

namespace LeanFX2

open LeanFX2.Foundation.Polygraph

/-- Local 1-argument congruence — `f a = f a'` from `a = a'`.
Zero-axiom: `congrArg` is from Init.Prelude. -/
theorem congrArgLam {scope : Nat}
    {leftBody rightBody : RawPolyTerm (scope + 1)}
    (bodyEq : leftBody = rightBody) :
    (RawPolyTerm.lam leftBody : RawPolyTerm scope) =
      RawPolyTerm.lam rightBody :=
  congrArg RawPolyTerm.lam bodyEq

/-- Local 2-argument congruence for `RawPolyTerm` constructors.  Zero-
axiom: built from `congrArg` and `congr` (Init.Prelude). -/
theorem congrArg2 {alpha beta gamma : Sort _}
    (functionMap : alpha → beta → gamma)
    {leftFirst rightFirst : alpha}
    {leftSecond rightSecond : beta}
    (firstEq : leftFirst = rightFirst)
    (secondEq : leftSecond = rightSecond) :
    functionMap leftFirst leftSecond =
      functionMap rightFirst rightSecond :=
  congr (congrArg functionMap firstEq) secondEq

/-- Local 3-argument congruence for `RawPolyTerm` constructors.
Zero-axiom: composes `congrArg2` with `congr`. -/
theorem congrArg3 {alpha beta gamma delta : Sort _}
    (functionMap : alpha → beta → gamma → delta)
    {leftFirst rightFirst : alpha}
    {leftSecond rightSecond : beta}
    {leftThird rightThird : gamma}
    (firstEq : leftFirst = rightFirst)
    (secondEq : leftSecond = rightSecond)
    (thirdEq : leftThird = rightThird) :
    functionMap leftFirst leftSecond leftThird =
      functionMap rightFirst rightSecond rightThird :=
  congr (congrArg2 functionMap firstEq secondEq) thirdEq

/-- The K11.13 Phase A headline commute lemma: applying a raw
renaming and then converting to `RawPolyTerm` is the same as
converting to `RawPolyTerm` and then applying the renaming there.
Structural induction on `rawTerm` with `targetScope` generalised (so
the IH for binder cases accepts `rawRenaming.lift`).  Every case
discharges by `simp only [RawTerm.rename, RawTerm.toRawPoly,
RawPolyTerm.rename]` followed by `congrArg{,2,3}` applied to the
inductive hypotheses. -/
theorem RawTerm.rename_toRawPoly_commute :
    ∀ {sourceScope targetScope : Nat}
      (rawTerm : RawTerm sourceScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
        (rawTerm.rename rawRenaming).toRawPoly =
          rawTerm.toRawPoly.rename rawRenaming := by
  intro sourceScope targetScope rawTerm
  induction rawTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArgLam (bodyIH rawRenaming.lift)
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.app
        (functionIH rawRenaming) (argumentIH rawRenaming)
  | pair firstValue secondValue firstIH secondIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.pair
        (firstIH rawRenaming) (secondIH rawRenaming)
  | fst pairTerm pairIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.fst (pairIH rawRenaming)
  | snd pairTerm pairIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.snd (pairIH rawRenaming)
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.boolElim
        (scrutineeIH rawRenaming) (thenIH rawRenaming)
        (elseIH rawRenaming)
  | natZero => intro _; rfl
  | natSucc predecessor predecessorIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.natSucc (predecessorIH rawRenaming)
  | natElim scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.natElim
        (scrutineeIH rawRenaming) (zeroIH rawRenaming)
        (succIH rawRenaming)
  | natRec scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.natRec
        (scrutineeIH rawRenaming) (zeroIH rawRenaming)
        (succIH rawRenaming)
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.listCons
        (headIH rawRenaming) (tailIH rawRenaming)
  | listElim scrutinee nilBranch consBranch
      scrutineeIH nilIH consIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.listElim
        (scrutineeIH rawRenaming) (nilIH rawRenaming)
        (consIH rawRenaming)
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.optionSome (valueIH rawRenaming)
  | optionMatch scrutinee noneBranch someBranch
      scrutineeIH noneIH someIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.optionMatch
        (scrutineeIH rawRenaming) (noneIH rawRenaming)
        (someIH rawRenaming)
  | eitherInl valueTerm valueIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.eitherInl (valueIH rawRenaming)
  | eitherInr valueTerm valueIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.eitherInr (valueIH rawRenaming)
  | eitherMatch scrutinee leftBranch rightBranch
      scrutineeIH leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.eitherMatch
        (scrutineeIH rawRenaming) (leftIH rawRenaming)
        (rightIH rawRenaming)
  | refl rawWitness witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.refl (witnessIH rawRenaming)
  | idJ baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.idJ
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | modIntro inner innerIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.modIntro (innerIH rawRenaming)
  | modElim inner innerIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.modElim (innerIH rawRenaming)
  | subsume inner innerIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.subsume (innerIH rawRenaming)
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.intervalOpp (intervalIH rawRenaming)
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.intervalMeet
        (leftIH rawRenaming) (rightIH rawRenaming)
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.intervalJoin
        (leftIH rawRenaming) (rightIH rawRenaming)
  | pathLam body bodyIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.pathLam (bodyIH rawRenaming.lift)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.pathApp
        (pathIH rawRenaming) (intervalIH rawRenaming)
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.glueIntro
        (baseIH rawRenaming) (partialIH rawRenaming)
  | glueElim gluedValue gluedIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.glueElim (gluedIH rawRenaming)
  | transp path source pathIH sourceIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.transp
        (pathIH rawRenaming) (sourceIH rawRenaming)
  | hcomp sides cap sidesIH capIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.hcomp
        (sidesIH rawRenaming) (capIH rawRenaming)
  | oeqRefl witness witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.oeqRefl (witnessIH rawRenaming)
  | oeqJ baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.oeqJ
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.oeqFunext (pointwiseIH rawRenaming)
  | idStrictRefl witness witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.idStrictRefl (witnessIH rawRenaming)
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.idStrictRec
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivIntro
        (forwardIH rawRenaming) (backwardIH rawRenaming)
  | equivApp equivTerm argument equivIH argumentIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivApp
        (equivIH rawRenaming) (argumentIH rawRenaming)
  | refineIntro rawValue predicateProof rawIH proofIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.refineIntro
        (rawIH rawRenaming) (proofIH rawRenaming)
  | refineElim refinedValue refinedIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.refineElim (refinedIH rawRenaming)
  | recordIntro firstField firstIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.recordIntro (firstIH rawRenaming)
  | recordProj recordValue recordIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.recordProj (recordIH rawRenaming)
  | codataUnfold initialState transition initialIH transitionIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.codataUnfold
        (initialIH rawRenaming) (transitionIH rawRenaming)
  | codataDest codataValue codataIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.codataDest (codataIH rawRenaming)
  | sessionSend channel payload channelIH payloadIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.sessionSend
        (channelIH rawRenaming) (payloadIH rawRenaming)
  | sessionRecv channel channelIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.sessionRecv (channelIH rawRenaming)
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.effectPerform
        (operationIH rawRenaming) (argumentsIH rawRenaming)
  | universeCode innerLevel => intro _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.arrowCode
        (domainIH rawRenaming) (codomainIH rawRenaming)
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.piTyCode
        (domainIH rawRenaming) (codomainIH rawRenaming.lift)
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.sigmaTyCode
        (domainIH rawRenaming) (codomainIH rawRenaming.lift)
  | productCode firstCode secondCode firstIH secondIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.productCode
        (firstIH rawRenaming) (secondIH rawRenaming)
  | sumCode leftCode rightCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.sumCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | listCode elementCode elementIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.listCode (elementIH rawRenaming)
  | optionCode elementCode elementIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.optionCode (elementIH rawRenaming)
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.eitherCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.idCode
        (typeIH rawRenaming) (leftIH rawRenaming) (rightIH rawRenaming)
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | cumulUpMarker innerCodeRaw innerIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.cumulUpMarker (innerIH rawRenaming)
  | uaToEquiv proofRaw proofIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.uaToEquiv (proofIH rawRenaming)
  | equivApply equivRaw argRaw equivIH argIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivApply
        (equivIH rawRenaming) (argIH rawRenaming)
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.pathCompose
        (leftIH rawRenaming) (rightIH rawRenaming)
  | idToEquiv proofRaw proofIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.idToEquiv (proofIH rawRenaming)
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.oeqTrans
        (firstIH rawRenaming) (secondIH rawRenaming)
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivCompose
        (firstIH rawRenaming) (secondIH rawRenaming)

/-- Corollary: weakening commutes with `toRawPoly`. -/
theorem RawTerm.weaken_toRawPoly_commute {scope : Nat}
    (rawTerm : RawTerm scope) :
    rawTerm.weaken.toRawPoly =
      (rawTerm.toRawPoly : RawPolyTerm scope).weaken :=
  RawTerm.rename_toRawPoly_commute rawTerm RawRenaming.weaken

end LeanFX2
