import LeanFX2.Foundation.Polygraph.PolyTermAction.SubstCommute

/-! # LeanFX2.Foundation.Polygraph.PolyTermAction.ToRawTermRename

K11.13 Phase C-1 — reverse-direction rename commute.

Phase A shipped `(rawTerm.rename rho).toRawPoly =
rawTerm.toRawPoly.rename rho`.  Phase C-1 here ships the reverse:
`(polyTerm.rename rho).toRawTerm = polyTerm.toRawTerm.rename rho`.

* `RawPolyTerm.toRawTerm_rename_commute` headline (73-case induction
  on RawPolyTerm rather than RawTerm).
* `RawPolyTerm.weaken_toRawTerm_commute` weakening corollary.

## Root status

Zero-axiom. -/

/-! ## K11.13 Phase C-1 — reverse-direction rename commute.

The Phase A commute showed that applying a raw renaming commutes with
the `RawTerm → RawPolyTerm` direction of the bijection:
`(rawTerm.rename rho).toRawPoly = rawTerm.toRawPoly.rename rho`.

Phase C-1 (this section) ships the reverse:
`(polyTerm.rename rho).toRawTerm = polyTerm.toRawTerm.rename rho`.

## Why both directions

The typed `PolyTerm.rename` (Phase C-2, follow-up) has 11 raw-in-Ty
constructors whose typed signature embeds the inner subterm's
`RawPolyTerm` payload INSIDE the kernel `Ty` index via
`RawPolyTerm.toRawTerm` (because `Ty` itself is indexed by `RawTerm`,
not `RawPolyTerm`).  Specifically, ctors like `PolyTerm.appPi /
.pair / .snd / .boolElim / .refl / .oeqRefl / .idStrictRefl /
.refineIntro` carry kernel `Ty` indices of the form
`codomainType.subst0 domainType argumentPolyRaw.toRawTerm` — where
the recursive `PolyTerm.rename` call delivers a subterm at
`(argumentPolyRaw.rename rho).toRawTerm` while the outer ctor signature
demands `argumentPolyRaw.toRawTerm.rename rho`.  Phase C-1 is the
bridge that lets each raw-in-Ty cast use a single rewrite at the Ty
level rather than inlining the commute case-by-case.

## Proof template

Identical to Phase A: induct on `polyTerm` with `targetScope`
generalised so binder cases threaded through `rawRenaming.lift`; each
case discharges via `simp only [RawPolyTerm.rename,
RawPolyTerm.toRawTerm, RawTerm.rename]` plus `congrArg{,2,3}` over
the IHs.  Zero-axiom — uses only `congrArg` / `congr` from
Init.Prelude and the structural induction principle.

The naming-discipline difference from Phase A is the bookkeeping
order: induct on `RawPolyTerm` (not `RawTerm`), project via
`RawPolyTerm.toRawTerm` (not `RawTerm.toRawPoly`), and the cong helpers
build `RawTerm.X` targets (not `RawPolyTerm.X`). -/

namespace LeanFX2.Foundation.Polygraph

theorem RawPolyTerm.toRawTerm_rename_commute :
    ∀ {sourceScope targetScope : Nat}
      (polyTerm : RawPolyTerm sourceScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
        (polyTerm.rename rawRenaming).toRawTerm =
          polyTerm.toRawTerm.rename rawRenaming := by
  intro sourceScope targetScope polyTerm
  induction polyTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.lam (bodyIH rawRenaming.lift)
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.app
        (functionIH rawRenaming) (argumentIH rawRenaming)
  | pair firstValue secondValue firstIH secondIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.pair
        (firstIH rawRenaming) (secondIH rawRenaming)
  | fst pairTerm pairIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.fst (pairIH rawRenaming)
  | snd pairTerm pairIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.snd (pairIH rawRenaming)
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.boolElim
        (scrutineeIH rawRenaming) (thenIH rawRenaming)
        (elseIH rawRenaming)
  | natZero => intro _; rfl
  | natSucc predecessor predecessorIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.natSucc (predecessorIH rawRenaming)
  | natElim scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.natElim
        (scrutineeIH rawRenaming) (zeroIH rawRenaming)
        (succIH rawRenaming)
  | natRec scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.natRec
        (scrutineeIH rawRenaming) (zeroIH rawRenaming)
        (succIH rawRenaming)
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.listCons
        (headIH rawRenaming) (tailIH rawRenaming)
  | listElim scrutinee nilBranch consBranch
      scrutineeIH nilIH consIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.listElim
        (scrutineeIH rawRenaming) (nilIH rawRenaming)
        (consIH rawRenaming)
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.optionSome (valueIH rawRenaming)
  | optionMatch scrutinee noneBranch someBranch
      scrutineeIH noneIH someIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.optionMatch
        (scrutineeIH rawRenaming) (noneIH rawRenaming)
        (someIH rawRenaming)
  | eitherInl valueTerm valueIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.eitherInl (valueIH rawRenaming)
  | eitherInr valueTerm valueIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.eitherInr (valueIH rawRenaming)
  | eitherMatch scrutinee leftBranch rightBranch
      scrutineeIH leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.eitherMatch
        (scrutineeIH rawRenaming) (leftIH rawRenaming)
        (rightIH rawRenaming)
  | refl rawWitness witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.refl (witnessIH rawRenaming)
  | idJ baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.idJ
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | modIntro inner innerIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.modIntro (innerIH rawRenaming)
  | modElim inner innerIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.modElim (innerIH rawRenaming)
  | subsume inner innerIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.subsume (innerIH rawRenaming)
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.intervalOpp (intervalIH rawRenaming)
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.intervalMeet
        (leftIH rawRenaming) (rightIH rawRenaming)
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.intervalJoin
        (leftIH rawRenaming) (rightIH rawRenaming)
  | pathLam body bodyIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.pathLam (bodyIH rawRenaming.lift)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.pathApp
        (pathIH rawRenaming) (intervalIH rawRenaming)
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.glueIntro
        (baseIH rawRenaming) (partialIH rawRenaming)
  | glueElim gluedValue gluedIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.glueElim (gluedIH rawRenaming)
  | transp path source pathIH sourceIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.transp
        (pathIH rawRenaming) (sourceIH rawRenaming)
  | hcomp sides cap sidesIH capIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.hcomp
        (sidesIH rawRenaming) (capIH rawRenaming)
  | oeqRefl witness witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.oeqRefl (witnessIH rawRenaming)
  | oeqJ baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.oeqJ
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.oeqFunext (pointwiseIH rawRenaming)
  | idStrictRefl witness witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.idStrictRefl (witnessIH rawRenaming)
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.idStrictRec
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivIntro
        (forwardIH rawRenaming) (backwardIH rawRenaming)
  | equivApp equivTerm argument equivIH argumentIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivApp
        (equivIH rawRenaming) (argumentIH rawRenaming)
  | refineIntro rawValue predicateProof rawIH proofIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.refineIntro
        (rawIH rawRenaming) (proofIH rawRenaming)
  | refineElim refinedValue refinedIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.refineElim (refinedIH rawRenaming)
  | recordIntro firstField firstIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.recordIntro (firstIH rawRenaming)
  | recordProj recordValue recordIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.recordProj (recordIH rawRenaming)
  | codataUnfold initialState transition initialIH transitionIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.codataUnfold
        (initialIH rawRenaming) (transitionIH rawRenaming)
  | codataDest codataValue codataIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.codataDest (codataIH rawRenaming)
  | sessionSend channel payload channelIH payloadIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.sessionSend
        (channelIH rawRenaming) (payloadIH rawRenaming)
  | sessionRecv channel channelIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.sessionRecv (channelIH rawRenaming)
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.effectPerform
        (operationIH rawRenaming) (argumentsIH rawRenaming)
  | universeCode innerLevel => intro _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.arrowCode
        (domainIH rawRenaming) (codomainIH rawRenaming)
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.piTyCode
        (domainIH rawRenaming) (codomainIH rawRenaming.lift)
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.sigmaTyCode
        (domainIH rawRenaming) (codomainIH rawRenaming.lift)
  | productCode firstCode secondCode firstIH secondIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.productCode
        (firstIH rawRenaming) (secondIH rawRenaming)
  | sumCode leftCode rightCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.sumCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | listCode elementCode elementIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.listCode (elementIH rawRenaming)
  | optionCode elementCode elementIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.optionCode (elementIH rawRenaming)
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.eitherCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.idCode
        (typeIH rawRenaming) (leftIH rawRenaming) (rightIH rawRenaming)
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | cumulUpMarker innerCodeRaw innerIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.cumulUpMarker (innerIH rawRenaming)
  | uaToEquiv proofRaw proofIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.uaToEquiv (proofIH rawRenaming)
  | equivApply equivRaw argRaw equivIH argIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivApply
        (equivIH rawRenaming) (argIH rawRenaming)
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.pathCompose
        (leftIH rawRenaming) (rightIH rawRenaming)
  | idToEquiv proofRaw proofIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.idToEquiv (proofIH rawRenaming)
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.oeqTrans
        (firstIH rawRenaming) (secondIH rawRenaming)
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivCompose
        (firstIH rawRenaming) (secondIH rawRenaming)

/-- Corollary: weakening commutes with `toRawTerm`. -/
theorem RawPolyTerm.weaken_toRawTerm_commute {scope : Nat}
    (polyTerm : RawPolyTerm scope) :
    polyTerm.weaken.toRawTerm =
      (polyTerm.toRawTerm : RawTerm scope).weaken :=
  RawPolyTerm.toRawTerm_rename_commute polyTerm RawRenaming.weaken


end LeanFX2.Foundation.Polygraph
