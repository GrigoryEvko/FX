import LeanFX2.Foundation.Polygraph.PolyTermAction.ToRawTermRename

/-! # LeanFX2.Foundation.Polygraph.PolyTermAction.ToRawTermSubst

K11.13 Phase C-1S — reverse-direction subst commute.

The substitution analog of Phase C-1:
`(polyTerm.subst sigma).toRawTerm = polyTerm.toRawTerm.subst sigma.toRawTermSubst`.

* `RawPolyTermSubst.toRawTermSubst` pointwise converter.
* `RawPolyTermSubst.lift_toRawTermSubst_commute` lift commute.
* `RawPolyTerm.toRawTerm_subst_commute` headline (73-case induction).
* `RawPolyTerm.subst0_toRawTerm_commute` single-binder corollary.

## Root status

Zero-axiom. -/

namespace LeanFX2.Foundation.Polygraph

/-! ## K11.13 Phase C-1S — reverse-direction subst commute.

Mirrors Phase C-1's `RawPolyTerm.toRawTerm_rename_commute` for the
substitution direction.  Where Phase C-1 said
`(polyTerm.rename rho).toRawTerm = polyTerm.toRawTerm.rename rho`,
Phase C-1S says
`(polyTerm.subst sigma).toRawTerm = polyTerm.toRawTerm.subst sigma.toRawTermSubst`.

Needs a `RawPolyTermSubst → RawTermSubst` converter, then mirrors the
73-case structural induction of Phase C-1 with `subst` / `RawTerm.subst`
in place of `rename` / `RawTerm.rename`. -/

/-- Pointwise converter: a `RawPolyTermSubst` becomes a `RawTermSubst`
by projecting each substituent through `RawPolyTerm.toRawTerm`. -/
@[reducible] def RawPolyTermSubst.toRawTermSubst {source target : Nat}
    (substitution : RawPolyTermSubst source target) :
    RawTermSubst source target :=
  fun position => (substitution position).toRawTerm

/-- `lift` commutes with the cross-layer converter pointwise.  Succ
case uses Phase C-1's `RawPolyTerm.toRawTerm_rename_commute` to bridge
`(σ k).rename weaken |>.toRawTerm = (σ k).toRawTerm.rename weaken`. -/
theorem RawPolyTermSubst.lift_toRawTermSubst_commute
    {sourceScope targetScope : Nat}
    (substitution : RawPolyTermSubst sourceScope targetScope) :
    ∀ position,
      (substitution.lift position).toRawTerm =
        substitution.toRawTermSubst.lift position
  | ⟨0, _⟩     => rfl
  | ⟨k + 1, h⟩ => by
      simp only [RawPolyTermSubst.toRawTermSubst, RawPolyTermSubst.lift,
                 RawTermSubst.lift]
      exact RawPolyTerm.toRawTerm_rename_commute
        (substitution ⟨k, Nat.lt_of_succ_lt_succ h⟩) RawRenaming.weaken

/-- K11.13 Phase C-1S headline: `RawPolyTerm.toRawTerm` commutes with
`RawPolyTerm.subst`.  73-case structural induction mirroring Phase C-1;
binder cases (lam, pathLam, piTyCode, sigmaTyCode) use the lift commute
to bridge `substitution.lift.toRawTermSubst` against
`substitution.toRawTermSubst.lift`. -/
theorem RawPolyTerm.toRawTerm_subst_commute :
    ∀ {sourceScope targetScope : Nat}
      (polyTerm : RawPolyTerm sourceScope)
      (substitution : RawPolyTermSubst sourceScope targetScope),
        (polyTerm.subst substitution).toRawTerm =
          polyTerm.toRawTerm.subst substitution.toRawTermSubst := by
  intro sourceScope targetScope polyTerm
  induction polyTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      have liftedCommute := bodyIH substitution.lift
      rw [liftedCommute]
      exact congrArg RawTerm.lam
        (RawTerm.subst_pointwise
          (RawPolyTermSubst.lift_toRawTermSubst_commute substitution) _)
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.app
        (functionIH substitution) (argumentIH substitution)
  | pair firstValue secondValue firstIH secondIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.pair
        (firstIH substitution) (secondIH substitution)
  | fst pairTerm pairIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.fst (pairIH substitution)
  | snd pairTerm pairIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.snd (pairIH substitution)
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.boolElim
        (scrutineeIH substitution) (thenIH substitution)
        (elseIH substitution)
  | natZero => intro _; rfl
  | natSucc predecessor predecessorIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.natSucc (predecessorIH substitution)
  | natElim scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.natElim
        (scrutineeIH substitution) (zeroIH substitution)
        (succIH substitution)
  | natRec scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.natRec
        (scrutineeIH substitution) (zeroIH substitution)
        (succIH substitution)
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.listCons
        (headIH substitution) (tailIH substitution)
  | listElim scrutinee nilBranch consBranch
      scrutineeIH nilIH consIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.listElim
        (scrutineeIH substitution) (nilIH substitution)
        (consIH substitution)
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.optionSome (valueIH substitution)
  | optionMatch scrutinee noneBranch someBranch
      scrutineeIH noneIH someIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.optionMatch
        (scrutineeIH substitution) (noneIH substitution)
        (someIH substitution)
  | eitherInl valueTerm valueIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.eitherInl (valueIH substitution)
  | eitherInr valueTerm valueIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.eitherInr (valueIH substitution)
  | eitherMatch scrutinee leftBranch rightBranch
      scrutineeIH leftIH rightIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.eitherMatch
        (scrutineeIH substitution) (leftIH substitution)
        (rightIH substitution)
  | refl rawWitness witnessIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.refl (witnessIH substitution)
  | idJ baseCase witness baseIH witnessIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.idJ
        (baseIH substitution) (witnessIH substitution)
  | modIntro inner innerIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.modIntro (innerIH substitution)
  | modElim inner innerIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.modElim (innerIH substitution)
  | subsume inner innerIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.subsume (innerIH substitution)
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.intervalOpp (intervalIH substitution)
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.intervalMeet
        (leftIH substitution) (rightIH substitution)
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.intervalJoin
        (leftIH substitution) (rightIH substitution)
  | pathLam body bodyIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      have liftedCommute := bodyIH substitution.lift
      rw [liftedCommute]
      exact congrArg RawTerm.pathLam
        (RawTerm.subst_pointwise
          (RawPolyTermSubst.lift_toRawTermSubst_commute substitution) _)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.pathApp
        (pathIH substitution) (intervalIH substitution)
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.glueIntro
        (baseIH substitution) (partialIH substitution)
  | glueElim gluedValue gluedIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.glueElim (gluedIH substitution)
  | transp path source pathIH sourceIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.transp
        (pathIH substitution) (sourceIH substitution)
  | transpFill path interval source pathIH intervalIH sourceIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.transpFill
        (pathIH substitution) (intervalIH substitution) (sourceIH substitution)
  | hcomp sides cap sidesIH capIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.hcomp
        (sidesIH substitution) (capIH substitution)
  | oeqRefl witness witnessIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.oeqRefl (witnessIH substitution)
  | oeqJ baseCase witness baseIH witnessIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.oeqJ
        (baseIH substitution) (witnessIH substitution)
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.oeqFunext (pointwiseIH substitution)
  | idStrictRefl witness witnessIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.idStrictRefl (witnessIH substitution)
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.idStrictRec
        (baseIH substitution) (witnessIH substitution)
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivIntro
        (forwardIH substitution) (backwardIH substitution)
  | equivApp equivTerm argument equivIH argumentIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivApp
        (equivIH substitution) (argumentIH substitution)
  | refineIntro rawValue predicateProof rawIH proofIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.refineIntro
        (rawIH substitution) (proofIH substitution)
  | refineElim refinedValue refinedIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.refineElim (refinedIH substitution)
  | recordIntro firstField firstIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.recordIntro (firstIH substitution)
  | recordProj recordValue recordIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.recordProj (recordIH substitution)
  | codataUnfold initialState transition initialIH transitionIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.codataUnfold
        (initialIH substitution) (transitionIH substitution)
  | codataDest codataValue codataIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.codataDest (codataIH substitution)
  | sessionSend channel payload channelIH payloadIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.sessionSend
        (channelIH substitution) (payloadIH substitution)
  | sessionRecv channel channelIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.sessionRecv (channelIH substitution)
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.effectPerform
        (operationIH substitution) (argumentsIH substitution)
  | universeCode innerLevel => intro _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.arrowCode
        (domainIH substitution) (codomainIH substitution)
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      have liftedCommute := codomainIH substitution.lift
      rw [liftedCommute]
      exact LeanFX2.congrArg2 RawTerm.piTyCode (domainIH substitution)
        (RawTerm.subst_pointwise
          (RawPolyTermSubst.lift_toRawTermSubst_commute substitution) _)
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      have liftedCommute := codomainIH substitution.lift
      rw [liftedCommute]
      exact LeanFX2.congrArg2 RawTerm.sigmaTyCode (domainIH substitution)
        (RawTerm.subst_pointwise
          (RawPolyTermSubst.lift_toRawTermSubst_commute substitution) _)
  | productCode firstCode secondCode firstIH secondIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.productCode
        (firstIH substitution) (secondIH substitution)
  | sumCode leftCode rightCode leftIH rightIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.sumCode
        (leftIH substitution) (rightIH substitution)
  | listCode elementCode elementIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.listCode (elementIH substitution)
  | optionCode elementCode elementIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.optionCode (elementIH substitution)
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.eitherCode
        (leftIH substitution) (rightIH substitution)
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.idCode
        (typeIH substitution) (leftIH substitution) (rightIH substitution)
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivCode
        (leftIH substitution) (rightIH substitution)
  | cumulUpMarker innerCodeRaw innerIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.cumulUpMarker (innerIH substitution)
  | uaToEquiv proofRaw proofIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.uaToEquiv (proofIH substitution)
  | equivApply equivRaw argRaw equivIH argIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivApply
        (equivIH substitution) (argIH substitution)
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.pathCompose
        (leftIH substitution) (rightIH substitution)
  | idToEquiv proofRaw proofIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.idToEquiv (proofIH substitution)
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.oeqTrans
        (firstIH substitution) (secondIH substitution)
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro substitution
      dsimp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivCompose
        (firstIH substitution) (secondIH substitution)

/-- Corollary: singleton substitution commutes with `toRawTerm`. -/
theorem RawPolyTerm.subst0_toRawTerm_commute {scope : Nat}
    (body : RawPolyTerm (scope + 1)) (rawArg : RawPolyTerm scope) :
    (body.subst (RawPolyTermSubst.singleton rawArg)).toRawTerm =
      body.toRawTerm.subst (RawTermSubst.singleton rawArg.toRawTerm) := by
  rw [RawPolyTerm.toRawTerm_subst_commute body
        (RawPolyTermSubst.singleton rawArg)]
  refine RawTerm.subst_pointwise ?_ body.toRawTerm
  intro position
  rcases position with ⟨n, hn⟩
  cases n with
  | zero => rfl
  | succ k => rfl


end LeanFX2.Foundation.Polygraph
