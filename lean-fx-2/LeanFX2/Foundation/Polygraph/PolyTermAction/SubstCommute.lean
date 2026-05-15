import LeanFX2.Foundation.Polygraph.PolyTermAction.RawPolyTermSubst

/-! # LeanFX2.Foundation.Polygraph.PolyTermAction.SubstCommute

K11.13 Phase B continued — pointwise lemmas + cross-layer converter
+ headline subst commute.

* `RawPolyTermSubst.lift_pointwise` and `RawPolyTerm.subst_pointwise`
  (pointwise equality respect).
* `RawTermSubst.toRawPolySubst` cross-layer converter and the
  `RawTermSubst.lift_toRawPolySubst_commute` lift commute.
* `RawTerm.subst_toRawPoly_commute` — the K11.13 Phase B headline
  (73-case structural induction).
* `RawTerm.subst0_toRawPoly_commute` corollary.

## Root status

Zero-axiom. -/

namespace LeanFX2.Foundation.Polygraph

/-- Lift respects pointwise equality. -/
theorem RawPolyTermSubst.lift_pointwise {sourceScope targetScope : Nat}
    {substitution1 substitution2 : RawPolyTermSubst sourceScope targetScope}
    (substEq : ∀ position, substitution1 position = substitution2 position) :
    ∀ position, substitution1.lift position = substitution2.lift position
  | ⟨0, _⟩     => rfl
  | ⟨k + 1, h⟩ => by
      simp only [RawPolyTermSubst.lift]
      rw [substEq ⟨k, Nat.lt_of_succ_lt_succ h⟩]

/-- `RawPolyTerm.subst` respects pointwise substitution equality. -/
theorem RawPolyTerm.subst_pointwise {sourceScope targetScope : Nat}
    {substitution1 substitution2 : RawPolyTermSubst sourceScope targetScope}
    (substEq : ∀ position, substitution1 position = substitution2 position) :
    ∀ (polyTerm : RawPolyTerm sourceScope),
      polyTerm.subst substitution1 = polyTerm.subst substitution2 := by
  intro polyTerm
  induction polyTerm generalizing targetScope with
  | var position =>
      simp only [RawPolyTerm.subst]; rw [substEq position]
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawPolyTerm.subst]
      rw [bodyIH (RawPolyTermSubst.lift_pointwise substEq)]
  | app fn arg fnIH argIH =>
      simp only [RawPolyTerm.subst]; rw [fnIH substEq, argIH substEq]
  | pair fv sv fvIH svIH =>
      simp only [RawPolyTerm.subst]; rw [fvIH substEq, svIH substEq]
  | fst pairTerm pairIH =>
      simp only [RawPolyTerm.subst]; rw [pairIH substEq]
  | snd pairTerm pairIH =>
      simp only [RawPolyTerm.subst]; rw [pairIH substEq]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, tIH substEq, eIH substEq]
  | natZero => rfl
  | natSucc p pIH =>
      simp only [RawPolyTerm.subst]; rw [pIH substEq]
  | natElim s z c sIH zIH cIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, zIH substEq, cIH substEq]
  | natRec s z c sIH zIH cIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, zIH substEq, cIH substEq]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      simp only [RawPolyTerm.subst]
      rw [headIH substEq, tailIH substEq]
  | listElim s n c sIH nIH cIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, nIH substEq, cIH substEq]
  | optionNone => rfl
  | optionSome v vIH =>
      simp only [RawPolyTerm.subst]; rw [vIH substEq]
  | optionMatch s n c sIH nIH cIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, nIH substEq, cIH substEq]
  | eitherInl v vIH =>
      simp only [RawPolyTerm.subst]; rw [vIH substEq]
  | eitherInr v vIH =>
      simp only [RawPolyTerm.subst]; rw [vIH substEq]
  | eitherMatch s l r sIH lIH rIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, lIH substEq, rIH substEq]
  | refl witness witnessIH =>
      simp only [RawPolyTerm.subst]; rw [witnessIH substEq]
  | idJ base witness baseIH witnessIH =>
      simp only [RawPolyTerm.subst]
      rw [baseIH substEq, witnessIH substEq]
  | modIntro inner innerIH =>
      simp only [RawPolyTerm.subst]; rw [innerIH substEq]
  | modElim inner innerIH =>
      simp only [RawPolyTerm.subst]; rw [innerIH substEq]
  | subsume inner innerIH =>
      simp only [RawPolyTerm.subst]; rw [innerIH substEq]
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      simp only [RawPolyTerm.subst]; rw [iIH substEq]
  | intervalMeet l r lIH rIH =>
      simp only [RawPolyTerm.subst]; rw [lIH substEq, rIH substEq]
  | intervalJoin l r lIH rIH =>
      simp only [RawPolyTerm.subst]; rw [lIH substEq, rIH substEq]
  | pathLam body bodyIH =>
      simp only [RawPolyTerm.subst]
      rw [bodyIH (RawPolyTermSubst.lift_pointwise substEq)]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawPolyTerm.subst]
      rw [pathIH substEq, intervalIH substEq]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawPolyTerm.subst]
      rw [baseIH substEq, partialIH substEq]
  | glueElim gluedValue gluedIH =>
      simp only [RawPolyTerm.subst]; rw [gluedIH substEq]
  | transp path source pathIH sourceIH =>
      simp only [RawPolyTerm.subst]
      rw [pathIH substEq, sourceIH substEq]
  | transpFill path interval source pathIH intervalIH sourceIH =>
      simp only [RawPolyTerm.subst]
      rw [pathIH substEq, intervalIH substEq, sourceIH substEq]
  | hcomp sides cap sidesIH capIH =>
      simp only [RawPolyTerm.subst]; rw [sidesIH substEq, capIH substEq]
  | oeqRefl witness witnessIH =>
      simp only [RawPolyTerm.subst]; rw [witnessIH substEq]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawPolyTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawPolyTerm.subst]; rw [pointwiseIH substEq]
  | idStrictRefl witness witnessIH =>
      simp only [RawPolyTerm.subst]; rw [witnessIH substEq]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawPolyTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      simp only [RawPolyTerm.subst]
      rw [forwardIH substEq, backwardIH substEq]
  | equivApp equivTerm argument equivIH argumentIH =>
      simp only [RawPolyTerm.subst]
      rw [equivIH substEq, argumentIH substEq]
  | refineIntro rawValue predicateProof rawIH proofIH =>
      simp only [RawPolyTerm.subst]; rw [rawIH substEq, proofIH substEq]
  | refineElim refinedValue refinedIH =>
      simp only [RawPolyTerm.subst]; rw [refinedIH substEq]
  | recordIntro firstField firstIH =>
      simp only [RawPolyTerm.subst]; rw [firstIH substEq]
  | recordProj recordValue recordIH =>
      simp only [RawPolyTerm.subst]; rw [recordIH substEq]
  | codataUnfold initialState transition initialIH transitionIH =>
      simp only [RawPolyTerm.subst]
      rw [initialIH substEq, transitionIH substEq]
  | codataDest codataValue codataIH =>
      simp only [RawPolyTerm.subst]; rw [codataIH substEq]
  | sessionSend channel payload channelIH payloadIH =>
      simp only [RawPolyTerm.subst]
      rw [channelIH substEq, payloadIH substEq]
  | sessionRecv channel channelIH =>
      simp only [RawPolyTerm.subst]; rw [channelIH substEq]
  | effectPerform operationTag arguments operationIH argumentsIH =>
      simp only [RawPolyTerm.subst]
      rw [operationIH substEq, argumentsIH substEq]
  | universeCode innerLevel => rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawPolyTerm.subst]
      rw [domainIH substEq, codomainIH substEq]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawPolyTerm.subst]
      rw [domainIH substEq,
          codomainIH (RawPolyTermSubst.lift_pointwise substEq)]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawPolyTerm.subst]
      rw [domainIH substEq,
          codomainIH (RawPolyTermSubst.lift_pointwise substEq)]
  | productCode firstCode secondCode firstIH secondIH =>
      simp only [RawPolyTerm.subst]
      rw [firstIH substEq, secondIH substEq]
  | sumCode leftCode rightCode leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [leftIH substEq, rightIH substEq]
  | listCode elementCode elementIH =>
      simp only [RawPolyTerm.subst]; rw [elementIH substEq]
  | optionCode elementCode elementIH =>
      simp only [RawPolyTerm.subst]; rw [elementIH substEq]
  | eitherCode leftCode rightCode leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [leftIH substEq, rightIH substEq]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [typeIH substEq, leftIH substEq, rightIH substEq]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [leftIH substEq, rightIH substEq]
  | cumulUpMarker innerCodeRaw innerIH =>
      simp only [RawPolyTerm.subst]; rw [innerIH substEq]
  | uaToEquiv proofRaw proofIH =>
      simp only [RawPolyTerm.subst]; rw [proofIH substEq]
  | equivApply equivRaw argRaw equivIH argIH =>
      simp only [RawPolyTerm.subst]; rw [equivIH substEq, argIH substEq]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [leftIH substEq, rightIH substEq]
  | idToEquiv proofRaw proofIH =>
      simp only [RawPolyTerm.subst]; rw [proofIH substEq]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      simp only [RawPolyTerm.subst]
      rw [firstIH substEq, secondIH substEq]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      simp only [RawPolyTerm.subst]
      rw [firstIH substEq, secondIH substEq]

end LeanFX2.Foundation.Polygraph

namespace LeanFX2

open LeanFX2.Foundation.Polygraph

/-- Cross-layer converter: a raw substitution targeting `RawTerm`
becomes a raw substitution targeting `RawPolyTerm` by pointwise
application of `RawTerm.toRawPoly`.  Marked `@[reducible]` so
downstream rewrites can unfold the converter definitionally. -/
@[reducible] def RawTermSubst.toRawPolySubst {source target : Nat}
    (substitution : RawTermSubst source target) :
    RawPolyTermSubst source target :=
  fun position => (substitution position).toRawPoly

/-- The `lift` operation commutes with the cross-layer converter
pointwise.  Succ case uses Phase A's `RawTerm.weaken_toRawPoly_commute`
to bridge `(σ k).rename weaken |>.toRawPoly = (σ k).toRawPoly.rename
weaken`. -/
theorem RawTermSubst.lift_toRawPolySubst_commute
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    ∀ position,
      substitution.lift.toRawPolySubst position =
        substitution.toRawPolySubst.lift position
  | ⟨0, _⟩     => rfl
  | ⟨k + 1, h⟩ => by
      simp only [RawTermSubst.toRawPolySubst, RawTermSubst.lift,
                 RawPolyTermSubst.lift]
      exact RawTerm.weaken_toRawPoly_commute
        (substitution ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- The K11.13 Phase B headline commute lemma: applying a raw
substitution and then converting to `RawPolyTerm` is the same as
converting both the term and the substitution to the polygraph
layer and substituting there.  Structural induction on `rawTerm`
with `targetScope` generalised so the binder cases receive
`bodyIH substitution.lift`.  Binder cases combine the IH with
`subst_pointwise` over `lift_toRawPolySubst_commute` to bridge
`substitution.lift.toRawPolySubst` against
`substitution.toRawPolySubst.lift`. -/
theorem RawTerm.subst_toRawPoly_commute :
    ∀ {sourceScope targetScope : Nat}
      (rawTerm : RawTerm sourceScope)
      (substitution : RawTermSubst sourceScope targetScope),
        (rawTerm.subst substitution).toRawPoly =
          rawTerm.toRawPoly.subst substitution.toRawPolySubst := by
  intro sourceScope targetScope rawTerm
  induction rawTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      have liftedCommute := bodyIH substitution.lift
      rw [liftedCommute]
      exact congrArgLam
        (RawPolyTerm.subst_pointwise
          (RawTermSubst.lift_toRawPolySubst_commute substitution) _)
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.app
        (functionIH substitution) (argumentIH substitution)
  | pair firstValue secondValue firstIH secondIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.pair
        (firstIH substitution) (secondIH substitution)
  | fst pairTerm pairIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.fst (pairIH substitution)
  | snd pairTerm pairIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.snd (pairIH substitution)
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch
      scrutineeIH thenIH elseIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.boolElim
        (scrutineeIH substitution) (thenIH substitution)
        (elseIH substitution)
  | natZero => intro _; rfl
  | natSucc predecessor predecessorIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.natSucc (predecessorIH substitution)
  | natElim scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.natElim
        (scrutineeIH substitution) (zeroIH substitution)
        (succIH substitution)
  | natRec scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.natRec
        (scrutineeIH substitution) (zeroIH substitution)
        (succIH substitution)
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.listCons
        (headIH substitution) (tailIH substitution)
  | listElim scrutinee nilBranch consBranch
      scrutineeIH nilIH consIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.listElim
        (scrutineeIH substitution) (nilIH substitution)
        (consIH substitution)
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.optionSome (valueIH substitution)
  | optionMatch scrutinee noneBranch someBranch
      scrutineeIH noneIH someIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.optionMatch
        (scrutineeIH substitution) (noneIH substitution)
        (someIH substitution)
  | eitherInl valueTerm valueIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.eitherInl (valueIH substitution)
  | eitherInr valueTerm valueIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.eitherInr (valueIH substitution)
  | eitherMatch scrutinee leftBranch rightBranch
      scrutineeIH leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.eitherMatch
        (scrutineeIH substitution) (leftIH substitution)
        (rightIH substitution)
  | refl rawWitness witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.refl (witnessIH substitution)
  | idJ baseCase witness baseIH witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.idJ
        (baseIH substitution) (witnessIH substitution)
  | modIntro inner innerIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.modIntro (innerIH substitution)
  | modElim inner innerIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.modElim (innerIH substitution)
  | subsume inner innerIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.subsume (innerIH substitution)
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.intervalOpp (intervalIH substitution)
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.intervalMeet
        (leftIH substitution) (rightIH substitution)
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.intervalJoin
        (leftIH substitution) (rightIH substitution)
  | pathLam body bodyIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      have liftedCommute := bodyIH substitution.lift
      rw [liftedCommute]
      exact congrArg RawPolyTerm.pathLam
        (RawPolyTerm.subst_pointwise
          (RawTermSubst.lift_toRawPolySubst_commute substitution) _)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.pathApp
        (pathIH substitution) (intervalIH substitution)
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.glueIntro
        (baseIH substitution) (partialIH substitution)
  | glueElim gluedValue gluedIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.glueElim (gluedIH substitution)
  | transp path source pathIH sourceIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.transp
        (pathIH substitution) (sourceIH substitution)
  | transpFill path interval source pathIH intervalIH sourceIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.transpFill
        (pathIH substitution) (intervalIH substitution) (sourceIH substitution)
  | hcomp sides cap sidesIH capIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.hcomp
        (sidesIH substitution) (capIH substitution)
  | oeqRefl witness witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.oeqRefl (witnessIH substitution)
  | oeqJ baseCase witness baseIH witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.oeqJ
        (baseIH substitution) (witnessIH substitution)
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.oeqFunext (pointwiseIH substitution)
  | idStrictRefl witness witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.idStrictRefl (witnessIH substitution)
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.idStrictRec
        (baseIH substitution) (witnessIH substitution)
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivIntro
        (forwardIH substitution) (backwardIH substitution)
  | equivApp equivTerm argument equivIH argumentIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivApp
        (equivIH substitution) (argumentIH substitution)
  | refineIntro rawValue predicateProof rawIH proofIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.refineIntro
        (rawIH substitution) (proofIH substitution)
  | refineElim refinedValue refinedIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.refineElim (refinedIH substitution)
  | recordIntro firstField firstIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.recordIntro (firstIH substitution)
  | recordProj recordValue recordIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.recordProj (recordIH substitution)
  | codataUnfold initialState transition initialIH transitionIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.codataUnfold
        (initialIH substitution) (transitionIH substitution)
  | codataDest codataValue codataIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.codataDest (codataIH substitution)
  | sessionSend channel payload channelIH payloadIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.sessionSend
        (channelIH substitution) (payloadIH substitution)
  | sessionRecv channel channelIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.sessionRecv (channelIH substitution)
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.effectPerform
        (operationIH substitution) (argumentsIH substitution)
  | universeCode innerLevel => intro _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.arrowCode
        (domainIH substitution) (codomainIH substitution)
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      have liftedCommute := codomainIH substitution.lift
      rw [liftedCommute]
      exact congrArg2 RawPolyTerm.piTyCode (domainIH substitution)
        (RawPolyTerm.subst_pointwise
          (RawTermSubst.lift_toRawPolySubst_commute substitution) _)
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      have liftedCommute := codomainIH substitution.lift
      rw [liftedCommute]
      exact congrArg2 RawPolyTerm.sigmaTyCode (domainIH substitution)
        (RawPolyTerm.subst_pointwise
          (RawTermSubst.lift_toRawPolySubst_commute substitution) _)
  | productCode firstCode secondCode firstIH secondIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.productCode
        (firstIH substitution) (secondIH substitution)
  | sumCode leftCode rightCode leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.sumCode
        (leftIH substitution) (rightIH substitution)
  | listCode elementCode elementIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.listCode (elementIH substitution)
  | optionCode elementCode elementIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.optionCode (elementIH substitution)
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.eitherCode
        (leftIH substitution) (rightIH substitution)
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.idCode
        (typeIH substitution) (leftIH substitution)
        (rightIH substitution)
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivCode
        (leftIH substitution) (rightIH substitution)
  | cumulUpMarker innerCodeRaw innerIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.cumulUpMarker (innerIH substitution)
  | uaToEquiv proofRaw proofIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.uaToEquiv (proofIH substitution)
  | equivApply equivRaw argRaw equivIH argIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivApply
        (equivIH substitution) (argIH substitution)
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.pathCompose
        (leftIH substitution) (rightIH substitution)
  | idToEquiv proofRaw proofIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.idToEquiv (proofIH substitution)
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.oeqTrans
        (firstIH substitution) (secondIH substitution)
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivCompose
        (firstIH substitution) (secondIH substitution)

/-- Corollary: `subst0` (single-binder β-substitution) commutes with
`toRawPoly`.  Derived from the headline `subst_toRawPoly_commute` at
`RawTermSubst.singleton`. -/
theorem RawTerm.subst0_toRawPoly_commute {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) :
    (body.subst0 rawArg).toRawPoly =
      body.toRawPoly.subst0 rawArg.toRawPoly := by
  unfold RawTerm.subst0 RawPolyTerm.subst0
  rw [RawTerm.subst_toRawPoly_commute body (RawTermSubst.singleton rawArg)]
  apply RawPolyTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩     => rfl
  | ⟨_ + 1, _⟩ => rfl

end LeanFX2
