import LeanFX2.Confluence.RawCdRename.Helpers

namespace LeanFX2

/-! ## Main theorem: `cd` commutes with `rename`.

Structural induction on `term`.  Atomic ctors close by `rfl`; pure
cong ctors rewrite via the appropriate IH; helper-using ctors invoke
the matching `cd<Helper>Case_rename` lemma above and then unfold cd
+ rewrite IHs.

Modeled on `RawTerm.rename_compose` (`Foundation/RawSubst.lean:375`)
— same induction shape, same case enumeration, plus an extra
helper-rename rewrite step for the 17 redex-bearing ctors. -/

theorem RawTerm.cd_rename {sourceScope : Nat} (term : RawTerm sourceScope) :
    ∀ {targetScope : Nat} (rho : RawRenaming sourceScope targetScope),
      (RawTerm.cd term).rename rho = RawTerm.cd (term.rename rho) := by
  induction term with
  | var position => intro _ _; rfl
  | unit => intro _ _; rfl
  | lam body bodyIH =>
      intro _ rho
      show (RawTerm.lam (RawTerm.cd body)).rename rho =
           RawTerm.cd (RawTerm.lam (body.rename rho.lift))
      dsimp only [RawTerm.rename, RawTerm.cd]
      exact congrArg RawTerm.lam (bodyIH rho.lift)
  | app fn arg fnIH argIH =>
      intro _ rho
      show (RawTerm.cdAppCase (RawTerm.cd fn) (RawTerm.cd arg)).rename rho =
           RawTerm.cd (RawTerm.app (fn.rename rho) (arg.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdAppCase_rename rho (RawTerm.cd fn) (RawTerm.cd arg),
          fnIH rho, argIH rho]
  | pair fv sv fvIH svIH =>
      intro _ rho
      show (RawTerm.pair (RawTerm.cd fv) (RawTerm.cd sv)).rename rho =
           RawTerm.cd (RawTerm.pair (fv.rename rho) (sv.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [fvIH rho, svIH rho]
  | fst pairTerm pairIH =>
      intro _ rho
      show (RawTerm.cdFstCase (RawTerm.cd pairTerm)).rename rho =
           RawTerm.cd (RawTerm.fst (pairTerm.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdFstCase_rename rho (RawTerm.cd pairTerm), pairIH rho]
  | snd pairTerm pairIH =>
      intro _ rho
      show (RawTerm.cdSndCase (RawTerm.cd pairTerm)).rename rho =
           RawTerm.cd (RawTerm.snd (pairTerm.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdSndCase_rename rho (RawTerm.cd pairTerm), pairIH rho]
  | boolTrue => intro _ _; rfl
  | boolFalse => intro _ _; rfl
  | boolElim s t e sIH tIH eIH =>
      intro _ rho
      show (RawTerm.cdBoolElimCase (RawTerm.cd s) (RawTerm.cd t) (RawTerm.cd e)).rename rho =
           RawTerm.cd (RawTerm.boolElim (s.rename rho) (t.rename rho) (e.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdBoolElimCase_rename rho (RawTerm.cd s) (RawTerm.cd t) (RawTerm.cd e),
          sIH rho, tIH rho, eIH rho]
  | natZero => intro _ _; rfl
  | natSucc p pIH =>
      intro _ rho
      show (RawTerm.natSucc (RawTerm.cd p)).rename rho =
           RawTerm.cd (RawTerm.natSucc (p.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [pIH rho]
  | natElim s z c sIH zIH cIH =>
      intro _ rho
      show (RawTerm.cdNatElimCase (RawTerm.cd s) (RawTerm.cd z) (RawTerm.cd c)).rename rho =
           RawTerm.cd (RawTerm.natElim (s.rename rho) (z.rename rho) (c.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdNatElimCase_rename rho (RawTerm.cd s) (RawTerm.cd z) (RawTerm.cd c),
          sIH rho, zIH rho, cIH rho]
  | natRec s z c sIH zIH cIH =>
      intro _ rho
      show (RawTerm.cdNatRecCase (RawTerm.cd s) (RawTerm.cd z) (RawTerm.cd c)).rename rho =
           RawTerm.cd (RawTerm.natRec (s.rename rho) (z.rename rho) (c.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdNatRecCase_rename rho (RawTerm.cd s) (RawTerm.cd z) (RawTerm.cd c),
          sIH rho, zIH rho, cIH rho]
  | listNil => intro _ _; rfl
  | listCons h t hIH tIH =>
      intro _ rho
      show (RawTerm.listCons (RawTerm.cd h) (RawTerm.cd t)).rename rho =
           RawTerm.cd (RawTerm.listCons (h.rename rho) (t.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [hIH rho, tIH rho]
  | listElim s n c sIH nIH cIH =>
      intro _ rho
      show (RawTerm.cdListElimCase (RawTerm.cd s) (RawTerm.cd n) (RawTerm.cd c)).rename rho =
           RawTerm.cd (RawTerm.listElim (s.rename rho) (n.rename rho) (c.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdListElimCase_rename rho (RawTerm.cd s) (RawTerm.cd n) (RawTerm.cd c),
          sIH rho, nIH rho, cIH rho]
  | optionNone => intro _ _; rfl
  | optionSome v vIH =>
      intro _ rho
      show (RawTerm.optionSome (RawTerm.cd v)).rename rho =
           RawTerm.cd (RawTerm.optionSome (v.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [vIH rho]
  | optionMatch s n c sIH nIH cIH =>
      intro _ rho
      show (RawTerm.cdOptionMatchCase (RawTerm.cd s) (RawTerm.cd n) (RawTerm.cd c)).rename rho =
           RawTerm.cd (RawTerm.optionMatch (s.rename rho) (n.rename rho) (c.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdOptionMatchCase_rename rho (RawTerm.cd s) (RawTerm.cd n) (RawTerm.cd c),
          sIH rho, nIH rho, cIH rho]
  | eitherInl v vIH =>
      intro _ rho
      show (RawTerm.eitherInl (RawTerm.cd v)).rename rho =
           RawTerm.cd (RawTerm.eitherInl (v.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [vIH rho]
  | eitherInr v vIH =>
      intro _ rho
      show (RawTerm.eitherInr (RawTerm.cd v)).rename rho =
           RawTerm.cd (RawTerm.eitherInr (v.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [vIH rho]
  | eitherMatch s l r sIH lIH rIH =>
      intro _ rho
      show (RawTerm.cdEitherMatchCase (RawTerm.cd s) (RawTerm.cd l) (RawTerm.cd r)).rename rho =
           RawTerm.cd (RawTerm.eitherMatch (s.rename rho) (l.rename rho) (r.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdEitherMatchCase_rename rho (RawTerm.cd s) (RawTerm.cd l) (RawTerm.cd r),
          sIH rho, lIH rho, rIH rho]
  | refl witness witnessIH =>
      intro _ rho
      show (RawTerm.refl (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.refl (witness.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [witnessIH rho]
  | idJ base witness baseIH witnessIH =>
      intro _ rho
      show (RawTerm.cdIdJCase (RawTerm.cd base) (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.idJ (base.rename rho) (witness.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdIdJCase_rename rho (RawTerm.cd base) (RawTerm.cd witness),
          baseIH rho, witnessIH rho]
  | modIntro inner innerIH =>
      intro _ rho
      show (RawTerm.modIntro (RawTerm.cd inner)).rename rho =
           RawTerm.cd (RawTerm.modIntro (inner.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [innerIH rho]
  | modElim inner innerIH =>
      intro _ rho
      show (RawTerm.cdModElimCase (RawTerm.cd inner)).rename rho =
           RawTerm.cd (RawTerm.modElim (inner.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdModElimCase_rename rho (RawTerm.cd inner), innerIH rho]
  | subsume inner innerIH =>
      intro _ rho
      show (RawTerm.subsume (RawTerm.cd inner)).rename rho =
           RawTerm.cd (RawTerm.subsume (inner.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [innerIH rho]
  | interval0 => intro _ _; rfl
  | interval1 => intro _ _; rfl
  | intervalOpp i iIH =>
      intro _ rho
      show (RawTerm.intervalOpp (RawTerm.cd i)).rename rho =
           RawTerm.cd (RawTerm.intervalOpp (i.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [iIH rho]
  | intervalMeet l r lIH rIH =>
      intro _ rho
      show (RawTerm.intervalMeet (RawTerm.cd l) (RawTerm.cd r)).rename rho =
           RawTerm.cd (RawTerm.intervalMeet (l.rename rho) (r.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [lIH rho, rIH rho]
  | intervalJoin l r lIH rIH =>
      intro _ rho
      show (RawTerm.intervalJoin (RawTerm.cd l) (RawTerm.cd r)).rename rho =
           RawTerm.cd (RawTerm.intervalJoin (l.rename rho) (r.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [lIH rho, rIH rho]
  | pathLam body bodyIH =>
      intro _ rho
      show (RawTerm.pathLam (RawTerm.cd body)).rename rho =
           RawTerm.cd (RawTerm.pathLam (body.rename rho.lift))
      dsimp only [RawTerm.rename, RawTerm.cd]
      exact congrArg RawTerm.pathLam (bodyIH rho.lift)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro _ rho
      show (RawTerm.cdPathAppCase (RawTerm.cd pathTerm) (RawTerm.cd intervalArg)).rename rho =
           RawTerm.cd (RawTerm.pathApp (pathTerm.rename rho) (intervalArg.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdPathAppCase_rename rho (RawTerm.cd pathTerm) (RawTerm.cd intervalArg),
          pathIH rho, intervalIH rho]
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro _ rho
      show (RawTerm.glueIntro (RawTerm.cd baseValue) (RawTerm.cd partialValue)).rename rho =
           RawTerm.cd (RawTerm.glueIntro (baseValue.rename rho) (partialValue.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [baseIH rho, partialIH rho]
  | glueElim gluedValue gluedIH =>
      intro _ rho
      show (RawTerm.cdGlueElimCase (RawTerm.cd gluedValue)).rename rho =
           RawTerm.cd (RawTerm.glueElim (gluedValue.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdGlueElimCase_rename rho (RawTerm.cd gluedValue), gluedIH rho]
  | transp pathTerm sourceTerm pathIH sourceIH =>
      intro _ rho
      show (RawTerm.cdTranspCase (RawTerm.cd pathTerm) (RawTerm.cd sourceTerm)).rename rho =
           RawTerm.cd (RawTerm.transp (pathTerm.rename rho) (sourceTerm.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdTranspCase_rename rho (RawTerm.cd pathTerm) (RawTerm.cd sourceTerm),
          pathIH rho, sourceIH rho]
  | transpFill pathTerm intervalTerm sourceTerm pathIH intervalIH sourceIH =>
      intro _ rho
      show (RawTerm.transpFill (RawTerm.cd pathTerm) (RawTerm.cd intervalTerm)
              (RawTerm.cd sourceTerm)).rename rho =
           RawTerm.cd (RawTerm.transpFill (pathTerm.rename rho)
              (intervalTerm.rename rho) (sourceTerm.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [pathIH rho, intervalIH rho, sourceIH rho]
  | hcomp sides cap sidesIH capIH =>
      intro _ rho
      show (RawTerm.cdHcompCase (RawTerm.cd sides) (RawTerm.cd cap)).rename rho =
           RawTerm.cd (RawTerm.hcomp (sides.rename rho) (cap.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdHcompCase_rename rho (RawTerm.cd sides) (RawTerm.cd cap),
          sidesIH rho, capIH rho]
  | oeqRefl witness witnessIH =>
      intro _ rho
      show (RawTerm.oeqRefl (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.oeqRefl (witness.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [witnessIH rho]
  | oeqJ base witness baseIH witnessIH =>
      intro _ rho
      show (RawTerm.oeqJ (RawTerm.cd base) (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.oeqJ (base.rename rho) (witness.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [baseIH rho, witnessIH rho]
  | oeqFunext pointwise pointwiseIH =>
      intro _ rho
      show (RawTerm.oeqFunext (RawTerm.cd pointwise)).rename rho =
           RawTerm.cd (RawTerm.oeqFunext (pointwise.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [pointwiseIH rho]
  | idStrictRefl witness witnessIH =>
      intro _ rho
      show (RawTerm.idStrictRefl (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.idStrictRefl (witness.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [witnessIH rho]
  | idStrictRec base witness baseIH witnessIH =>
      intro _ rho
      show (RawTerm.cdIdStrictRecCase (RawTerm.cd base) (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.idStrictRec (base.rename rho) (witness.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdIdStrictRecCase_rename rho (RawTerm.cd base) (RawTerm.cd witness),
          baseIH rho, witnessIH rho]
  | equivIntro fwd bwd fwdIH bwdIH =>
      intro _ rho
      show (RawTerm.equivIntro (RawTerm.cd fwd) (RawTerm.cd bwd)).rename rho =
           RawTerm.cd (RawTerm.equivIntro (fwd.rename rho) (bwd.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [fwdIH rho, bwdIH rho]
  | equivApp equivTerm argument equivIH argIH =>
      intro _ rho
      show (RawTerm.equivApp (RawTerm.cd equivTerm) (RawTerm.cd argument)).rename rho =
           RawTerm.cd (RawTerm.equivApp (equivTerm.rename rho) (argument.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [equivIH rho, argIH rho]
  | refineIntro rawValue predicateProof valueIH proofIH =>
      intro _ rho
      show (RawTerm.refineIntro (RawTerm.cd rawValue) (RawTerm.cd predicateProof)).rename rho =
           RawTerm.cd (RawTerm.refineIntro (rawValue.rename rho) (predicateProof.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [valueIH rho, proofIH rho]
  | refineElim refinedValue refinedIH =>
      intro _ rho
      show (RawTerm.cdRefineElimCase (RawTerm.cd refinedValue)).rename rho =
           RawTerm.cd (RawTerm.refineElim (refinedValue.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdRefineElimCase_rename rho (RawTerm.cd refinedValue), refinedIH rho]
  | recordIntro firstField firstIH =>
      intro _ rho
      show (RawTerm.recordIntro (RawTerm.cd firstField)).rename rho =
           RawTerm.cd (RawTerm.recordIntro (firstField.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [firstIH rho]
  | recordProj recordValue recordIH =>
      intro _ rho
      show (RawTerm.cdRecordProjCase (RawTerm.cd recordValue)).rename rho =
           RawTerm.cd (RawTerm.recordProj (recordValue.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdRecordProjCase_rename rho (RawTerm.cd recordValue), recordIH rho]
  | codataUnfold initialState transition stateIH transIH =>
      intro _ rho
      show (RawTerm.codataUnfold (RawTerm.cd initialState) (RawTerm.cd transition)).rename rho =
           RawTerm.cd (RawTerm.codataUnfold (initialState.rename rho) (transition.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [stateIH rho, transIH rho]
  | codataDest codataValue codataIH =>
      intro _ rho
      show (RawTerm.cdCodataDestCase (RawTerm.cd codataValue)).rename rho =
           RawTerm.cd (RawTerm.codataDest (codataValue.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdCodataDestCase_rename rho (RawTerm.cd codataValue), codataIH rho]
  | sessionSend channel payload chIH payloadIH =>
      intro _ rho
      show (RawTerm.sessionSend (RawTerm.cd channel) (RawTerm.cd payload)).rename rho =
           RawTerm.cd (RawTerm.sessionSend (channel.rename rho) (payload.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [chIH rho, payloadIH rho]
  | sessionRecv channel chIH =>
      intro _ rho
      show (RawTerm.sessionRecv (RawTerm.cd channel)).rename rho =
           RawTerm.cd (RawTerm.sessionRecv (channel.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [chIH rho]
  | effectPerform operationTag arguments tagIH argsIH =>
      intro _ rho
      show (RawTerm.effectPerform (RawTerm.cd operationTag) (RawTerm.cd arguments)).rename rho =
           RawTerm.cd (RawTerm.effectPerform (operationTag.rename rho) (arguments.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [tagIH rho, argsIH rho]
  | universeCode innerLevel => intro _ _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro _ rho
      show (RawTerm.arrowCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)).rename rho =
           RawTerm.cd (RawTerm.arrowCode (domainCode.rename rho) (codomainCode.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [domainIH rho, codomainIH rho]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro _ rho
      show (RawTerm.piTyCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)).rename rho =
           RawTerm.cd (RawTerm.piTyCode (domainCode.rename rho) (codomainCode.rename rho.lift))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [domainIH rho, codomainIH rho.lift]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro _ rho
      show (RawTerm.sigmaTyCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)).rename rho =
           RawTerm.cd (RawTerm.sigmaTyCode (domainCode.rename rho) (codomainCode.rename rho.lift))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [domainIH rho, codomainIH rho.lift]
  | productCode firstCode secondCode firstIH secondIH =>
      intro _ rho
      show (RawTerm.productCode (RawTerm.cd firstCode) (RawTerm.cd secondCode)).rename rho =
           RawTerm.cd (RawTerm.productCode (firstCode.rename rho) (secondCode.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [firstIH rho, secondIH rho]
  | sumCode leftCode rightCode leftIH rightIH =>
      intro _ rho
      show (RawTerm.sumCode (RawTerm.cd leftCode) (RawTerm.cd rightCode)).rename rho =
           RawTerm.cd (RawTerm.sumCode (leftCode.rename rho) (rightCode.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [leftIH rho, rightIH rho]
  | listCode elementCode elementIH =>
      intro _ rho
      show (RawTerm.listCode (RawTerm.cd elementCode)).rename rho =
           RawTerm.cd (RawTerm.listCode (elementCode.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [elementIH rho]
  | optionCode elementCode elementIH =>
      intro _ rho
      show (RawTerm.optionCode (RawTerm.cd elementCode)).rename rho =
           RawTerm.cd (RawTerm.optionCode (elementCode.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [elementIH rho]
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro _ rho
      show (RawTerm.eitherCode (RawTerm.cd leftCode) (RawTerm.cd rightCode)).rename rho =
           RawTerm.cd (RawTerm.eitherCode (leftCode.rename rho) (rightCode.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [leftIH rho, rightIH rho]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro _ rho
      show (RawTerm.idCode (RawTerm.cd typeCode) (RawTerm.cd leftRaw) (RawTerm.cd rightRaw)).rename rho =
           RawTerm.cd (RawTerm.idCode (typeCode.rename rho) (leftRaw.rename rho) (rightRaw.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [typeIH rho, leftIH rho, rightIH rho]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro _ rho
      show (RawTerm.equivCode (RawTerm.cd leftTypeCode) (RawTerm.cd rightTypeCode)).rename rho =
           RawTerm.cd (RawTerm.equivCode (leftTypeCode.rename rho) (rightTypeCode.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [leftIH rho, rightIH rho]
  | cumulUpMarker innerCodeRaw innerIH =>
      intro _ rho
      show (RawTerm.cumulUpMarker (RawTerm.cd innerCodeRaw)).rename rho =
           RawTerm.cd (RawTerm.cumulUpMarker (innerCodeRaw.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [innerIH rho]
  | uaToEquiv proofRaw proofIH =>
      intro _ rho
      show (RawTerm.uaToEquiv (RawTerm.cd proofRaw)).rename rho =
           RawTerm.cd (RawTerm.uaToEquiv (proofRaw.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [proofIH rho]
  | equivApply equivRaw argRaw equivIH argIH =>
      intro _ rho
      show (RawTerm.cdEquivApplyCase (RawTerm.cd equivRaw) (RawTerm.cd argRaw)).rename rho =
           RawTerm.cd (RawTerm.equivApply (equivRaw.rename rho) (argRaw.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdEquivApplyCase_rename rho (RawTerm.cd equivRaw) (RawTerm.cd argRaw),
        equivIH rho, argIH rho]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro _ rho
      show (RawTerm.pathCompose (RawTerm.cd leftPathRaw) (RawTerm.cd rightPathRaw)).rename rho =
           RawTerm.cd (RawTerm.pathCompose (leftPathRaw.rename rho)
                                            (rightPathRaw.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [leftIH rho, rightIH rho]
  | idToEquiv proofRaw proofIH =>
      intro _ rho
      show (RawTerm.cdIdToEquivCase (RawTerm.cd proofRaw)).rename rho =
           RawTerm.cd (RawTerm.idToEquiv (proofRaw.rename rho))
      dsimp only [RawTerm.cd]
      rw [RawTerm.cdIdToEquivCase_rename rho (RawTerm.cd proofRaw),
        proofIH rho]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro _ rho
      show (RawTerm.oeqTrans (RawTerm.cd firstProof) (RawTerm.cd secondProof)).rename rho =
           RawTerm.cd (RawTerm.oeqTrans (firstProof.rename rho)
                                        (secondProof.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [firstIH rho, secondIH rho]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro _ rho
      show (RawTerm.equivCompose (RawTerm.cd firstEquiv) (RawTerm.cd secondEquiv)).rename rho =
           RawTerm.cd (RawTerm.equivCompose (firstEquiv.rename rho)
                                            (secondEquiv.rename rho))
      dsimp only [RawTerm.rename, RawTerm.cd]
      rw [firstIH rho, secondIH rho]

/-! ## Specialization: `cd_weaken`. -/

/-- Specialization of `cd_rename` to weakening: developing the
weakened term equals weakening the developed term.  This is the
load-bearing fact for the `transpReflBeta` cd cascade — together
with `RawTerm.unweaken?_weaken` it gives `unweaken? (cd t.weaken) =
some (cd t)`, recognizing constant-path transp at the cd layer. -/
theorem RawTerm.cd_weaken {scope : Nat} (term : RawTerm scope) :
    RawTerm.cd term.weaken = (RawTerm.cd term).weaken := by
  show RawTerm.cd (term.rename RawRenaming.weaken) =
       (RawTerm.cd term).rename RawRenaming.weaken
  exact (RawTerm.cd_rename term RawRenaming.weaken).symm

/-! ## Corollary: `unweaken? ∘ cd ∘ weaken = some ∘ cd`. -/

/-- The cd cascade's recognizer fact: weakening a term and then
developing makes the weakened structure recoverable via `unweaken?`,
and the recovered preimage is `cd term`.  Closes the chain
`unweaken? (cd t.weaken) = unweaken? (cd t).weaken = some (cd t)`. -/
theorem RawTerm.unweaken?_cd_weaken {scope : Nat} (term : RawTerm scope) :
    RawTerm.unweaken? (RawTerm.cd term.weaken) = some (RawTerm.cd term) := by
  rw [RawTerm.cd_weaken term]
  exact RawTerm.unweaken?_weaken (RawTerm.cd term)

end LeanFX2
