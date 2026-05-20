import LeanFX2.Foundation.RawSubst.RenameDefs

/-! # LeanFX2.Foundation.RawSubst.RenameLemmas

Pointwise + composition lemmas for `RawTerm.rename` plus the
load-bearing `weaken/lift` commute identity. Mirrors the BHKM RcR
fusion lemma at the raw-renaming layer.

## Root status

Structural induction over `RawTerm`; strict zero-axiom (induction
with universal binder per `feedback_lean_match_arity_axioms.md`). -/

namespace LeanFX2

/-! ## Pointwise + composition lemmas for raw renaming.

These are needed to prove the `weaken/lift` commute laws that
downstream Term.rename / Ty.subst use.  Proofs use `induction` tactic
(propext-free per `feedback_lean_zero_axiom_match.md` Rule 6) and
chain rewrites via `rw`. -/

/-- Lift respects pointwise equality. -/
theorem RawRenaming.lift_pointwise {sourceScope targetScope : Nat}
    {rho1 rho2 : RawRenaming sourceScope targetScope}
    (renamingEq : ∀ position, rho1 position = rho2 position) :
    ∀ position, rho1.lift position = rho2.lift position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      simp only [RawRenaming.lift]
      exact congrArg Fin.succ (renamingEq ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- RawTerm.rename respects pointwise renaming equality. -/
theorem RawTerm.rename_pointwise {sourceScope targetScope : Nat}
    {rho1 rho2 : RawRenaming sourceScope targetScope}
    (renamingEq : ∀ position, rho1 position = rho2 position) :
    ∀ (term : RawTerm sourceScope), term.rename rho1 = term.rename rho2 := by
  intro term
  induction term generalizing targetScope with
  | var position =>
      dsimp only [RawTerm.rename]; rw [renamingEq position]
  | unit => rfl
  | lam body bodyIH =>
      dsimp only [RawTerm.rename]; rw [bodyIH (RawRenaming.lift_pointwise renamingEq)]
  | app fn arg fnIH argIH =>
      dsimp only [RawTerm.rename]; rw [fnIH renamingEq, argIH renamingEq]
  | pair fv sv fvIH svIH =>
      dsimp only [RawTerm.rename]; rw [fvIH renamingEq, svIH renamingEq]
  | fst pairTerm pairIH =>
      dsimp only [RawTerm.rename]; rw [pairIH renamingEq]
  | snd pairTerm pairIH =>
      dsimp only [RawTerm.rename]; rw [pairIH renamingEq]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      dsimp only [RawTerm.rename]; rw [sIH renamingEq, tIH renamingEq, eIH renamingEq]
  | natZero => rfl
  | natSucc p pIH =>
      dsimp only [RawTerm.rename]; rw [pIH renamingEq]
  | natElim s z c sIH zIH cIH =>
      dsimp only [RawTerm.rename]; rw [sIH renamingEq, zIH renamingEq, cIH renamingEq]
  | natRec s z c sIH zIH cIH =>
      dsimp only [RawTerm.rename]; rw [sIH renamingEq, zIH renamingEq, cIH renamingEq]
  | listNil => rfl
  | listCons h t hIH tIH =>
      dsimp only [RawTerm.rename]; rw [hIH renamingEq, tIH renamingEq]
  | listElim s n c sIH nIH cIH =>
      dsimp only [RawTerm.rename]; rw [sIH renamingEq, nIH renamingEq, cIH renamingEq]
  | optionNone => rfl
  | optionSome v vIH =>
      dsimp only [RawTerm.rename]; rw [vIH renamingEq]
  | optionMatch s n c sIH nIH cIH =>
      dsimp only [RawTerm.rename]; rw [sIH renamingEq, nIH renamingEq, cIH renamingEq]
  | eitherInl v vIH =>
      dsimp only [RawTerm.rename]; rw [vIH renamingEq]
  | eitherInr v vIH =>
      dsimp only [RawTerm.rename]; rw [vIH renamingEq]
  | eitherMatch s l r sIH lIH rIH =>
      dsimp only [RawTerm.rename]; rw [sIH renamingEq, lIH renamingEq, rIH renamingEq]
  | refl witness witnessIH =>
      dsimp only [RawTerm.rename]; rw [witnessIH renamingEq]
  | idJ base witness baseIH witnessIH =>
      dsimp only [RawTerm.rename]; rw [baseIH renamingEq, witnessIH renamingEq]
  | modIntro inner innerIH =>
      dsimp only [RawTerm.rename]; rw [innerIH renamingEq]
  | modElim inner innerIH =>
      dsimp only [RawTerm.rename]; rw [innerIH renamingEq]
  | subsume inner innerIH =>
      dsimp only [RawTerm.rename]; rw [innerIH renamingEq]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      dsimp only [RawTerm.rename]; rw [iIH renamingEq]
  | intervalMeet l r lIH rIH =>
      dsimp only [RawTerm.rename]; rw [lIH renamingEq, rIH renamingEq]
  | intervalJoin l r lIH rIH =>
      dsimp only [RawTerm.rename]; rw [lIH renamingEq, rIH renamingEq]
  | pathLam body bodyIH =>
      dsimp only [RawTerm.rename]
      rw [bodyIH (RawRenaming.lift_pointwise renamingEq)]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      dsimp only [RawTerm.rename]; rw [pathIH renamingEq, intervalIH renamingEq]
  | glueIntro baseValue partialValue baseIH partialIH =>
      dsimp only [RawTerm.rename]; rw [baseIH renamingEq, partialIH renamingEq]
  | glueElim gluedValue gluedIH =>
      dsimp only [RawTerm.rename]; rw [gluedIH renamingEq]
  | transp path source pathIH sourceIH =>
      dsimp only [RawTerm.rename]; rw [pathIH renamingEq, sourceIH renamingEq]
  | hcomp sides cap sidesIH capIH =>
      dsimp only [RawTerm.rename]; rw [sidesIH renamingEq, capIH renamingEq]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      dsimp only [RawTerm.rename]; rw [witnessIH renamingEq]
  | oeqJ baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.rename]; rw [baseIH renamingEq, witnessIH renamingEq]
  | oeqFunext pointwiseEquality pointwiseIH =>
      dsimp only [RawTerm.rename]; rw [pointwiseIH renamingEq]
  | idStrictRefl witness witnessIH =>
      dsimp only [RawTerm.rename]; rw [witnessIH renamingEq]
  | idStrictRec baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.rename]; rw [baseIH renamingEq, witnessIH renamingEq]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      dsimp only [RawTerm.rename]; rw [fwdIH renamingEq, bwdIH renamingEq]
  | equivApp equivTerm argument equivIH argIH =>
      dsimp only [RawTerm.rename]; rw [equivIH renamingEq, argIH renamingEq]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      dsimp only [RawTerm.rename]; rw [valueIH renamingEq, proofIH renamingEq]
  | refineElim refinedValue refinedIH =>
      dsimp only [RawTerm.rename]; rw [refinedIH renamingEq]
  | recordIntro firstField firstIH =>
      dsimp only [RawTerm.rename]; rw [firstIH renamingEq]
  | recordProj recordValue recordIH =>
      dsimp only [RawTerm.rename]; rw [recordIH renamingEq]
  | codataUnfold initialState transition stateIH transIH =>
      dsimp only [RawTerm.rename]; rw [stateIH renamingEq, transIH renamingEq]
  | codataDest codataValue codataIH =>
      dsimp only [RawTerm.rename]; rw [codataIH renamingEq]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      dsimp only [RawTerm.rename]; rw [chIH renamingEq, payloadIH renamingEq]
  | sessionRecv channel chIH =>
      dsimp only [RawTerm.rename]; rw [chIH renamingEq]
  | effectPerform operationTag arguments tagIH argsIH =>
      dsimp only [RawTerm.rename]; rw [tagIH renamingEq, argsIH renamingEq]
  | universeCode innerLevel => rfl
  -- CUMUL-2.1 per-shape type codes.
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.rename]; rw [domainIH renamingEq, codomainIH renamingEq]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.rename]
      rw [domainIH renamingEq, codomainIH (RawRenaming.lift_pointwise renamingEq)]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.rename]
      rw [domainIH renamingEq, codomainIH (RawRenaming.lift_pointwise renamingEq)]
  | productCode firstCode secondCode firstIH secondIH =>
      dsimp only [RawTerm.rename]; rw [firstIH renamingEq, secondIH renamingEq]
  | sumCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.rename]; rw [leftIH renamingEq, rightIH renamingEq]
  | listCode elementCode elementIH =>
      dsimp only [RawTerm.rename]; rw [elementIH renamingEq]
  | optionCode elementCode elementIH =>
      dsimp only [RawTerm.rename]; rw [elementIH renamingEq]
  | eitherCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.rename]; rw [leftIH renamingEq, rightIH renamingEq]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      dsimp only [RawTerm.rename]
      rw [typeIH renamingEq, leftIH renamingEq, rightIH renamingEq]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      dsimp only [RawTerm.rename]; rw [leftIH renamingEq, rightIH renamingEq]
  | cumulUpMarker innerCodeRaw innerIH =>
      dsimp only [RawTerm.rename]; rw [innerIH renamingEq]
  | uaToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.rename]; rw [proofIH renamingEq]
  | equivApply equivRaw argRaw equivIH argIH =>
      dsimp only [RawTerm.rename]; rw [equivIH renamingEq, argIH renamingEq]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      dsimp only [RawTerm.rename]; rw [leftIH renamingEq, rightIH renamingEq]
  | idToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.rename]; rw [proofIH renamingEq]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      dsimp only [RawTerm.rename]; rw [firstIH renamingEq, secondIH renamingEq]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      dsimp only [RawTerm.rename]; rw [firstIH renamingEq, secondIH renamingEq]
  | transpFill pathTy currentInterval source pathIH intervalIH sourceIH =>
      dsimp only [RawTerm.rename]
      rw [pathIH renamingEq, intervalIH renamingEq, sourceIH renamingEq]

/-- Compose two raw renamings into a single rename. -/
theorem RawTerm.rename_compose {sourceScope middleScope targetScope : Nat}
    (rho1 : RawRenaming sourceScope middleScope)
    (rho2 : RawRenaming middleScope targetScope)
    (term : RawTerm sourceScope) :
    (term.rename rho1).rename rho2 =
      term.rename (fun position => rho2 (rho1 position)) := by
  induction term generalizing middleScope targetScope with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      dsimp only [RawTerm.rename]
      rw [bodyIH rho1.lift rho2.lift]
      congr 1
      apply RawTerm.rename_pointwise
      intro position
      cases position with
      | mk val isLt =>
        cases val with
        | zero => rfl
        | succ k => rfl
  | app fn arg fnIH argIH =>
      dsimp only [RawTerm.rename]; rw [fnIH rho1 rho2, argIH rho1 rho2]
  | pair fv sv fvIH svIH =>
      dsimp only [RawTerm.rename]; rw [fvIH rho1 rho2, svIH rho1 rho2]
  | fst pairTerm pairIH => simp only [RawTerm.rename]; rw [pairIH rho1 rho2]
  | snd pairTerm pairIH => simp only [RawTerm.rename]; rw [pairIH rho1 rho2]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      dsimp only [RawTerm.rename]; rw [sIH rho1 rho2, tIH rho1 rho2, eIH rho1 rho2]
  | natZero => rfl
  | natSucc p pIH => simp only [RawTerm.rename]; rw [pIH rho1 rho2]
  | natElim s z c sIH zIH cIH =>
      dsimp only [RawTerm.rename]; rw [sIH rho1 rho2, zIH rho1 rho2, cIH rho1 rho2]
  | natRec s z c sIH zIH cIH =>
      dsimp only [RawTerm.rename]; rw [sIH rho1 rho2, zIH rho1 rho2, cIH rho1 rho2]
  | listNil => rfl
  | listCons h t hIH tIH =>
      dsimp only [RawTerm.rename]; rw [hIH rho1 rho2, tIH rho1 rho2]
  | listElim s n c sIH nIH cIH =>
      dsimp only [RawTerm.rename]; rw [sIH rho1 rho2, nIH rho1 rho2, cIH rho1 rho2]
  | optionNone => rfl
  | optionSome v vIH => simp only [RawTerm.rename]; rw [vIH rho1 rho2]
  | optionMatch s n c sIH nIH cIH =>
      dsimp only [RawTerm.rename]; rw [sIH rho1 rho2, nIH rho1 rho2, cIH rho1 rho2]
  | eitherInl v vIH => simp only [RawTerm.rename]; rw [vIH rho1 rho2]
  | eitherInr v vIH => simp only [RawTerm.rename]; rw [vIH rho1 rho2]
  | eitherMatch s l r sIH lIH rIH =>
      dsimp only [RawTerm.rename]; rw [sIH rho1 rho2, lIH rho1 rho2, rIH rho1 rho2]
  | refl witness witnessIH => simp only [RawTerm.rename]; rw [witnessIH rho1 rho2]
  | idJ base witness baseIH witnessIH =>
      dsimp only [RawTerm.rename]; rw [baseIH rho1 rho2, witnessIH rho1 rho2]
  | modIntro inner innerIH => simp only [RawTerm.rename]; rw [innerIH rho1 rho2]
  | modElim inner innerIH => simp only [RawTerm.rename]; rw [innerIH rho1 rho2]
  | subsume inner innerIH => simp only [RawTerm.rename]; rw [innerIH rho1 rho2]
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH => simp only [RawTerm.rename]; rw [iIH rho1 rho2]
  | intervalMeet l r lIH rIH =>
      dsimp only [RawTerm.rename]; rw [lIH rho1 rho2, rIH rho1 rho2]
  | intervalJoin l r lIH rIH =>
      dsimp only [RawTerm.rename]; rw [lIH rho1 rho2, rIH rho1 rho2]
  | pathLam body bodyIH =>
      dsimp only [RawTerm.rename]
      rw [bodyIH rho1.lift rho2.lift]
      congr 1
      apply RawTerm.rename_pointwise
      intro position
      cases position with
      | mk val isLt =>
        cases val with
        | zero => rfl
        | succ k => rfl
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      dsimp only [RawTerm.rename]; rw [pathIH rho1 rho2, intervalIH rho1 rho2]
  | glueIntro baseValue partialValue baseIH partialIH =>
      dsimp only [RawTerm.rename]; rw [baseIH rho1 rho2, partialIH rho1 rho2]
  | glueElim gluedValue gluedIH =>
      dsimp only [RawTerm.rename]; rw [gluedIH rho1 rho2]
  | transp path source pathIH sourceIH =>
      dsimp only [RawTerm.rename]; rw [pathIH rho1 rho2, sourceIH rho1 rho2]
  | hcomp sides cap sidesIH capIH =>
      dsimp only [RawTerm.rename]; rw [sidesIH rho1 rho2, capIH rho1 rho2]
  | oeqRefl witness witnessIH =>
      dsimp only [RawTerm.rename]; rw [witnessIH rho1 rho2]
  | oeqJ baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.rename]; rw [baseIH rho1 rho2, witnessIH rho1 rho2]
  | oeqFunext pointwiseEquality pointwiseIH =>
      dsimp only [RawTerm.rename]; rw [pointwiseIH rho1 rho2]
  | idStrictRefl witness witnessIH =>
      dsimp only [RawTerm.rename]; rw [witnessIH rho1 rho2]
  | idStrictRec baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.rename]; rw [baseIH rho1 rho2, witnessIH rho1 rho2]
  | equivIntro fwd bwd fwdIH bwdIH =>
      dsimp only [RawTerm.rename]; rw [fwdIH rho1 rho2, bwdIH rho1 rho2]
  | equivApp equivTerm argument equivIH argIH =>
      dsimp only [RawTerm.rename]; rw [equivIH rho1 rho2, argIH rho1 rho2]
  | refineIntro rawValue predicateProof valueIH proofIH =>
      dsimp only [RawTerm.rename]; rw [valueIH rho1 rho2, proofIH rho1 rho2]
  | refineElim refinedValue refinedIH =>
      dsimp only [RawTerm.rename]; rw [refinedIH rho1 rho2]
  | recordIntro firstField firstIH =>
      dsimp only [RawTerm.rename]; rw [firstIH rho1 rho2]
  | recordProj recordValue recordIH =>
      dsimp only [RawTerm.rename]; rw [recordIH rho1 rho2]
  | codataUnfold initialState transition stateIH transIH =>
      dsimp only [RawTerm.rename]; rw [stateIH rho1 rho2, transIH rho1 rho2]
  | codataDest codataValue codataIH =>
      dsimp only [RawTerm.rename]; rw [codataIH rho1 rho2]
  | sessionSend channel payload chIH payloadIH =>
      dsimp only [RawTerm.rename]; rw [chIH rho1 rho2, payloadIH rho1 rho2]
  | sessionRecv channel chIH =>
      dsimp only [RawTerm.rename]; rw [chIH rho1 rho2]
  | effectPerform operationTag arguments tagIH argsIH =>
      dsimp only [RawTerm.rename]; rw [tagIH rho1 rho2, argsIH rho1 rho2]
  | universeCode innerLevel => rfl
  -- CUMUL-2.1 per-shape type codes.
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.rename]; rw [domainIH rho1 rho2, codomainIH rho1 rho2]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.rename]
      rw [domainIH rho1 rho2, codomainIH rho1.lift rho2.lift]
      congr 1
      apply RawTerm.rename_pointwise
      intro position
      cases position with
      | mk val isLt =>
        cases val with
        | zero => rfl
        | succ k => rfl
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.rename]
      rw [domainIH rho1 rho2, codomainIH rho1.lift rho2.lift]
      congr 1
      apply RawTerm.rename_pointwise
      intro position
      cases position with
      | mk val isLt =>
        cases val with
        | zero => rfl
        | succ k => rfl
  | productCode firstCode secondCode firstIH secondIH =>
      dsimp only [RawTerm.rename]; rw [firstIH rho1 rho2, secondIH rho1 rho2]
  | sumCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.rename]; rw [leftIH rho1 rho2, rightIH rho1 rho2]
  | listCode elementCode elementIH =>
      dsimp only [RawTerm.rename]; rw [elementIH rho1 rho2]
  | optionCode elementCode elementIH =>
      dsimp only [RawTerm.rename]; rw [elementIH rho1 rho2]
  | eitherCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.rename]; rw [leftIH rho1 rho2, rightIH rho1 rho2]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      dsimp only [RawTerm.rename]
      rw [typeIH rho1 rho2, leftIH rho1 rho2, rightIH rho1 rho2]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      dsimp only [RawTerm.rename]; rw [leftIH rho1 rho2, rightIH rho1 rho2]
  | cumulUpMarker innerCodeRaw innerIH =>
      dsimp only [RawTerm.rename]; rw [innerIH rho1 rho2]
  | uaToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.rename]; rw [proofIH rho1 rho2]
  | equivApply equivRaw argRaw equivIH argIH =>
      dsimp only [RawTerm.rename]; rw [equivIH rho1 rho2, argIH rho1 rho2]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      dsimp only [RawTerm.rename]; rw [leftIH rho1 rho2, rightIH rho1 rho2]
  | idToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.rename]; rw [proofIH rho1 rho2]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      dsimp only [RawTerm.rename]; rw [firstIH rho1 rho2, secondIH rho1 rho2]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      dsimp only [RawTerm.rename]; rw [firstIH rho1 rho2, secondIH rho1 rho2]
  | transpFill pathTy currentInterval source pathIH intervalIH sourceIH =>
      dsimp only [RawTerm.rename]
      rw [pathIH rho1 rho2, intervalIH rho1 rho2, sourceIH rho1 rho2]

/-- The load-bearing weaken/lift commute identity (pointwise).
    `weaken.compose rho.lift = rho.compose weaken` per position. -/
theorem RawRenaming.weaken_lift_commute {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) :
    ∀ position, rho.lift (RawRenaming.weaken position) =
                RawRenaming.weaken (rho position) :=
  fun _ => rfl

/-- weaken-after-rename equals rename-after-weaken on raw terms. -/
theorem RawTerm.weaken_rename_commute {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) (term : RawTerm sourceScope) :
    term.weaken.rename rho.lift = (term.rename rho).weaken := by
  show (term.rename RawRenaming.weaken).rename rho.lift =
       (term.rename rho).rename RawRenaming.weaken
  rw [RawTerm.rename_compose RawRenaming.weaken rho.lift term,
      RawTerm.rename_compose rho RawRenaming.weaken term]
  exact RawTerm.rename_pointwise (RawRenaming.weaken_lift_commute rho) term

end LeanFX2
