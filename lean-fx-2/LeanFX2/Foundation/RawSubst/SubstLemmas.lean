import LeanFX2.Foundation.RawSubst.SubstDefs

/-! # LeanFX2.Foundation.RawSubst.SubstLemmas

Pointwise + composition lemmas for `RawTerm.subst` plus the
cross-direction `rename_subst_commute` / `subst_rename_commute` /
`subst_compose` ladder. Implements the BHKM ScR / RcS / ScS fusion
lemmas at the raw-substitution layer.

## Root status

Structural induction over `RawTerm`; strict zero-axiom. Load-bearing
for `Term.rename` appPi/pair/snd cases downstream. -/

namespace LeanFX2

/-! ## Pointwise + composition lemmas for raw substitution.

Mirror of the renaming-side foundation: `subst_pointwise`,
`subst_compose`, and the cross-direction `rename_subst_commute` /
`subst_rename_commute` lemmas needed by `Ty.subst0_rename_commute`
(load-bearing for the typed `Term.rename`'s appPi/pair/snd cases).

All proofs use the same induction-tactic pattern as the rename
lemmas: structural induction on the term, simp + rw chain through
each ctor, lift-side properties propagated via dedicated pointwise
lemmas.  All zero-axiom (recursor-based, no propext leak). -/

/-- Lift respects pointwise equality on substitutions. -/
theorem RawTermSubst.lift_pointwise {sourceScope targetScope : Nat}
    {sigma1 sigma2 : RawTermSubst sourceScope targetScope}
    (substEq : ∀ position, sigma1 position = sigma2 position) :
    ∀ position, sigma1.lift position = sigma2.lift position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      simp only [RawTermSubst.lift]
      rw [substEq ⟨k, Nat.lt_of_succ_lt_succ h⟩]

/-- RawTerm.subst respects pointwise substitution equality. -/
theorem RawTerm.subst_pointwise {sourceScope targetScope : Nat}
    {sigma1 sigma2 : RawTermSubst sourceScope targetScope}
    (substEq : ∀ position, sigma1 position = sigma2 position) :
    ∀ (term : RawTerm sourceScope), term.subst sigma1 = term.subst sigma2 := by
  intro term
  induction term generalizing targetScope with
  | var position =>
      dsimp only [RawTerm.subst]; rw [substEq position]
  | unit => rfl
  | lam body bodyIH =>
      dsimp only [RawTerm.subst]
      rw [bodyIH (RawTermSubst.lift_pointwise substEq)]
  | app fn arg fnIH argIH =>
      dsimp only [RawTerm.subst]; rw [fnIH substEq, argIH substEq]
  | pair fv sv fvIH svIH =>
      dsimp only [RawTerm.subst]; rw [fvIH substEq, svIH substEq]
  | fst pairTerm pairIH =>
      dsimp only [RawTerm.subst]; rw [pairIH substEq]
  | snd pairTerm pairIH =>
      dsimp only [RawTerm.subst]; rw [pairIH substEq]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      dsimp only [RawTerm.subst]; rw [sIH substEq, tIH substEq, eIH substEq]
  | natZero => rfl
  | natSucc p pIH =>
      dsimp only [RawTerm.subst]; rw [pIH substEq]
  | natElim s z c sIH zIH cIH =>
      dsimp only [RawTerm.subst]; rw [sIH substEq, zIH substEq, cIH substEq]
  | natRec s z c sIH zIH cIH =>
      dsimp only [RawTerm.subst]; rw [sIH substEq, zIH substEq, cIH substEq]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      dsimp only [RawTerm.subst]; rw [headIH substEq, tailIH substEq]
  | listElim s n c sIH nIH cIH =>
      dsimp only [RawTerm.subst]; rw [sIH substEq, nIH substEq, cIH substEq]
  | optionNone => rfl
  | optionSome v vIH =>
      dsimp only [RawTerm.subst]; rw [vIH substEq]
  | optionMatch s n c sIH nIH cIH =>
      dsimp only [RawTerm.subst]; rw [sIH substEq, nIH substEq, cIH substEq]
  | eitherInl v vIH =>
      dsimp only [RawTerm.subst]; rw [vIH substEq]
  | eitherInr v vIH =>
      dsimp only [RawTerm.subst]; rw [vIH substEq]
  | eitherMatch s l r sIH lIH rIH =>
      dsimp only [RawTerm.subst]; rw [sIH substEq, lIH substEq, rIH substEq]
  | refl witness witnessIH =>
      dsimp only [RawTerm.subst]; rw [witnessIH substEq]
  | idJ base witness baseIH witnessIH =>
      dsimp only [RawTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  | modIntro inner innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH substEq]
  | modElim inner innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH substEq]
  | subsume inner innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH substEq]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      dsimp only [RawTerm.subst]; rw [iIH substEq]
  | intervalMeet l r lIH rIH =>
      dsimp only [RawTerm.subst]; rw [lIH substEq, rIH substEq]
  | intervalJoin l r lIH rIH =>
      dsimp only [RawTerm.subst]; rw [lIH substEq, rIH substEq]
  | pathLam body bodyIH =>
      dsimp only [RawTerm.subst]
      rw [bodyIH (RawTermSubst.lift_pointwise substEq)]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      dsimp only [RawTerm.subst]; rw [pathIH substEq, intervalIH substEq]
  | glueIntro baseValue partialValue baseIH partialIH =>
      dsimp only [RawTerm.subst]; rw [baseIH substEq, partialIH substEq]
  | glueElim gluedValue gluedIH =>
      dsimp only [RawTerm.subst]; rw [gluedIH substEq]
  | transp path source pathIH sourceIH =>
      dsimp only [RawTerm.subst]; rw [pathIH substEq, sourceIH substEq]
  | hcomp sides cap sidesIH capIH =>
      dsimp only [RawTerm.subst]; rw [sidesIH substEq, capIH substEq]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      dsimp only [RawTerm.subst]; rw [witnessIH substEq]
  | oeqJ baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  | oeqFunext pointwiseEquality pointwiseIH =>
      dsimp only [RawTerm.subst]; rw [pointwiseIH substEq]
  | idStrictRefl witness witnessIH =>
      dsimp only [RawTerm.subst]; rw [witnessIH substEq]
  | idStrictRec baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      dsimp only [RawTerm.subst]; rw [fwdIH substEq, bwdIH substEq]
  | equivApp equivTerm argument equivIH argIH =>
      dsimp only [RawTerm.subst]; rw [equivIH substEq, argIH substEq]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      dsimp only [RawTerm.subst]; rw [valueIH substEq, proofIH substEq]
  | refineElim refinedValue refinedIH =>
      dsimp only [RawTerm.subst]; rw [refinedIH substEq]
  | recordIntro firstField firstIH =>
      dsimp only [RawTerm.subst]; rw [firstIH substEq]
  | recordProj recordValue recordIH =>
      dsimp only [RawTerm.subst]; rw [recordIH substEq]
  | codataUnfold initialState transition stateIH transIH =>
      dsimp only [RawTerm.subst]; rw [stateIH substEq, transIH substEq]
  | codataDest codataValue codataIH =>
      dsimp only [RawTerm.subst]; rw [codataIH substEq]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      dsimp only [RawTerm.subst]; rw [chIH substEq, payloadIH substEq]
  | sessionRecv channel chIH =>
      dsimp only [RawTerm.subst]; rw [chIH substEq]
  | effectPerform operationTag arguments tagIH argsIH =>
      dsimp only [RawTerm.subst]; rw [tagIH substEq, argsIH substEq]
  | universeCode innerLevel => rfl
  -- CUMUL-2.1 per-shape type codes.
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst]; rw [domainIH substEq, codomainIH substEq]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst]
      rw [domainIH substEq, codomainIH (RawTermSubst.lift_pointwise substEq)]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst]
      rw [domainIH substEq, codomainIH (RawTermSubst.lift_pointwise substEq)]
  | productCode firstCode secondCode firstIH secondIH =>
      dsimp only [RawTerm.subst]; rw [firstIH substEq, secondIH substEq]
  | sumCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH substEq, rightIH substEq]
  | listCode elementCode elementIH =>
      dsimp only [RawTerm.subst]; rw [elementIH substEq]
  | optionCode elementCode elementIH =>
      dsimp only [RawTerm.subst]; rw [elementIH substEq]
  | eitherCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH substEq, rightIH substEq]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      dsimp only [RawTerm.subst]
      rw [typeIH substEq, leftIH substEq, rightIH substEq]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH substEq, rightIH substEq]
  | cumulUpMarker innerCodeRaw innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH substEq]
  | uaToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.subst]; rw [proofIH substEq]
  | equivApply equivRaw argRaw equivIH argIH =>
      dsimp only [RawTerm.subst]; rw [equivIH substEq, argIH substEq]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH substEq, rightIH substEq]
  | idToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.subst]; rw [proofIH substEq]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      dsimp only [RawTerm.subst]; rw [firstIH substEq, secondIH substEq]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      dsimp only [RawTerm.subst]; rw [firstIH substEq, secondIH substEq]
  | transpFill pathTy currentInterval source pathIH intervalIH sourceIH =>
      dsimp only [RawTerm.subst]
      rw [pathIH substEq, intervalIH substEq, sourceIH substEq]

/-! ### Cross-direction: rename-after-subst and subst-after-rename. -/

/-- Lifted-renamed substitution agrees pointwise: substituting after
renaming = substituting under the renamed positions. -/
theorem RawTermSubst.lift_renaming_pull {sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : RawTermSubst middleScope targetScope) :
    ∀ position,
      sigma.lift (rho.lift position) =
        RawTermSubst.lift (fun i => sigma (rho i)) position
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- rename-then-subst factors through pre-composed substitution. -/
theorem RawTerm.rename_subst_commute {sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : RawTermSubst middleScope targetScope)
    (term : RawTerm sourceScope) :
    (term.rename rho).subst sigma = term.subst (fun position => sigma (rho position)) := by
  induction term generalizing middleScope targetScope with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [bodyIH rho.lift sigma.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_renaming_pull rho sigma
  | app fn arg fnIH argIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [fnIH rho sigma, argIH rho sigma]
  | pair fv sv fvIH svIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [fvIH rho sigma, svIH rho sigma]
  | fst pairTerm pairIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [pairIH rho sigma]
  | snd pairTerm pairIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [pairIH rho sigma]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, tIH rho sigma, eIH rho sigma]
  | natZero => rfl
  | natSucc p pIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [pIH rho sigma]
  | natElim s z c sIH zIH cIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, zIH rho sigma, cIH rho sigma]
  | natRec s z c sIH zIH cIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, zIH rho sigma, cIH rho sigma]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [headIH rho sigma, tailIH rho sigma]
  | listElim s n c sIH nIH cIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, nIH rho sigma, cIH rho sigma]
  | optionNone => rfl
  | optionSome v vIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [vIH rho sigma]
  | optionMatch s n c sIH nIH cIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, nIH rho sigma, cIH rho sigma]
  | eitherInl v vIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [vIH rho sigma]
  | eitherInr v vIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [vIH rho sigma]
  | eitherMatch s l r sIH lIH rIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, lIH rho sigma, rIH rho sigma]
  | refl witness witnessIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [witnessIH rho sigma]
  | idJ base witness baseIH witnessIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [baseIH rho sigma, witnessIH rho sigma]
  | modIntro inner innerIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [innerIH rho sigma]
  | modElim inner innerIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [innerIH rho sigma]
  | subsume inner innerIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [innerIH rho sigma]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [iIH rho sigma]
  | intervalMeet l r lIH rIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [lIH rho sigma, rIH rho sigma]
  | intervalJoin l r lIH rIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [lIH rho sigma, rIH rho sigma]
  | pathLam body bodyIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [bodyIH rho.lift sigma.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_renaming_pull rho sigma
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [pathIH rho sigma, intervalIH rho sigma]
  | glueIntro baseValue partialValue baseIH partialIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [baseIH rho sigma, partialIH rho sigma]
  | glueElim gluedValue gluedIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [gluedIH rho sigma]
  | transp path source pathIH sourceIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [pathIH rho sigma, sourceIH rho sigma]
  | hcomp sides cap sidesIH capIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [sidesIH rho sigma, capIH rho sigma]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [witnessIH rho sigma]
  | oeqJ baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [baseIH rho sigma, witnessIH rho sigma]
  | oeqFunext pointwiseEquality pointwiseIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [pointwiseIH rho sigma]
  | idStrictRefl witness witnessIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [witnessIH rho sigma]
  | idStrictRec baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [baseIH rho sigma, witnessIH rho sigma]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [fwdIH rho sigma, bwdIH rho sigma]
  | equivApp equivTerm argument equivIH argIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [equivIH rho sigma, argIH rho sigma]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [valueIH rho sigma, proofIH rho sigma]
  | refineElim refinedValue refinedIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [refinedIH rho sigma]
  | recordIntro firstField firstIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [firstIH rho sigma]
  | recordProj recordValue recordIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [recordIH rho sigma]
  | codataUnfold initialState transition stateIH transIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [stateIH rho sigma, transIH rho sigma]
  | codataDest codataValue codataIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [codataIH rho sigma]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [chIH rho sigma, payloadIH rho sigma]
  | sessionRecv channel chIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [chIH rho sigma]
  | effectPerform operationTag arguments tagIH argsIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [tagIH rho sigma, argsIH rho sigma]
  | universeCode innerLevel => rfl
  -- CUMUL-2.1 per-shape type codes.
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [domainIH rho sigma, codomainIH rho sigma]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [domainIH rho sigma, codomainIH rho.lift sigma.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_renaming_pull rho sigma
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [domainIH rho sigma, codomainIH rho.lift sigma.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_renaming_pull rho sigma
  | productCode firstCode secondCode firstIH secondIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [firstIH rho sigma, secondIH rho sigma]
  | sumCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [leftIH rho sigma, rightIH rho sigma]
  | listCode elementCode elementIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [elementIH rho sigma]
  | optionCode elementCode elementIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [elementIH rho sigma]
  | eitherCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [leftIH rho sigma, rightIH rho sigma]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [typeIH rho sigma, leftIH rho sigma, rightIH rho sigma]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [leftIH rho sigma, rightIH rho sigma]
  | cumulUpMarker innerCodeRaw innerIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [innerIH rho sigma]
  | uaToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [proofIH rho sigma]
  | equivApply equivRaw argRaw equivIH argIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [equivIH rho sigma, argIH rho sigma]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [leftIH rho sigma, rightIH rho sigma]
  | idToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]; rw [proofIH rho sigma]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [firstIH rho sigma, secondIH rho sigma]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [firstIH rho sigma, secondIH rho sigma]
  | transpFill pathTy currentInterval source pathIH intervalIH sourceIH =>
      dsimp only [RawTerm.rename, RawTerm.subst]
      rw [pathIH rho sigma, intervalIH rho sigma, sourceIH rho sigma]

/-- Lifted-then-renamed substitution agrees pointwise with renamed-then-lifted. -/
theorem RawTermSubst.lift_then_rename_lift {sourceScope middleScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope) :
    ∀ position,
      (sigma.lift position).rename rho.lift =
        RawTermSubst.lift (fun i => (sigma i).rename rho) position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      simp only [RawTermSubst.lift]
      rw [RawTerm.rename_compose RawRenaming.weaken rho.lift
            (sigma ⟨k, Nat.lt_of_succ_lt_succ h⟩),
          RawTerm.rename_compose rho RawRenaming.weaken
            (sigma ⟨k, Nat.lt_of_succ_lt_succ h⟩)]
      apply RawTerm.rename_pointwise
      intro p
      exact RawRenaming.weaken_lift_commute rho p

/-- subst-then-rename factors through post-composed substitution. -/
theorem RawTerm.subst_rename_commute {sourceScope middleScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope)
    (term : RawTerm sourceScope) :
    (term.subst sigma).rename rho =
      term.subst (fun position => (sigma position).rename rho) := by
  induction term generalizing middleScope targetScope with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [bodyIH sigma.lift rho.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_then_rename_lift sigma rho
  | app fn arg fnIH argIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [fnIH sigma rho, argIH sigma rho]
  | pair fv sv fvIH svIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [fvIH sigma rho, svIH sigma rho]
  | fst pairTerm pairIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [pairIH sigma rho]
  | snd pairTerm pairIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [pairIH sigma rho]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, tIH sigma rho, eIH sigma rho]
  | natZero => rfl
  | natSucc p pIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [pIH sigma rho]
  | natElim s z c sIH zIH cIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, zIH sigma rho, cIH sigma rho]
  | natRec s z c sIH zIH cIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, zIH sigma rho, cIH sigma rho]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [headIH sigma rho, tailIH sigma rho]
  | listElim s n c sIH nIH cIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, nIH sigma rho, cIH sigma rho]
  | optionNone => rfl
  | optionSome v vIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [vIH sigma rho]
  | optionMatch s n c sIH nIH cIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, nIH sigma rho, cIH sigma rho]
  | eitherInl v vIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [vIH sigma rho]
  | eitherInr v vIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [vIH sigma rho]
  | eitherMatch s l r sIH lIH rIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, lIH sigma rho, rIH sigma rho]
  | refl witness witnessIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [witnessIH sigma rho]
  | idJ base witness baseIH witnessIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [baseIH sigma rho, witnessIH sigma rho]
  | modIntro inner innerIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [innerIH sigma rho]
  | modElim inner innerIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [innerIH sigma rho]
  | subsume inner innerIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [innerIH sigma rho]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [iIH sigma rho]
  | intervalMeet l r lIH rIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [lIH sigma rho, rIH sigma rho]
  | intervalJoin l r lIH rIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [lIH sigma rho, rIH sigma rho]
  | pathLam body bodyIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [bodyIH sigma.lift rho.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_then_rename_lift sigma rho
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [pathIH sigma rho, intervalIH sigma rho]
  | glueIntro baseValue partialValue baseIH partialIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [baseIH sigma rho, partialIH sigma rho]
  | glueElim gluedValue gluedIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [gluedIH sigma rho]
  | transp path source pathIH sourceIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [pathIH sigma rho, sourceIH sigma rho]
  | hcomp sides cap sidesIH capIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [sidesIH sigma rho, capIH sigma rho]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [witnessIH sigma rho]
  | oeqJ baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [baseIH sigma rho, witnessIH sigma rho]
  | oeqFunext pointwiseEquality pointwiseIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [pointwiseIH sigma rho]
  | idStrictRefl witness witnessIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [witnessIH sigma rho]
  | idStrictRec baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [baseIH sigma rho, witnessIH sigma rho]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [fwdIH sigma rho, bwdIH sigma rho]
  | equivApp equivTerm argument equivIH argIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [equivIH sigma rho, argIH sigma rho]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [valueIH sigma rho, proofIH sigma rho]
  | refineElim refinedValue refinedIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [refinedIH sigma rho]
  | recordIntro firstField firstIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [firstIH sigma rho]
  | recordProj recordValue recordIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [recordIH sigma rho]
  | codataUnfold initialState transition stateIH transIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [stateIH sigma rho, transIH sigma rho]
  | codataDest codataValue codataIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [codataIH sigma rho]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [chIH sigma rho, payloadIH sigma rho]
  | sessionRecv channel chIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [chIH sigma rho]
  | effectPerform operationTag arguments tagIH argsIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [tagIH sigma rho, argsIH sigma rho]
  | universeCode innerLevel => rfl
  -- CUMUL-2.1 per-shape type codes.
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [domainIH sigma rho, codomainIH sigma rho]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [domainIH sigma rho, codomainIH sigma.lift rho.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_then_rename_lift sigma rho
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [domainIH sigma rho, codomainIH sigma.lift rho.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_then_rename_lift sigma rho
  | productCode firstCode secondCode firstIH secondIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [firstIH sigma rho, secondIH sigma rho]
  | sumCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [leftIH sigma rho, rightIH sigma rho]
  | listCode elementCode elementIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [elementIH sigma rho]
  | optionCode elementCode elementIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [elementIH sigma rho]
  | eitherCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [leftIH sigma rho, rightIH sigma rho]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [typeIH sigma rho, leftIH sigma rho, rightIH sigma rho]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [leftIH sigma rho, rightIH sigma rho]
  | cumulUpMarker innerCodeRaw innerIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [innerIH sigma rho]
  | uaToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [proofIH sigma rho]
  | equivApply equivRaw argRaw equivIH argIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [equivIH sigma rho, argIH sigma rho]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [leftIH sigma rho, rightIH sigma rho]
  | idToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]; rw [proofIH sigma rho]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [firstIH sigma rho, secondIH sigma rho]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [firstIH sigma rho, secondIH sigma rho]
  | transpFill pathTy currentInterval source pathIH intervalIH sourceIH =>
      dsimp only [RawTerm.subst, RawTerm.rename]
      rw [pathIH sigma rho, intervalIH sigma rho, sourceIH sigma rho]

/-! ### subst-subst composition. -/

/-- Compose two substitutions: substituting by the first, then the
second, equals substituting once by the composed substitution. -/
@[reducible] def RawTermSubst.compose {sourceScope middleScope targetScope : Nat}
    (sigma1 : RawTermSubst sourceScope middleScope)
    (sigma2 : RawTermSubst middleScope targetScope) :
    RawTermSubst sourceScope targetScope :=
  fun position => (sigma1 position).subst sigma2

/-- Lift commutes with substitution composition (pointwise). -/
theorem RawTermSubst.lift_compose_pointwise {sourceScope middleScope targetScope : Nat}
    (sigma1 : RawTermSubst sourceScope middleScope)
    (sigma2 : RawTermSubst middleScope targetScope) :
    ∀ position,
      (RawTermSubst.compose sigma1 sigma2).lift position =
        RawTermSubst.compose sigma1.lift sigma2.lift position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      simp only [RawTermSubst.lift, RawTermSubst.compose]
      rw [RawTerm.subst_rename_commute sigma2 RawRenaming.weaken
            (sigma1 ⟨k, Nat.lt_of_succ_lt_succ h⟩),
          RawTerm.rename_subst_commute RawRenaming.weaken sigma2.lift
            (sigma1 ⟨k, Nat.lt_of_succ_lt_succ h⟩)]
      apply RawTerm.subst_pointwise
      intro p
      cases p with
      | mk val isLt => rfl

/-- Substitution composes: applying two substitutions sequentially
equals applying the composed substitution once. -/
theorem RawTerm.subst_compose {sourceScope middleScope targetScope : Nat}
    (sigma1 : RawTermSubst sourceScope middleScope)
    (sigma2 : RawTermSubst middleScope targetScope)
    (term : RawTerm sourceScope) :
    (term.subst sigma1).subst sigma2 =
      term.subst (RawTermSubst.compose sigma1 sigma2) := by
  induction term generalizing middleScope targetScope with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      dsimp only [RawTerm.subst]
      rw [bodyIH sigma1.lift sigma2.lift]
      congr 1
      apply RawTerm.subst_pointwise
      intro p
      exact (RawTermSubst.lift_compose_pointwise sigma1 sigma2 p).symm
  | app fn arg fnIH argIH =>
      dsimp only [RawTerm.subst]; rw [fnIH sigma1 sigma2, argIH sigma1 sigma2]
  | pair fv sv fvIH svIH =>
      dsimp only [RawTerm.subst]; rw [fvIH sigma1 sigma2, svIH sigma1 sigma2]
  | fst pairTerm pairIH =>
      dsimp only [RawTerm.subst]; rw [pairIH sigma1 sigma2]
  | snd pairTerm pairIH =>
      dsimp only [RawTerm.subst]; rw [pairIH sigma1 sigma2]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      dsimp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, tIH sigma1 sigma2, eIH sigma1 sigma2]
  | natZero => rfl
  | natSucc p pIH =>
      dsimp only [RawTerm.subst]; rw [pIH sigma1 sigma2]
  | natElim s z c sIH zIH cIH =>
      dsimp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, zIH sigma1 sigma2, cIH sigma1 sigma2]
  | natRec s z c sIH zIH cIH =>
      dsimp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, zIH sigma1 sigma2, cIH sigma1 sigma2]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      dsimp only [RawTerm.subst]
      rw [headIH sigma1 sigma2, tailIH sigma1 sigma2]
  | listElim s n c sIH nIH cIH =>
      dsimp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, nIH sigma1 sigma2, cIH sigma1 sigma2]
  | optionNone => rfl
  | optionSome v vIH =>
      dsimp only [RawTerm.subst]; rw [vIH sigma1 sigma2]
  | optionMatch s n c sIH nIH cIH =>
      dsimp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, nIH sigma1 sigma2, cIH sigma1 sigma2]
  | eitherInl v vIH =>
      dsimp only [RawTerm.subst]; rw [vIH sigma1 sigma2]
  | eitherInr v vIH =>
      dsimp only [RawTerm.subst]; rw [vIH sigma1 sigma2]
  | eitherMatch s l r sIH lIH rIH =>
      dsimp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, lIH sigma1 sigma2, rIH sigma1 sigma2]
  | refl witness witnessIH =>
      dsimp only [RawTerm.subst]; rw [witnessIH sigma1 sigma2]
  | idJ base witness baseIH witnessIH =>
      dsimp only [RawTerm.subst]
      rw [baseIH sigma1 sigma2, witnessIH sigma1 sigma2]
  | modIntro inner innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH sigma1 sigma2]
  | modElim inner innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH sigma1 sigma2]
  | subsume inner innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH sigma1 sigma2]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      dsimp only [RawTerm.subst]; rw [iIH sigma1 sigma2]
  | intervalMeet l r lIH rIH =>
      dsimp only [RawTerm.subst]; rw [lIH sigma1 sigma2, rIH sigma1 sigma2]
  | intervalJoin l r lIH rIH =>
      dsimp only [RawTerm.subst]; rw [lIH sigma1 sigma2, rIH sigma1 sigma2]
  | pathLam body bodyIH =>
      dsimp only [RawTerm.subst]
      rw [bodyIH sigma1.lift sigma2.lift]
      congr 1
      apply RawTerm.subst_pointwise
      intro p
      exact (RawTermSubst.lift_compose_pointwise sigma1 sigma2 p).symm
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      dsimp only [RawTerm.subst]; rw [pathIH sigma1 sigma2, intervalIH sigma1 sigma2]
  | glueIntro baseValue partialValue baseIH partialIH =>
      dsimp only [RawTerm.subst]; rw [baseIH sigma1 sigma2, partialIH sigma1 sigma2]
  | glueElim gluedValue gluedIH =>
      dsimp only [RawTerm.subst]; rw [gluedIH sigma1 sigma2]
  | transp path source pathIH sourceIH =>
      dsimp only [RawTerm.subst]; rw [pathIH sigma1 sigma2, sourceIH sigma1 sigma2]
  | hcomp sides cap sidesIH capIH =>
      dsimp only [RawTerm.subst]; rw [sidesIH sigma1 sigma2, capIH sigma1 sigma2]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      dsimp only [RawTerm.subst]; rw [witnessIH sigma1 sigma2]
  | oeqJ baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.subst]; rw [baseIH sigma1 sigma2, witnessIH sigma1 sigma2]
  | oeqFunext pointwiseEquality pointwiseIH =>
      dsimp only [RawTerm.subst]; rw [pointwiseIH sigma1 sigma2]
  | idStrictRefl witness witnessIH =>
      dsimp only [RawTerm.subst]; rw [witnessIH sigma1 sigma2]
  | idStrictRec baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.subst]; rw [baseIH sigma1 sigma2, witnessIH sigma1 sigma2]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      dsimp only [RawTerm.subst]; rw [fwdIH sigma1 sigma2, bwdIH sigma1 sigma2]
  | equivApp equivTerm argument equivIH argIH =>
      dsimp only [RawTerm.subst]; rw [equivIH sigma1 sigma2, argIH sigma1 sigma2]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      dsimp only [RawTerm.subst]; rw [valueIH sigma1 sigma2, proofIH sigma1 sigma2]
  | refineElim refinedValue refinedIH =>
      dsimp only [RawTerm.subst]; rw [refinedIH sigma1 sigma2]
  | recordIntro firstField firstIH =>
      dsimp only [RawTerm.subst]; rw [firstIH sigma1 sigma2]
  | recordProj recordValue recordIH =>
      dsimp only [RawTerm.subst]; rw [recordIH sigma1 sigma2]
  | codataUnfold initialState transition stateIH transIH =>
      dsimp only [RawTerm.subst]; rw [stateIH sigma1 sigma2, transIH sigma1 sigma2]
  | codataDest codataValue codataIH =>
      dsimp only [RawTerm.subst]; rw [codataIH sigma1 sigma2]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      dsimp only [RawTerm.subst]; rw [chIH sigma1 sigma2, payloadIH sigma1 sigma2]
  | sessionRecv channel chIH =>
      dsimp only [RawTerm.subst]; rw [chIH sigma1 sigma2]
  | effectPerform operationTag arguments tagIH argsIH =>
      dsimp only [RawTerm.subst]; rw [tagIH sigma1 sigma2, argsIH sigma1 sigma2]
  | universeCode innerLevel => rfl
  -- CUMUL-2.1 per-shape type codes.
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst]
      rw [domainIH sigma1 sigma2, codomainIH sigma1 sigma2]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst]
      rw [domainIH sigma1 sigma2, codomainIH sigma1.lift sigma2.lift]
      congr 1
      apply RawTerm.subst_pointwise
      intro position
      exact (RawTermSubst.lift_compose_pointwise sigma1 sigma2 position).symm
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst]
      rw [domainIH sigma1 sigma2, codomainIH sigma1.lift sigma2.lift]
      congr 1
      apply RawTerm.subst_pointwise
      intro position
      exact (RawTermSubst.lift_compose_pointwise sigma1 sigma2 position).symm
  | productCode firstCode secondCode firstIH secondIH =>
      dsimp only [RawTerm.subst]; rw [firstIH sigma1 sigma2, secondIH sigma1 sigma2]
  | sumCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH sigma1 sigma2, rightIH sigma1 sigma2]
  | listCode elementCode elementIH =>
      dsimp only [RawTerm.subst]; rw [elementIH sigma1 sigma2]
  | optionCode elementCode elementIH =>
      dsimp only [RawTerm.subst]; rw [elementIH sigma1 sigma2]
  | eitherCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH sigma1 sigma2, rightIH sigma1 sigma2]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      dsimp only [RawTerm.subst]
      rw [typeIH sigma1 sigma2, leftIH sigma1 sigma2, rightIH sigma1 sigma2]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH sigma1 sigma2, rightIH sigma1 sigma2]
  | cumulUpMarker innerCodeRaw innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH sigma1 sigma2]
  | uaToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.subst]; rw [proofIH sigma1 sigma2]
  | equivApply equivRaw argRaw equivIH argIH =>
      dsimp only [RawTerm.subst]; rw [equivIH sigma1 sigma2, argIH sigma1 sigma2]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH sigma1 sigma2, rightIH sigma1 sigma2]
  | idToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.subst]; rw [proofIH sigma1 sigma2]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      dsimp only [RawTerm.subst]; rw [firstIH sigma1 sigma2, secondIH sigma1 sigma2]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      dsimp only [RawTerm.subst]; rw [firstIH sigma1 sigma2, secondIH sigma1 sigma2]
  | transpFill pathTy currentInterval source pathIH intervalIH sourceIH =>
      dsimp only [RawTerm.subst]
      rw [pathIH sigma1 sigma2, intervalIH sigma1 sigma2, sourceIH sigma1 sigma2]

end LeanFX2
