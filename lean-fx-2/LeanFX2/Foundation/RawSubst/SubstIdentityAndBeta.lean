import LeanFX2.Foundation.RawSubst.SubstLemmas

/-! # LeanFX2.Foundation.RawSubst.SubstIdentityAndBeta

Single-binder β-substitution commute, identity-substitution
identity, and the load-bearing `weaken_subst_singleton` /
`weaken_subst_commute` corollaries.

## Root status

Downstream β-reduction proofs depend on these; strict zero-axiom. -/

namespace LeanFX2

/-! ### Single-binder β-substitution commute (load-bearing).

`subst0_rename_commute`: renaming a β-redex's reduct equals β-reducing
the renamed redex.  This is what `Term.rename`'s appPi/pair/snd cases
need to discharge type-index obligations. -/

/-- Pointwise property: singleton-after-renaming = renaming-after-singleton. -/
theorem RawTermSubst.singleton_rename_commute_pointwise {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (rawArg : RawTerm sourceScope) :
    ∀ position,
      ((RawTermSubst.singleton rawArg) position).rename rho =
        (RawTermSubst.singleton (rawArg.rename rho)) (rho.lift position)
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- Renaming a single-variable substitution result equals single-variable
substitution after renaming under the lift.  Load-bearing for typed
`Term.rename` on β-redex result types. -/
theorem RawTerm.subst0_rename_commute {sourceScope targetScope : Nat}
    (body : RawTerm (sourceScope + 1))
    (rawArg : RawTerm sourceScope)
    (rho : RawRenaming sourceScope targetScope) :
    (body.subst0 rawArg).rename rho =
      (body.rename rho.lift).subst0 (rawArg.rename rho) := by
  show (body.subst (RawTermSubst.singleton rawArg)).rename rho =
       (body.rename rho.lift).subst (RawTermSubst.singleton (rawArg.rename rho))
  rw [RawTerm.subst_rename_commute (RawTermSubst.singleton rawArg) rho body,
      RawTerm.rename_subst_commute rho.lift
        (RawTermSubst.singleton (rawArg.rename rho)) body]
  apply RawTerm.subst_pointwise
  exact RawTermSubst.singleton_rename_commute_pointwise rho rawArg

/-! ### Identity substitution + load-bearing β-reduction lemmas. -/

/-- Lift of identity substitution agrees pointwise with identity. -/
theorem RawTermSubst.identity_lift_pointwise {scope : Nat} :
    ∀ position,
      (@RawTermSubst.identity scope).lift position = RawTermSubst.identity position
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- Substituting by the identity is the identity. -/
theorem RawTerm.subst_identity {scope : Nat} (term : RawTerm scope) :
    term.subst RawTermSubst.identity = term := by
  induction term with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      dsimp only [RawTerm.subst]
      rw [RawTerm.subst_pointwise RawTermSubst.identity_lift_pointwise body, bodyIH]
  | app fn arg fnIH argIH =>
      dsimp only [RawTerm.subst]; rw [fnIH, argIH]
  | pair fv sv fvIH svIH =>
      dsimp only [RawTerm.subst]; rw [fvIH, svIH]
  | fst pairTerm pairIH =>
      dsimp only [RawTerm.subst]; rw [pairIH]
  | snd pairTerm pairIH =>
      dsimp only [RawTerm.subst]; rw [pairIH]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      dsimp only [RawTerm.subst]; rw [sIH, tIH, eIH]
  | natZero => rfl
  | natSucc p pIH =>
      dsimp only [RawTerm.subst]; rw [pIH]
  | natElim s z c sIH zIH cIH =>
      dsimp only [RawTerm.subst]; rw [sIH, zIH, cIH]
  | natRec s z c sIH zIH cIH =>
      dsimp only [RawTerm.subst]; rw [sIH, zIH, cIH]
  | listNil => rfl
  | listCons h t hIH tIH =>
      dsimp only [RawTerm.subst]; rw [hIH, tIH]
  | listElim s n c sIH nIH cIH =>
      dsimp only [RawTerm.subst]; rw [sIH, nIH, cIH]
  | optionNone => rfl
  | optionSome v vIH =>
      dsimp only [RawTerm.subst]; rw [vIH]
  | optionMatch s n c sIH nIH cIH =>
      dsimp only [RawTerm.subst]; rw [sIH, nIH, cIH]
  | eitherInl v vIH =>
      dsimp only [RawTerm.subst]; rw [vIH]
  | eitherInr v vIH =>
      dsimp only [RawTerm.subst]; rw [vIH]
  | eitherMatch s l r sIH lIH rIH =>
      dsimp only [RawTerm.subst]; rw [sIH, lIH, rIH]
  | refl witness witnessIH =>
      dsimp only [RawTerm.subst]; rw [witnessIH]
  | idJ base witness baseIH witnessIH =>
      dsimp only [RawTerm.subst]; rw [baseIH, witnessIH]
  | modIntro inner innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH]
  | modElim inner innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH]
  | subsume inner innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      dsimp only [RawTerm.subst]; rw [iIH]
  | intervalMeet l r lIH rIH =>
      dsimp only [RawTerm.subst]; rw [lIH, rIH]
  | intervalJoin l r lIH rIH =>
      dsimp only [RawTerm.subst]; rw [lIH, rIH]
  | pathLam body bodyIH =>
      dsimp only [RawTerm.subst]
      rw [RawTerm.subst_pointwise RawTermSubst.identity_lift_pointwise body, bodyIH]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      dsimp only [RawTerm.subst]; rw [pathIH, intervalIH]
  | glueIntro baseValue partialValue baseIH partialIH =>
      dsimp only [RawTerm.subst]; rw [baseIH, partialIH]
  | glueElim gluedValue gluedIH =>
      dsimp only [RawTerm.subst]; rw [gluedIH]
  | transp path source pathIH sourceIH =>
      dsimp only [RawTerm.subst]; rw [pathIH, sourceIH]
  | hcomp sides cap sidesIH capIH =>
      dsimp only [RawTerm.subst]; rw [sidesIH, capIH]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      dsimp only [RawTerm.subst]; rw [witnessIH]
  | oeqJ baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.subst]; rw [baseIH, witnessIH]
  | oeqFunext pointwiseEquality pointwiseIH =>
      dsimp only [RawTerm.subst]; rw [pointwiseIH]
  | idStrictRefl witness witnessIH =>
      dsimp only [RawTerm.subst]; rw [witnessIH]
  | idStrictRec baseCase witness baseIH witnessIH =>
      dsimp only [RawTerm.subst]; rw [baseIH, witnessIH]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      dsimp only [RawTerm.subst]; rw [fwdIH, bwdIH]
  | equivApp equivTerm argument equivIH argIH =>
      dsimp only [RawTerm.subst]; rw [equivIH, argIH]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      dsimp only [RawTerm.subst]; rw [valueIH, proofIH]
  | refineElim refinedValue refinedIH =>
      dsimp only [RawTerm.subst]; rw [refinedIH]
  | recordIntro firstField firstIH =>
      dsimp only [RawTerm.subst]; rw [firstIH]
  | recordProj recordValue recordIH =>
      dsimp only [RawTerm.subst]; rw [recordIH]
  | codataUnfold initialState transition stateIH transIH =>
      dsimp only [RawTerm.subst]; rw [stateIH, transIH]
  | codataDest codataValue codataIH =>
      dsimp only [RawTerm.subst]; rw [codataIH]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      dsimp only [RawTerm.subst]; rw [chIH, payloadIH]
  | sessionRecv channel chIH =>
      dsimp only [RawTerm.subst]; rw [chIH]
  | effectPerform operationTag arguments tagIH argsIH =>
      dsimp only [RawTerm.subst]; rw [tagIH, argsIH]
  | universeCode innerLevel => rfl
  -- CUMUL-2.1 per-shape type codes.
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst]; rw [domainIH, codomainIH]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst]
      rw [RawTerm.subst_pointwise RawTermSubst.identity_lift_pointwise codomainCode,
          codomainIH, domainIH]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      dsimp only [RawTerm.subst]
      rw [RawTerm.subst_pointwise RawTermSubst.identity_lift_pointwise codomainCode,
          codomainIH, domainIH]
  | productCode firstCode secondCode firstIH secondIH =>
      dsimp only [RawTerm.subst]; rw [firstIH, secondIH]
  | sumCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH, rightIH]
  | listCode elementCode elementIH =>
      dsimp only [RawTerm.subst]; rw [elementIH]
  | optionCode elementCode elementIH =>
      dsimp only [RawTerm.subst]; rw [elementIH]
  | eitherCode leftCode rightCode leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH, rightIH]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [typeIH, leftIH, rightIH]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH, rightIH]
  | cumulUpMarker innerCodeRaw innerIH =>
      dsimp only [RawTerm.subst]; rw [innerIH]
  | uaToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.subst]; rw [proofIH]
  | equivApply equivRaw argRaw equivIH argIH =>
      dsimp only [RawTerm.subst]; rw [equivIH, argIH]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      dsimp only [RawTerm.subst]; rw [leftIH, rightIH]
  | idToEquiv proofRaw proofIH =>
      dsimp only [RawTerm.subst]; rw [proofIH]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      dsimp only [RawTerm.subst]; rw [firstIH, secondIH]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      dsimp only [RawTerm.subst]; rw [firstIH, secondIH]
  | transpFill pathTy currentInterval source pathIH intervalIH sourceIH =>
      dsimp only [RawTerm.subst]; rw [pathIH, intervalIH, sourceIH]

/-- Pre-composing weaken with a singleton (on RawTermSubst) gives the
identity substitution pointwise. -/
theorem RawTermSubst.weaken_then_singleton_pointwise {scope : Nat}
    (rawArg : RawTerm scope) :
    ∀ position,
      (RawTermSubst.singleton rawArg) (RawRenaming.weaken position) =
        RawTermSubst.identity position :=
  fun _ => rfl

/-- Weakening a raw term then substituting by a singleton returns the
original term — the load-bearing β-reduction lemma on raw terms. -/
theorem RawTerm.weaken_subst_singleton {scope : Nat}
    (term rawArg : RawTerm scope) :
    term.weaken.subst (RawTermSubst.singleton rawArg) = term := by
  show (term.rename RawRenaming.weaken).subst (RawTermSubst.singleton rawArg) = term
  rw [RawTerm.rename_subst_commute RawRenaming.weaken (RawTermSubst.singleton rawArg) term,
      RawTerm.subst_pointwise (RawTermSubst.weaken_then_singleton_pointwise rawArg) term,
      RawTerm.subst_identity term]

/-- Lift commutes with renameOutput (RawTerm side, weaken-flavor). -/
theorem RawTermSubst.weaken_lift_subst_pointwise {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) :
    ∀ position,
      sigma.lift (RawRenaming.weaken position) = (sigma position).rename RawRenaming.weaken :=
  fun _ => rfl

/-- weaken-after-subst equals subst-after-weaken on raw terms. -/
theorem RawTerm.weaken_subst_commute {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) (term : RawTerm sourceScope) :
    term.weaken.subst sigma.lift = (term.subst sigma).weaken := by
  show (term.rename RawRenaming.weaken).subst sigma.lift =
       (term.subst sigma).rename RawRenaming.weaken
  rw [RawTerm.rename_subst_commute RawRenaming.weaken sigma.lift term,
      RawTerm.subst_rename_commute sigma RawRenaming.weaken term]
  apply RawTerm.subst_pointwise
  exact RawTermSubst.weaken_lift_subst_pointwise sigma

end LeanFX2
