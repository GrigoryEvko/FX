import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.Precompose

/-! # LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SubstPointwise

Semantic slice of typed pointwise substitution and composition infrastructure. -/

namespace LeanFX2

/-! ## Pointwise lemmas — TermSubsts agreeing on every position

When two TermSubsts over the *same* underlying `Subst` agree pointwise,
`Term.subst` produces equal results.  No HEq needed — both sides have
the same `someType.subst sigma` index.  Casts that appear in `Term.subst`
(e.g. via `Ty.weaken_subst_commute`) are identical between LHS and RHS
because they depend only on `sigma` and the type indices, not on the
TermSubst values themselves; rewriting with the IH passes through them
unchanged. -/

/-- Lift preserves pointwise equality of TermSubsts. -/
theorem TermSubst.lift_pointwise
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    {firstTermSubst secondTermSubst : TermSubst sourceCtx targetCtx sigma}
    (pointwiseEq : ∀ position, firstTermSubst position = secondTermSubst position)
    (newSourceType : Ty level sourceScope) :
    ∀ position,
      firstTermSubst.lift newSourceType position =
        secondTermSubst.lift newSourceType position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show
        (Ty.weaken_subst_commute sigma
            (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)).symm ▸
          Term.weaken (newSourceType.subst sigma)
            (firstTermSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩) =
        (Ty.weaken_subst_commute sigma
            (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)).symm ▸
          Term.weaken (newSourceType.subst sigma)
            (secondTermSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩)
      rw [pointwiseEq ⟨k, Nat.lt_of_succ_lt_succ h⟩]

/-- Term.subst respects pointwise equality of TermSubsts.  If two
TermSubsts over the same Subst agree on every variable position, then
they substitute equally into every term.  29-case structural induction. -/
theorem Term.subst_pointwise
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    {firstTermSubst secondTermSubst : TermSubst sourceCtx targetCtx sigma}
    (pointwiseEq : ∀ position, firstTermSubst position = secondTermSubst position) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
      (someTerm : Term sourceCtx someType raw),
        Term.subst firstTermSubst someTerm = Term.subst secondTermSubst someTerm
  | _, _, .var position => pointwiseEq position
  | _, _, .unit => rfl
  | _, _, .lam body => by
      dsimp only [Term.subst]
      rw [Term.subst_pointwise (TermSubst.lift_pointwise pointwiseEq _) body]
  | _, _, .app fnTerm argTerm => by
      show Term.app _ _ = Term.app _ _
      rw [Term.subst_pointwise pointwiseEq fnTerm,
          Term.subst_pointwise pointwiseEq argTerm]
  | _, _, .lamPi body => by
      show Term.lamPi _ = Term.lamPi _
      rw [Term.subst_pointwise (TermSubst.lift_pointwise pointwiseEq _) body]
  | _, _, .appPi fnTerm argTerm => by
      dsimp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq fnTerm,
          Term.subst_pointwise pointwiseEq argTerm]
  | _, _, .pair firstValue secondValue => by
      dsimp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq firstValue,
          Term.subst_pointwise pointwiseEq secondValue]
  | _, _, .fst pairTerm => by
      show Term.fst _ = Term.fst _
      rw [Term.subst_pointwise pointwiseEq pairTerm]
  | _, _, .snd pairTerm => by
      dsimp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq pairTerm]
  | _, _, .boolTrue => rfl
  | _, _, .boolFalse => rfl
  | _, _, .boolElim scrutinee thenBranch elseBranch => by
      dsimp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq thenBranch,
          Term.subst_pointwise pointwiseEq elseBranch]
  | _, _, .natZero => rfl
  | _, _, .natSucc predecessor => by
      show Term.natSucc _ = Term.natSucc _
      rw [Term.subst_pointwise pointwiseEq predecessor]
  | _, _, .natElim scrutinee zeroBranch succBranch => by
      show Term.natElim _ _ _ = Term.natElim _ _ _
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq zeroBranch,
          Term.subst_pointwise pointwiseEq succBranch]
  | _, _, .natRec scrutinee zeroBranch succBranch => by
      show Term.natRec _ _ _ = Term.natRec _ _ _
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq zeroBranch,
          Term.subst_pointwise pointwiseEq succBranch]
  | _, _, .listNil => rfl
  | _, _, .listCons headTerm tailTerm => by
      show Term.listCons _ _ = Term.listCons _ _
      rw [Term.subst_pointwise pointwiseEq headTerm,
          Term.subst_pointwise pointwiseEq tailTerm]
  | _, _, .listElim scrutinee nilBranch consBranch => by
      show Term.listElim _ _ _ = Term.listElim _ _ _
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq nilBranch,
          Term.subst_pointwise pointwiseEq consBranch]
  | _, _, .optionNone => rfl
  | _, _, .optionSome valueTerm => by
      show Term.optionSome _ = Term.optionSome _
      rw [Term.subst_pointwise pointwiseEq valueTerm]
  | _, _, .optionMatch scrutinee noneBranch someBranch => by
      show Term.optionMatch _ _ _ = Term.optionMatch _ _ _
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq noneBranch,
          Term.subst_pointwise pointwiseEq someBranch]
  | _, _, .eitherInl valueTerm => by
      show Term.eitherInl _ = Term.eitherInl _
      rw [Term.subst_pointwise pointwiseEq valueTerm]
  | _, _, .eitherInr valueTerm => by
      show Term.eitherInr _ = Term.eitherInr _
      rw [Term.subst_pointwise pointwiseEq valueTerm]
  | _, _, .eitherMatch scrutinee leftBranch rightBranch => by
      show Term.eitherMatch _ _ _ = Term.eitherMatch _ _ _
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq leftBranch,
          Term.subst_pointwise pointwiseEq rightBranch]
  | _, _, .refl _ _ => rfl
  | _, _, .idJ baseCase witness => by
      show Term.idJ _ _ = Term.idJ _ _
      rw [Term.subst_pointwise pointwiseEq baseCase,
          Term.subst_pointwise pointwiseEq witness]
  | _, _, .oeqRefl _ _ => rfl
  | _, _, .oeqJ baseCase witness => by
      show Term.oeqJ _ _ = Term.oeqJ _ _
      rw [Term.subst_pointwise pointwiseEq baseCase,
          Term.subst_pointwise pointwiseEq witness]
  | _, _, .oeqFunext _ _ _ _ pointwiseProof => by
      dsimp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq pointwiseProof]
  | _, _, .idStrictRefl _ _ _ => rfl
  | _, _, .idStrictRec _ baseCase witness => by
      show Term.idStrictRec _ _ _ = Term.idStrictRec _ _ _
      rw [Term.subst_pointwise pointwiseEq baseCase,
          Term.subst_pointwise pointwiseEq witness]
  | _, _, .modIntro innerTerm => by
      show Term.modIntro _ = Term.modIntro _
      rw [Term.subst_pointwise pointwiseEq innerTerm]
  | _, _, .modElim innerTerm => by
      show Term.modElim _ = Term.modElim _
      rw [Term.subst_pointwise pointwiseEq innerTerm]
  | _, _, .subsume innerTerm => by
      show Term.subsume _ = Term.subsume _
      rw [Term.subst_pointwise pointwiseEq innerTerm]
  | _, _, .interval0 => rfl
  | _, _, .interval1 => rfl
  | _, _, .intervalOpp innerValue => by
      show Term.intervalOpp _ = Term.intervalOpp _
      rw [Term.subst_pointwise pointwiseEq innerValue]
  | _, _, .intervalMeet leftValue rightValue => by
      show Term.intervalMeet _ _ = Term.intervalMeet _ _
      rw [Term.subst_pointwise pointwiseEq leftValue,
          Term.subst_pointwise pointwiseEq rightValue]
  | _, _, .intervalJoin leftValue rightValue => by
      show Term.intervalJoin _ _ = Term.intervalJoin _ _
      rw [Term.subst_pointwise pointwiseEq leftValue,
          Term.subst_pointwise pointwiseEq rightValue]
  | _, _, .pathLam _ _ _ _ body => by
      dsimp only [Term.subst]
      rw [Term.subst_pointwise
            (TermSubst.lift_pointwise pointwiseEq Ty.interval) body]
  | _, _, .pathApp _ pathTerm intervalTerm => by
      show Term.pathApp _ _ _ = Term.pathApp _ _ _
      rw [Term.subst_pointwise pointwiseEq pathTerm,
          Term.subst_pointwise pointwiseEq intervalTerm]
  | _, _, .glueIntro _ _ _ baseValue partialValue => by
      show Term.glueIntro _ _ _ _ _ = Term.glueIntro _ _ _ _ _
      rw [Term.subst_pointwise pointwiseEq baseValue,
          Term.subst_pointwise pointwiseEq partialValue]
  | _, _, .glueElim _ gluedValue => by
      show Term.glueElim _ _ = Term.glueElim _ _
      rw [Term.subst_pointwise pointwiseEq gluedValue]
  | _, _, .transp _ _ _ _ _ _ _ typePath sourceValue => by
      show Term.transp _ _ _ _ _ _ _ _ _ = Term.transp _ _ _ _ _ _ _ _ _
      rw [Term.subst_pointwise pointwiseEq typePath,
          Term.subst_pointwise pointwiseEq sourceValue]
  | _, _, .hcomp _ sidesValue capValue => by
      show Term.hcomp _ _ _ = Term.hcomp _ _ _
      rw [Term.subst_pointwise pointwiseEq sidesValue,
          Term.subst_pointwise pointwiseEq capValue]
  | _, _, .hcompPath _ _ _ sidesPath capValue => by
      show Term.hcompPath _ _ _ _ _ = Term.hcompPath _ _ _ _ _
      rw [Term.subst_pointwise pointwiseEq sidesPath,
          Term.subst_pointwise pointwiseEq capValue]
  | _, _, .recordIntro firstField => by
      show Term.recordIntro _ = Term.recordIntro _
      rw [Term.subst_pointwise pointwiseEq firstField]
  | _, _, .recordProj recordValue => by
      show Term.recordProj _ = Term.recordProj _
      rw [Term.subst_pointwise pointwiseEq recordValue]
  | _, _, .refineIntro _ baseValue predicateProof => by
      show Term.refineIntro _ _ _ = Term.refineIntro _ _ _
      rw [Term.subst_pointwise pointwiseEq baseValue,
          Term.subst_pointwise pointwiseEq predicateProof]
  | _, _, .refineElim refinedValue => by
      show Term.refineElim _ = Term.refineElim _
      rw [Term.subst_pointwise pointwiseEq refinedValue]
  | _, _, .codataUnfold initialState transition => by
      show Term.codataUnfold _ _ = Term.codataUnfold _ _
      rw [Term.subst_pointwise pointwiseEq initialState,
          Term.subst_pointwise pointwiseEq transition]
  | _, _, .codataDest codataValue => by
      show Term.codataDest _ = Term.codataDest _
      rw [Term.subst_pointwise pointwiseEq codataValue]
  | _, _, .sessionSend _ channel payload => by
      show Term.sessionSend _ _ _ = Term.sessionSend _ _ _
      rw [Term.subst_pointwise pointwiseEq channel,
          Term.subst_pointwise pointwiseEq payload]
  | _, _, .sessionRecv channel => by
      show Term.sessionRecv _ = Term.sessionRecv _
      rw [Term.subst_pointwise pointwiseEq channel]
  | _, _, .effectPerform _ _ _ _ operationTag arguments => by
      show Term.effectPerform _ _ _ _ _ _ = Term.effectPerform _ _ _ _ _ _
      rw [Term.subst_pointwise pointwiseEq operationTag,
          Term.subst_pointwise pointwiseEq arguments]
  -- Universe-code: scope-polymorphic; both sides definitionally
  -- equal regardless of substitution (no var dependencies).
  | _, _, .universeCode _ _ _ _ => rfl
  -- Cumul-up — Phase CUMUL-2.6 Design D: subst arm recurses on
  -- inner typeCode, so pointwise propagates via Term.subst_pointwise
  -- on the typeCode.
  | _, _, .cumulUp _ _ _ _ _ typeCode => by
      show Term.cumulUp _ _ _ _ _ _ = Term.cumulUp _ _ _ _ _ _
      rw [Term.subst_pointwise pointwiseEq typeCode]
  -- HoTT canonical equivalence/funext refl-fragment witnesses: their
  -- subst arms in Term/Subst.lean depend ONLY on the underlying
  -- Subst (not on the TermSubst pointwise data), so both sides
  -- reduce to identical shapes.
  | _, _, .equivReflId _ => rfl
  | _, _, .funextRefl _ _ _ => rfl
  | _, _, .equivReflIdAtId _ _ _ _ => rfl
  | _, _, .funextReflAtId _ _ _ => rfl
  -- HoTT heterogeneous-carrier equivIntroHet (Phase 12.A.B8.5): the
  -- subst arm in Term/Subst.lean recurses on the four subterms via
  -- Term.subst (which respects pointwise hypothesis by structural
  -- IH).  Pointwise equality propagates through forward/backward plus
  -- the proof-function obligations, then the ctor reassembles identically.
  | _, _, .equivIntroHet forward backward leftInv rightInv => by
      dsimp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq forward,
          Term.subst_pointwise pointwiseEq backward,
          Term.subst_pointwise pointwiseEq leftInv,
          Term.subst_pointwise pointwiseEq rightInv]
  | _, _, .equivApp equivTerm argumentTerm => by
      show Term.equivApp _ _ = Term.equivApp _ _
      rw [Term.subst_pointwise pointwiseEq equivTerm,
          Term.subst_pointwise pointwiseEq argumentTerm]
  -- HoTT heterogeneous-carrier path-from-equivalence (Phase 12.A.B8.5b):
  -- the subst arm in Term/Subst.lean recurses on the single subterm
  -- `equivWitness` via Term.subst.  Both TermSubsts share the SAME
  -- underlying `sigma`, so `carrierARaw.subst sigma.forRaw` and
  -- `carrierBRaw.subst sigma.forRaw` are identical on both sides
  -- (depending only on sigma, not on the TermSubst values).  Pointwise
  -- equality propagates through the equivWitness subterm via the
  -- structural IH and the ctor reassembles identically.
  | _, _, .uaIntroHet _ _ _ _ equivWitness => by
      show Term.uaIntroHet _ _ _ _ _ = Term.uaIntroHet _ _ _ _ _
      rw [Term.subst_pointwise pointwiseEq equivWitness]
  -- Phase D3.6-P3: univalence-β extractor.  Same single-subterm
  -- pattern as `uaIntroHet`: the subst arm in Term/Subst.lean
  -- recurses on the single typed subterm `proof` via Term.subst.
  -- Both TermSubsts share the SAME underlying `sigma`, so
  -- `leftTyRaw.subst sigma.forRaw` and `rightTyRaw.subst sigma.forRaw`
  -- are identical on both sides.  Pointwise equality propagates
  -- through the `proof` subterm via the structural IH and the ctor
  -- reassembles identically.
  | _, _, .uaToEquiv _ _ _ _ _ _ proof => by
      show Term.uaToEquiv _ _ _ _ _ _ _ = Term.uaToEquiv _ _ _ _ _ _ _
      rw [Term.subst_pointwise pointwiseEq proof]
  -- Phase D3.6-P4: univalence-β application.  Binary-subterm pattern
  -- mirroring `equivApp`: the subst arm in Term/Subst.lean recurses
  -- on both `equivTerm` and `argumentTerm` via Term.subst; pointwise
  -- equality propagates through both subterms via the structural IH.
  | _, _, .equivApply equivTerm argumentTerm => by
      show Term.equivApply _ _ = Term.equivApply _ _
      rw [Term.subst_pointwise pointwiseEq equivTerm,
          Term.subst_pointwise pointwiseEq argumentTerm]
  -- HoTT heterogeneous-carrier funext-introduction at Id-of-arrow
  -- (Phase 12.A.B8.8): the subst arm in Term/Subst.lean has NO
  -- subterm to recurse on (funextIntroHet is a VALUE, like
  -- funextReflAtId).  Both TermSubsts share the SAME underlying
  -- `sigma`, so `domainType.subst sigma`, `codomainType.subst sigma`,
  -- `applyARaw.subst sigma.forRaw.lift`, and `applyBRaw.subst
  -- sigma.forRaw.lift` are all identical on both sides — they
  -- depend only on `sigma`, not on the TermSubst values.  rfl
  -- discharges the pointwise equality.
  | _, _, .funextIntroHet _ _ _ _ => rfl
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped).  The subst
  -- arms in Term/Subst.lean for ALL ten ctors depend ONLY on the
  -- underlying `sigma` (specifically `sigma.forRaw`), NOT on the
  -- TermSubst pointwise data.  Both TermSubsts share the SAME
  -- `sigma`, so all schematic raw payloads substitute identically on
  -- both sides.  rfl discharges the pointwise equality.
  | _, _, .arrowCode _ _ _ _ => rfl
  | _, _, .piTyCode _ _ _ _ => rfl
  | _, _, .sigmaTyCode _ _ _ _ => rfl
  | _, _, .productCode _ _ _ _ => rfl
  | _, _, .sumCode _ _ _ _ => rfl
  | _, _, .listCode _ _ _ => rfl
  | _, _, .optionCode _ _ _ => rfl
  | _, _, .eitherCode _ _ _ _ => rfl
  | _, _, .idCode _ _ _ _ _ => rfl
  | _, _, .equivCode _ _ _ _ => rfl

end LeanFX2
