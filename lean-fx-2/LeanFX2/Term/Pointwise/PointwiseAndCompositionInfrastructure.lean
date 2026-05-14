import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Subst

/-! # LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure

Pointwise equality for TermSubst plus typed substitution composition
infrastructure (compose, cast HEq scaffolding, beta-singleton consSingleton).
Foundational layer of the Pointwise cascade.

## Root status

Kernel — pointwise/composition skeleton consumed by every weaken-subst-
singleton constructor arm. -/

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
      simp only [Term.subst]
      rw [Term.subst_pointwise (TermSubst.lift_pointwise pointwiseEq _) body]
  | _, _, .app fnTerm argTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq fnTerm,
          Term.subst_pointwise pointwiseEq argTerm]
  | _, _, .lamPi body => by
      simp only [Term.subst]
      rw [Term.subst_pointwise (TermSubst.lift_pointwise pointwiseEq _) body]
  | _, _, .appPi fnTerm argTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq fnTerm,
          Term.subst_pointwise pointwiseEq argTerm]
  | _, _, .pair firstValue secondValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq firstValue,
          Term.subst_pointwise pointwiseEq secondValue]
  | _, _, .fst pairTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq pairTerm]
  | _, _, .snd pairTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq pairTerm]
  | _, _, .boolTrue => rfl
  | _, _, .boolFalse => rfl
  | _, _, .boolElim scrutinee thenBranch elseBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq thenBranch,
          Term.subst_pointwise pointwiseEq elseBranch]
  | _, _, .natZero => rfl
  | _, _, .natSucc predecessor => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq predecessor]
  | _, _, .natElim scrutinee zeroBranch succBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq zeroBranch,
          Term.subst_pointwise pointwiseEq succBranch]
  | _, _, .natRec scrutinee zeroBranch succBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq zeroBranch,
          Term.subst_pointwise pointwiseEq succBranch]
  | _, _, .listNil => rfl
  | _, _, .listCons headTerm tailTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq headTerm,
          Term.subst_pointwise pointwiseEq tailTerm]
  | _, _, .listElim scrutinee nilBranch consBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq nilBranch,
          Term.subst_pointwise pointwiseEq consBranch]
  | _, _, .optionNone => rfl
  | _, _, .optionSome valueTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq valueTerm]
  | _, _, .optionMatch scrutinee noneBranch someBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq noneBranch,
          Term.subst_pointwise pointwiseEq someBranch]
  | _, _, .eitherInl valueTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq valueTerm]
  | _, _, .eitherInr valueTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq valueTerm]
  | _, _, .eitherMatch scrutinee leftBranch rightBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq leftBranch,
          Term.subst_pointwise pointwiseEq rightBranch]
  | _, _, .refl _ _ => rfl
  | _, _, .idJ baseCase witness => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq baseCase,
          Term.subst_pointwise pointwiseEq witness]
  | _, _, .oeqRefl _ _ => rfl
  | _, _, .oeqJ baseCase witness => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq baseCase,
          Term.subst_pointwise pointwiseEq witness]
  | _, _, .oeqFunext _ _ _ _ pointwiseProof => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq pointwiseProof]
  | _, _, .idStrictRefl _ _ _ => rfl
  | _, _, .idStrictRec _ baseCase witness => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq baseCase,
          Term.subst_pointwise pointwiseEq witness]
  | _, _, .modIntro innerTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq innerTerm]
  | _, _, .modElim innerTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq innerTerm]
  | _, _, .subsume innerTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq innerTerm]
  | _, _, .interval0 => rfl
  | _, _, .interval1 => rfl
  | _, _, .intervalOpp innerValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq innerValue]
  | _, _, .intervalMeet leftValue rightValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq leftValue,
          Term.subst_pointwise pointwiseEq rightValue]
  | _, _, .intervalJoin leftValue rightValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq leftValue,
          Term.subst_pointwise pointwiseEq rightValue]
  | _, _, .pathLam _ _ _ _ body => by
      simp only [Term.subst]
      rw [Term.subst_pointwise
            (TermSubst.lift_pointwise pointwiseEq Ty.interval) body]
  | _, _, .pathApp _ pathTerm intervalTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq pathTerm,
          Term.subst_pointwise pointwiseEq intervalTerm]
  | _, _, .glueIntro _ _ _ baseValue partialValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq baseValue,
          Term.subst_pointwise pointwiseEq partialValue]
  | _, _, .glueElim _ gluedValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq gluedValue]
  | _, _, .transp _ _ _ _ _ _ _ typePath sourceValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq typePath,
          Term.subst_pointwise pointwiseEq sourceValue]
  | _, _, .hcomp _ sidesValue capValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq sidesValue,
          Term.subst_pointwise pointwiseEq capValue]
  | _, _, .recordIntro firstField => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq firstField]
  | _, _, .recordProj recordValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq recordValue]
  | _, _, .refineIntro _ baseValue predicateProof => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq baseValue,
          Term.subst_pointwise pointwiseEq predicateProof]
  | _, _, .refineElim refinedValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq refinedValue]
  | _, _, .codataUnfold initialState transition => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq initialState,
          Term.subst_pointwise pointwiseEq transition]
  | _, _, .codataDest codataValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq codataValue]
  | _, _, .sessionSend _ channel payload => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq channel,
          Term.subst_pointwise pointwiseEq payload]
  | _, _, .sessionRecv channel => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq channel]
  | _, _, .effectPerform _ _ _ _ operationTag arguments => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq operationTag,
          Term.subst_pointwise pointwiseEq arguments]
  -- Universe-code: scope-polymorphic; both sides definitionally
  -- equal regardless of substitution (no var dependencies).
  | _, _, .universeCode _ _ _ _ => rfl
  -- Cumul-up — Phase CUMUL-2.6 Design D: subst arm recurses on
  -- inner typeCode, so pointwise propagates via Term.subst_pointwise
  -- on the typeCode.
  | _, _, .cumulUp _ _ _ _ _ typeCode => by
      simp only [Term.subst]
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
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq forward,
          Term.subst_pointwise pointwiseEq backward,
          Term.subst_pointwise pointwiseEq leftInv,
          Term.subst_pointwise pointwiseEq rightInv]
  | _, _, .equivApp equivTerm argumentTerm => by
      simp only [Term.subst]
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
      simp only [Term.subst]
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
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq proof]
  -- Phase D3.6-P4: univalence-β application.  Binary-subterm pattern
  -- mirroring `equivApp`: the subst arm in Term/Subst.lean recurses
  -- on both `equivTerm` and `argumentTerm` via Term.subst; pointwise
  -- equality propagates through both subterms via the structural IH.
  | _, _, .equivApply equivTerm argumentTerm => by
      simp only [Term.subst]
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

/-! ## TermSubst composition

`TermSubst.compose` builds the typed companion of `Subst.compose`.
For each source position `position`, it produces a Term in the final
target whose type/raw match the composed substitution by post-substituting
the first TermSubst's value through the second TermSubst.  The Ty
alignment uses `Ty.subst_compose`; the raw alignment is definitional
(both `Subst.compose.forRaw` and `RawTermSubst.compose` are defined
pointwise as `(σ1.forRaw p).subst σ2.forRaw`). -/

/-- Compose two TermSubsts: post-substitute the first's image through
the second.  The Ty cast aligns `(varType src pos).subst σ1).subst σ2`
with `(varType src pos).subst (Subst.compose σ1 σ2)` via the typed
two-position cast helper `Term.castType`. -/
def TermSubst.compose
    {mode : Mode} {level : Nat} {sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {firstSubst : Subst level sourceScope middleScope}
    {secondSubst : Subst level middleScope targetScope}
    (firstTermSubst : TermSubst sourceCtx middleCtx firstSubst)
    (secondTermSubst : TermSubst middleCtx targetCtx secondSubst) :
    TermSubst sourceCtx targetCtx (Subst.compose firstSubst secondSubst) :=
  fun position =>
    cast
      (by rw [Ty.subst_compose firstSubst secondSubst (varType sourceCtx position)])
      (Term.subst secondTermSubst (firstTermSubst position))

/-- The cast in `TermSubst.compose` doesn't change the Term value
underneath — only the type index.  HEq witnesses this directly via
`cast_heq`. -/
theorem TermSubst.compose_position_HEq
    {mode : Mode} {level : Nat} {sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {firstSubst : Subst level sourceScope middleScope}
    {secondSubst : Subst level middleScope targetScope}
    (firstTermSubst : TermSubst sourceCtx middleCtx firstSubst)
    (secondTermSubst : TermSubst middleCtx targetCtx secondSubst)
    (position : Fin sourceScope) :
    HEq (TermSubst.compose firstTermSubst secondTermSubst position)
        (Term.subst secondTermSubst (firstTermSubst position)) :=
  cast_heq _ _

/-! ## Beta-specific singleton composition

These lemmas package the substitution shape used by lambda beta
contracta.  They live at the Term layer because they mention only
`Ty`, `RawTerm`, and `TermSubst`, while downstream reducibility lemmas
consume them to relate body IHs under an extended substitution to the
concrete `Term.subst0` contractum. -/

/-- A type-index cast on a typed term is heterogeneously equal to the
original term. -/
theorem Term.type_eq_cast_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {raw : RawTerm scope}
    (typeEq : sourceType = targetType)
    (sourceTerm : Term context sourceType raw) :
    HEq (typeEq ▸ sourceTerm) sourceTerm := by
  cases typeEq
  exact HEq.rfl

/-- A symmetric type-index cast on a typed term is heterogeneously
equal to the original term. -/
theorem Term.type_eq_symm_cast_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {raw : RawTerm scope}
    (typeEq : sourceType = targetType)
    {targetTerm : Term context targetType raw} :
    HEq (typeEq.symm ▸ targetTerm) targetTerm := by
  cases typeEq
  exact HEq.rfl

/-- The freshly-bound variable is stable under equality of the single
head type added to the context. -/
theorem Term.var_zero_cons_type_eq_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    (typeEq : firstType = secondType) :
    HEq
      (Term.var (context := context.cons firstType)
        ⟨0, Nat.zero_lt_succ scope⟩)
      (Term.var (context := context.cons secondType)
        ⟨0, Nat.zero_lt_succ scope⟩) := by
  cases typeEq
  exact HEq.rfl

/-- Renaming ignores a pure symmetric type-index cast up to the
corresponding renamed type-index cast. -/
theorem Term.rename_type_eq_symm_cast_heq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {sourceType targetType : Ty level sourceScope}
    {raw : RawTerm sourceScope}
    (typeEq : sourceType = targetType)
    {targetTerm : Term sourceCtx targetType raw} :
    HEq (Term.rename termRenaming (typeEq.symm ▸ targetTerm))
      ((congrArg (fun someType => Ty.rename someType rho) typeEq).symm ▸
        Term.rename termRenaming targetTerm) := by
  cases typeEq
  exact HEq.rfl

/-- The cast in `TermSubst.renameOutput` changes only the type index.

This packages the exact `Ty.subst_rename_commute` transport used by
`TermSubst.renameOutput`, so downstream binder-stability proofs can
reason about the renamed substitution entry without unfolding the
definition at every position. -/
theorem TermSubst.renameOutput_position_HEq
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope middleScope}
    {rho : RawRenaming middleScope targetScope}
    (termSubst : TermSubst sourceCtx middleCtx sigma)
    (termRenaming : TermRenaming middleCtx targetCtx rho)
    (position : Fin sourceScope) :
    HEq (TermSubst.renameOutput termSubst termRenaming position)
      (Term.rename termRenaming (termSubst position)) := by
  change HEq
    (Ty.subst_rename_commute sigma rho (varType sourceCtx position) ▸
      Term.rename termRenaming (termSubst position))
    (Term.rename termRenaming (termSubst position))
  exact Term.type_eq_cast_heq
    (Ty.subst_rename_commute sigma rho (varType sourceCtx position))
    (Term.rename termRenaming (termSubst position))

/-- A raw-index cast on a typed term is heterogeneously equal to the
original term. -/
theorem Term.raw_eq_cast_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (rawEq : sourceRaw = targetRaw)
    (sourceTerm : Term context someType sourceRaw) :
    HEq (rawEq ▸ sourceTerm) sourceTerm := by
  cases rawEq
  exact HEq.rfl

/-- Combined type/raw casts on a typed term are heterogeneously equal
to the original term. -/
theorem Term.type_raw_eq_cast_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEq : sourceType = targetType)
    (rawEq : sourceRaw = targetRaw)
    (sourceTerm : Term context sourceType sourceRaw) :
    HEq (rawEq ▸ typeEq ▸ sourceTerm) sourceTerm := by
  cases typeEq
  cases rawEq
  exact HEq.rfl

/-- Substitution ignores a pure type-index cast up to heterogeneous
equality. -/
theorem Term.subst_type_eq_cast_heq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {sourceType targetType : Ty level sourceScope}
    {raw : RawTerm sourceScope}
    (typeEq : sourceType = targetType)
    (sourceTerm : Term sourceCtx sourceType raw) :
    HEq (Term.subst termSubst (typeEq ▸ sourceTerm))
      (Term.subst termSubst sourceTerm) := by
  cases typeEq
  exact HEq.rfl

/-! ## Lift/compose alignment

These lemmas compare the two substitution shapes exposed by binder
composition:

* lifting the already-composed substitution; and
* composing the two individually lifted substitutions.

The fresh-variable case is the first cast-bearing obstruction in the
`Term.subst_compose` binder proof: both sides reduce to variable zero,
but their target contexts differ by `Ty.subst_compose`. -/

/-- Fresh-variable entry of lifted substitution composition.

This compares `(first.compose second).lift` with
`first.lift.compose second.lift` at position zero.  The proof strips the
type-index casts on both sides, then relates the two variable-zero terms
through the context-head equality supplied by `Ty.subst_compose`. -/
theorem TermSubst.lift_compose_zero_HEq
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {firstSubst : Subst level sourceScope middleScope}
    {secondSubst : Subst level middleScope targetScope}
    (firstTermSubst : TermSubst sourceCtx middleCtx firstSubst)
    (secondTermSubst : TermSubst middleCtx targetCtx secondSubst)
    (newSourceType : Ty level sourceScope) :
    HEq
      ((TermSubst.compose firstTermSubst secondTermSubst).lift
        newSourceType ⟨0, Nat.zero_lt_succ sourceScope⟩)
      (TermSubst.compose (firstTermSubst.lift newSourceType)
        (secondTermSubst.lift (newSourceType.subst firstSubst))
        ⟨0, Nat.zero_lt_succ sourceScope⟩) := by
  simp only [TermSubst.lift, TermSubst.compose]
  apply HEq.trans
  · exact Term.type_eq_symm_cast_heq
      (Ty.weaken_subst_commute (Subst.compose firstSubst secondSubst)
        newSourceType)
  · apply HEq.symm
    apply HEq.trans
    · exact cast_heq _ _
    · apply HEq.trans
      · exact Term.subst_type_eq_cast_heq _ _ _
      · simp only [Term.subst, TermSubst.lift]
        apply HEq.trans
        · exact Term.type_eq_symm_cast_heq
            (Ty.weaken_subst_commute secondSubst
              (newSourceType.subst firstSubst))
        · exact Term.var_zero_cons_type_eq_heq
            (Ty.subst_compose firstSubst secondSubst newSourceType)

/-- Substitution law for the beta-specific environment extension:
weakening a source type, lifting an existing substitution, then
substituting the fresh argument is propositionally the original
substitution on that type. -/
theorem Ty.weaken_subst_lift_singleton
    {level scope targetScope : Nat}
    (sourceType domainType : Ty level scope)
    (sigma : Subst level scope targetScope)
    (argumentRaw : RawTerm targetScope) :
    sourceType.weaken.subst
        (Subst.compose sigma.lift
          (Subst.singleton (domainType.subst sigma) argumentRaw)) =
      sourceType.subst sigma := by
  rw [← Ty.subst_compose sigma.lift
        (Subst.singleton (domainType.subst sigma) argumentRaw)
        sourceType.weaken]
  rw [Ty.weaken_subst_commute sigma sourceType]
  exact Ty.weaken_subst_singleton (sourceType.subst sigma)
    (domainType.subst sigma) argumentRaw

/-- Raw beta-contractum alignment for the beta-specific substitution
extension. -/
theorem RawTerm.subst_lift_singleton_eq_subst0
    {level scope targetScope : Nat}
    (bodyRaw : RawTerm (scope + 1))
    (domainType : Ty level scope)
    (sigma : Subst level scope targetScope)
    (argumentRaw : RawTerm targetScope) :
    bodyRaw.subst
        (Subst.compose sigma.lift
          (Subst.singleton (domainType.subst sigma) argumentRaw)).forRaw =
      (bodyRaw.subst sigma.forRaw.lift).subst0 argumentRaw := by
  unfold RawTerm.subst0
  rw [RawTerm.subst_compose sigma.forRaw.lift
    (RawTermSubst.singleton argumentRaw) bodyRaw]

/-- Weakening under one existing binder, then substituting by the lifted
singleton, returns the original raw term. -/
theorem RawTerm.weaken_lift_subst_singleton_lift {scope : Nat}
    (term : RawTerm (scope + 1)) (rawArg : RawTerm scope) :
    (term.rename RawRenaming.weaken.lift).subst
        (RawTermSubst.singleton rawArg).lift =
      term := by
  rw [RawTerm.rename_subst_commute RawRenaming.weaken.lift
      (RawTermSubst.singleton rawArg).lift term,
    RawTerm.subst_pointwise ?_ term,
    RawTerm.subst_identity term]
  intro position
  rcases position with ⟨positionIndex, positionLt⟩
  cases positionIndex with
  | zero => rfl
  | succ _ => rfl

/-- Weakening under one existing binder, then substituting by the lifted
singleton, returns the original type. -/
theorem Ty.weaken_lift_subst_singleton_lift {level scope : Nat}
    (someType : Ty level (scope + 1))
    (substituent : Ty level scope)
    (rawArg : RawTerm scope) :
    (someType.rename RawRenaming.weaken.lift).subst
        (Subst.singleton substituent rawArg).lift =
      someType := by
  rw [Ty.rename_subst_commute RawRenaming.weaken.lift
      (Subst.singleton substituent rawArg).lift someType]
  rw [Ty.subst_pointwise ?_ ?_ someType, Ty.subst_identity someType]
  · intro position
    rcases position with ⟨positionIndex, positionLt⟩
    cases positionIndex with
    | zero => rfl
    | succ _ => rfl
  · intro position
    rcases position with ⟨positionIndex, positionLt⟩
    cases positionIndex with
    | zero => rfl
    | succ _ => rfl

/-- Beta-specific extension of a typed substitution by an argument.

Unlike `TermSubst.lift`, this substitution lands back in the original
target context: position zero maps to the supplied argument, while
successor positions map to the original substitution witnesses. -/
def TermSubst.consSingleton
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw) :
    TermSubst (sourceCtx.cons domainType) targetCtx
      (Subst.compose sigma.lift
        (Subst.singleton (domainType.subst sigma) argumentRaw))
  | ⟨0, _⟩ =>
      (Ty.weaken_subst_lift_singleton domainType domainType sigma
        argumentRaw).symm ▸
        argumentTerm
  | ⟨positionIndex + 1, positionIsWithinScope⟩ =>
      let previousPosition : Fin scope :=
        ⟨positionIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
      have typeEq :
          ((varType (sourceCtx.cons domainType)
              ⟨positionIndex + 1, positionIsWithinScope⟩).subst
            (Subst.compose sigma.lift
              (Subst.singleton (domainType.subst sigma) argumentRaw))) =
            (varType sourceCtx previousPosition).subst sigma := by
        exact Ty.weaken_subst_lift_singleton
          (varType sourceCtx previousPosition) domainType sigma argumentRaw
      have rawEq :
          (Subst.compose sigma.lift
              (Subst.singleton (domainType.subst sigma) argumentRaw)).forRaw
              ⟨positionIndex + 1, positionIsWithinScope⟩ =
            sigma.forRaw previousPosition := by
        exact RawTerm.weaken_subst_singleton
          (sigma.forRaw previousPosition) argumentRaw
      rawEq.symm ▸ typeEq.symm ▸ termSubst previousPosition

/-- The fresh entry of `TermSubst.consSingleton` is the supplied
argument, modulo the definitional type-index cast used by the
substitution family. -/
theorem TermSubst.consSingleton_zero_HEq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw) :
    HEq
      (TermSubst.consSingleton termSubst argumentTerm
        ⟨0, Nat.zero_lt_succ scope⟩)
      argumentTerm :=
  Term.type_eq_cast_heq
    (Ty.weaken_subst_lift_singleton domainType domainType sigma
      argumentRaw).symm
    argumentTerm

/-- A successor entry of `TermSubst.consSingleton` is the corresponding
old substitution entry, modulo the raw/type casts that collapse
weakening followed by singleton substitution. -/
theorem TermSubst.consSingleton_succ_HEq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw)
    (previousIndex : Nat)
    (positionIsWithinScope : previousIndex + 1 < scope + 1) :
    HEq
      (TermSubst.consSingleton termSubst argumentTerm
        ⟨previousIndex + 1, positionIsWithinScope⟩)
      (termSubst
        ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩) := by
  simp only [TermSubst.consSingleton]
  exact Term.type_raw_eq_cast_heq
    (Ty.weaken_subst_lift_singleton
      (varType sourceCtx
        ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)
      domainType sigma argumentRaw).symm
    (RawTerm.weaken_subst_singleton
      (sigma.forRaw
        ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)
      argumentRaw).symm
    (termSubst
      ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)

/-- The fresh variable of `termSubst.lift` collapses to the singleton
argument after substituting by `TermSubst.singleton`, up to HEq. -/
theorem TermSubst.lift_zero_subst_singleton_heq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (termSubst.lift domainType ⟨0, Nat.zero_lt_succ scope⟩))
      argumentTerm := by
  simp only [TermSubst.lift, varType]
  apply HEq.trans
    (Term.subst_type_eq_cast_heq (TermSubst.singleton argumentTerm)
      (Ty.weaken_subst_commute sigma domainType).symm
      (Term.var (context := targetCtx.cons (domainType.subst sigma))
        ⟨0, Nat.zero_lt_succ targetScope⟩))
  change HEq
    (TermSubst.singleton argumentTerm ⟨0, Nat.zero_lt_succ targetScope⟩)
    argumentTerm
  simp only [TermSubst.singleton, varType]
  exact Term.type_eq_cast_heq
    (Ty.weaken_subst_singleton (domainType.subst sigma)
      (domainType.subst sigma) argumentRaw).symm
    argumentTerm

/-- The fresh entry of the composed lift-then-singleton substitution
agrees with the beta-specific `consSingleton` substitution.

This is the zero-position half of the entrywise comparison needed by
the typed beta-contractum bridge.  The successor half requires the
general weaken-then-singleton collapse for arbitrary substituted terms
and is intentionally left to that structural theorem. -/
theorem TermSubst.compose_lift_singleton_consSingleton_zero_HEq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw) :
    HEq
      (TermSubst.compose (termSubst.lift domainType)
        (TermSubst.singleton argumentTerm)
        ⟨0, Nat.zero_lt_succ scope⟩)
      (TermSubst.consSingleton termSubst argumentTerm
        ⟨0, Nat.zero_lt_succ scope⟩) := by
  exact HEq.trans
    (TermSubst.compose_position_HEq
      (termSubst.lift domainType)
      (TermSubst.singleton argumentTerm)
      ⟨0, Nat.zero_lt_succ scope⟩)
    (HEq.trans
      (TermSubst.lift_zero_subst_singleton_heq termSubst argumentTerm)
      (TermSubst.consSingleton_zero_HEq termSubst argumentTerm).symm)

/-- Successor comparison for composed lift-then-singleton substitutions,
assuming the old substitution entry itself collapses after weakening and
singleton substitution.

This theorem does not hide the hard structural obligation: `entryHEq`
is precisely the arbitrary-term weaken-then-singleton collapse needed
for the old substitution entry.  Once that structural theorem exists,
this lemma turns it into the successor half of the `compose` versus
`consSingleton` comparison. -/
theorem TermSubst.compose_lift_singleton_consSingleton_succ_of_entry_HEq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw)
    (previousIndex : Nat)
    (positionIsWithinScope : previousIndex + 1 < scope + 1)
    (entryHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken (domainType.subst sigma)
            (termSubst
              ⟨previousIndex,
                Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)))
        (termSubst
          ⟨previousIndex,
            Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)) :
    HEq
      (TermSubst.compose (termSubst.lift domainType)
        (TermSubst.singleton argumentTerm)
        ⟨previousIndex + 1, positionIsWithinScope⟩)
      (TermSubst.consSingleton termSubst argumentTerm
        ⟨previousIndex + 1, positionIsWithinScope⟩) := by
  let previousPosition : Fin scope :=
    ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
  exact HEq.trans
    (TermSubst.compose_position_HEq
      (termSubst.lift domainType)
      (TermSubst.singleton argumentTerm)
      ⟨previousIndex + 1, positionIsWithinScope⟩)
    (HEq.trans
      (Term.subst_type_eq_cast_heq
        (TermSubst.singleton argumentTerm)
        (Ty.weaken_subst_commute sigma
          (varType sourceCtx previousPosition)).symm
        (Term.weaken (domainType.subst sigma)
          (termSubst previousPosition)))
      (HEq.trans entryHEq
        (TermSubst.consSingleton_succ_HEq termSubst argumentTerm
          previousIndex positionIsWithinScope).symm))

/-- Pointwise equality between the composed lift-then-singleton
substitution and the beta-specific `consSingleton` substitution.

The theorem packages the already-audited zero and successor HEq entries
into the exact same-index equality needed by `Term.subst_pointwise`.
It still exposes the real remaining obligation: every old substitution
entry must collapse after weakening and singleton substitution. -/
theorem TermSubst.compose_lift_singleton_consSingleton_pointwise_of_entry
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw)
    (entryHEq :
      ∀ previousPosition : Fin scope,
        HEq
          (Term.subst (TermSubst.singleton argumentTerm)
            (Term.weaken (domainType.subst sigma)
              (termSubst previousPosition)))
          (termSubst previousPosition)) :
    ∀ position,
      TermSubst.compose (termSubst.lift domainType)
        (TermSubst.singleton argumentTerm) position =
      TermSubst.consSingleton termSubst argumentTerm position := by
  intro position
  rcases position with ⟨positionIndex, positionIsWithinScope⟩
  cases positionIndex with
  | zero =>
      exact eq_of_heq
        (TermSubst.compose_lift_singleton_consSingleton_zero_HEq
          termSubst argumentTerm)
  | succ previousIndex =>
      exact eq_of_heq
        (TermSubst.compose_lift_singleton_consSingleton_succ_of_entry_HEq
          termSubst argumentTerm previousIndex positionIsWithinScope
          (entryHEq
            ⟨previousIndex,
              Nat.lt_of_succ_lt_succ positionIsWithinScope⟩))

/-- Substituting a term with the composed lift-then-singleton
substitution is the same as substituting it with the beta-specific
`consSingleton` substitution, assuming the old substitution entries
collapse after weaken-then-singleton.

This is the body-level form needed by the lambda contractum route:
after the entry theorem is available, `Term.subst_pointwise` can
transport every body in one step instead of re-opening constructor
cases. -/
theorem Term.subst_compose_lift_singleton_eq_consSingleton_of_entry
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw)
    (entryHEq :
      ∀ previousPosition : Fin scope,
        HEq
          (Term.subst (TermSubst.singleton argumentTerm)
            (Term.weaken (domainType.subst sigma)
              (termSubst previousPosition)))
          (termSubst previousPosition))
    {bodyType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (bodyTerm : Term (sourceCtx.cons domainType) bodyType bodyRaw) :
    Term.subst
        (TermSubst.compose (termSubst.lift domainType)
          (TermSubst.singleton argumentTerm))
        bodyTerm =
      Term.subst (TermSubst.consSingleton termSubst argumentTerm)
        bodyTerm := by
  exact Term.subst_pointwise
    (TermSubst.compose_lift_singleton_consSingleton_pointwise_of_entry
      termSubst argumentTerm entryHEq)
    bodyTerm


end LeanFX2
