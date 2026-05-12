import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Subst

/-! # Term/Pointwise — substitution pointwise & commute lemmas

Lemmas about how `Term.subst` and `Term.rename` interact with
substitutions that are pointwise-equivalent or compose with each other.

## Approach

The Foundation layer (`Foundation/Subst.lean` + `Foundation/RawSubst.lean`)
proves Eq-shaped commute laws on `Ty` and `RawTerm` because their indices
are scope/level naturals — no dependency on contexts or term values.

At the Term layer, `Term someCtx someType raw` carries the *value* of
`someType` and `raw` as type-level indices, so Term-level commutes
generally come in two shapes:

* **Eq-shaped pointwise lemmas** — when both sides have the same
  `someType` and `raw` (e.g. `Term.subst_pointwise`: two TermSubsts
  over the same Subst).  These reduce to structural induction.
* **HEq-shaped commute lemmas** — when the subst/rename composition
  changes the index (e.g. `Term.subst_compose`: subst-then-subst vs
  subst-by-composed).  Both sides have types that are *propositionally*
  Eq via the Foundation lemmas, but not definitionally Eq, so HEq is
  the right tool.

Downstream consumers (Compat) lift HEq results to Eq via `▸` casts at
the use site, or absorb the index difference into the two-Ty signature
of Step / Step.par / StepStar / Conv.

## Dependencies

* `Term/Subst.lean`
* (transitively) `Foundation/Subst.lean`, `Foundation/RawSubst.lean`
-/

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

/-! ## Weakening followed by singleton substitution

These lemmas build the constructor-by-constructor collapse needed by
the lambda beta-contractum route: weaken a typed term through a fresh
binder, then substitute that fresh binder by a singleton argument.  The
full structural theorem is intentionally assembled in small audited
slices because cast-bearing binders and dependent eliminators require
their own alignment work. -/

/-- Variable case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_var_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (position : Fin scope)
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.var (context := context) position)))
      (Term.var (context := context) position) := by
  simp only [Term.weaken, Term.rename, Term.subst, TermSubst.singleton]
  exact Term.type_raw_eq_cast_heq
    (Ty.weaken_subst_singleton (varType context position) newType
      argumentRaw).symm
    (RawTerm.weaken_subst_singleton (RawTerm.var position) argumentRaw).symm
    (Term.var position)

/-- Unit value case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_unit_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.unit (context := context))))
      (Term.unit (context := context)) := by
  rfl

/-- Boolean true case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_boolTrue_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.boolTrue (context := context))))
      (Term.boolTrue (context := context)) := by
  rfl

/-- Boolean false case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_boolFalse_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.boolFalse (context := context))))
      (Term.boolFalse (context := context)) := by
  rfl

/-- Natural zero case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_natZero_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.natZero (context := context))))
      (Term.natZero (context := context)) := by
  rfl

/-- Empty list case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_listNil_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (elementType : Ty level scope)
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType
          (Term.listNil (context := context) (elementType := elementType))))
      (Term.listNil (context := context) (elementType := elementType)) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.listNil_HEq_congr
    (Ty.weaken_subst_singleton elementType newType argumentRaw)

/-- Empty option case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_optionNone_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (elementType : Ty level scope)
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType
          (Term.optionNone (context := context) (elementType := elementType))))
      (Term.optionNone (context := context) (elementType := elementType)) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.optionNone_HEq_congr
    (Ty.weaken_subst_singleton elementType newType argumentRaw)

/-- Interval zero case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_interval0_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.interval0 (context := context))))
      (Term.interval0 (context := context)) := by
  rfl

/-- Interval one case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_interval1_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.interval1 (context := context))))
      (Term.interval1 (context := context)) := by
  rfl

/-- Natural successor preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_natSucc_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (predecessorTerm : Term context Ty.nat predecessorRaw)
    (predecessorHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType predecessorTerm))
        predecessorTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.natSucc predecessorTerm)))
      (Term.natSucc predecessorTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.natSucc_HEq_congr
    (RawTerm.weaken_subst_singleton predecessorRaw argumentRaw)
    predecessorHEq

/-- List cons preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_listCons_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (headHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType headTerm))
        headTerm)
    (tailHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType tailTerm))
        tailTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.listCons headTerm tailTerm)))
      (Term.listCons headTerm tailTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.listCons_HEq_congr
    (Ty.weaken_subst_singleton elementType newType argumentRaw)
    (RawTerm.weaken_subst_singleton headRaw argumentRaw)
    (RawTerm.weaken_subst_singleton tailRaw argumentRaw)
    headHEq tailHEq

/-- Option some preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_optionSome_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (valueTerm : Term context elementType valueRaw)
    (valueHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType valueTerm))
        valueTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.optionSome valueTerm)))
      (Term.optionSome valueTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.optionSome_HEq_congr
    (Ty.weaken_subst_singleton elementType newType argumentRaw)
    (RawTerm.weaken_subst_singleton valueRaw argumentRaw)
    valueHEq

/-- Either-left injection preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_eitherInl_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (valueTerm : Term context leftType valueRaw)
    (valueHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType valueTerm))
        valueTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType
          (Term.eitherInl (rightType := rightType) valueTerm)))
      (Term.eitherInl (rightType := rightType) valueTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.eitherInl_HEq_congr
    (Ty.weaken_subst_singleton leftType newType argumentRaw)
    (Ty.weaken_subst_singleton rightType newType argumentRaw)
    (RawTerm.weaken_subst_singleton valueRaw argumentRaw)
    valueHEq

/-- Either-right injection preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_eitherInr_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (valueTerm : Term context rightType valueRaw)
    (valueHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType valueTerm))
        valueTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType
          (Term.eitherInr (leftType := leftType) valueTerm)))
      (Term.eitherInr (leftType := leftType) valueTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.eitherInr_HEq_congr
    (Ty.weaken_subst_singleton leftType newType argumentRaw)
    (Ty.weaken_subst_singleton rightType newType argumentRaw)
    (RawTerm.weaken_subst_singleton valueRaw argumentRaw)
    valueHEq

/-- Interval negation preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_intervalOpp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (innerTerm : Term context Ty.interval innerRaw)
    (innerHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType innerTerm))
        innerTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.intervalOpp innerTerm)))
      (Term.intervalOpp innerTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.intervalOpp_HEq_congr
    (RawTerm.weaken_subst_singleton innerRaw argumentRaw)
    innerHEq

/-- Interval meet preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_intervalMeet_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (leftTerm : Term context Ty.interval leftRaw)
    (rightTerm : Term context Ty.interval rightRaw)
    (leftHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType leftTerm))
        leftTerm)
    (rightHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType rightTerm))
        rightTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.intervalMeet leftTerm rightTerm)))
      (Term.intervalMeet leftTerm rightTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.intervalMeet_HEq_congr
    (RawTerm.weaken_subst_singleton leftRaw argumentRaw)
    (RawTerm.weaken_subst_singleton rightRaw argumentRaw)
    leftHEq rightHEq

/-- Interval join preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_intervalJoin_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (leftTerm : Term context Ty.interval leftRaw)
    (rightTerm : Term context Ty.interval rightRaw)
    (leftHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType leftTerm))
        leftTerm)
    (rightHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType rightTerm))
        rightTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.intervalJoin leftTerm rightTerm)))
      (Term.intervalJoin leftTerm rightTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.intervalJoin_HEq_congr
    (RawTerm.weaken_subst_singleton leftRaw argumentRaw)
    (RawTerm.weaken_subst_singleton rightRaw argumentRaw)
    leftHEq rightHEq

/-- Modal introduction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_modIntro_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType innerTerm))
        innerTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.modIntro innerTerm)))
      (Term.modIntro innerTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.modIntro_HEq_congr
    (Ty.weaken_subst_singleton innerType newType argumentRaw)
    (RawTerm.weaken_subst_singleton innerRaw argumentRaw)
    innerHEq

/-- Modal elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_modElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType innerTerm))
        innerTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.modElim innerTerm)))
      (Term.modElim innerTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.modElim_HEq_congr
    (Ty.weaken_subst_singleton innerType newType argumentRaw)
    (RawTerm.weaken_subst_singleton innerRaw argumentRaw)
    innerHEq

/-- Cumulativity subsumption preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_subsume_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType innerTerm))
        innerTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.subsume innerTerm)))
      (Term.subsume innerTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.subsume_HEq_congr
    (Ty.weaken_subst_singleton innerType newType argumentRaw)
    (RawTerm.weaken_subst_singleton innerRaw argumentRaw)
    innerHEq

/-- Non-dependent application preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_app_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentValueRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentValue : Term context domainType argumentValueRaw)
    (functionHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType functionTerm))
        functionTerm)
    (argumentHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType argumentValue))
        argumentValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.app functionTerm argumentValue)))
      (Term.app functionTerm argumentValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.app_HEq_congr
    (Ty.weaken_subst_singleton domainType newType singletonRaw)
    (Ty.weaken_subst_singleton codomainType newType singletonRaw)
    (RawTerm.weaken_subst_singleton functionRaw singletonRaw)
    (RawTerm.weaken_subst_singleton argumentValueRaw singletonRaw)
    functionHEq argumentHEq

/-- Natural elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_natElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (zeroHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType zeroBranch))
        zeroBranch)
    (succHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType succBranch))
        succBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.natElim scrutinee zeroBranch succBranch)))
      (Term.natElim scrutinee zeroBranch succBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.natElim_HEq_congr
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton zeroRaw singletonRaw)
    (RawTerm.weaken_subst_singleton succRaw singletonRaw)
    scrutineeHEq zeroHEq succHEq

/-- Natural recursion preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_natRec_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (zeroHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType zeroBranch))
        zeroBranch)
    (succHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType succBranch))
        succBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.natRec scrutinee zeroBranch succBranch)))
      (Term.natRec scrutinee zeroBranch succBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.natRec_HEq_congr
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton zeroRaw singletonRaw)
    (RawTerm.weaken_subst_singleton succRaw singletonRaw)
    scrutineeHEq zeroHEq succHEq

/-- List elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_listElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (nilHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType nilBranch))
        nilBranch)
    (consHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType consBranch))
        consBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.listElim scrutinee nilBranch consBranch)))
      (Term.listElim scrutinee nilBranch consBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.listElim_HEq_congr
    (Ty.weaken_subst_singleton elementType newType singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton nilRaw singletonRaw)
    (RawTerm.weaken_subst_singleton consRaw singletonRaw)
    scrutineeHEq nilHEq consHEq

/-- Option matching preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_optionMatch_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (noneHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType noneBranch))
        noneBranch)
    (someHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType someBranch))
        someBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.optionMatch scrutinee noneBranch someBranch)))
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.optionMatch_HEq_congr
    (Ty.weaken_subst_singleton elementType newType singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton noneRaw singletonRaw)
    (RawTerm.weaken_subst_singleton someRaw singletonRaw)
    scrutineeHEq noneHEq someHEq

/-- Either matching preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_eitherMatch_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (leftHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType leftBranch))
        leftBranch)
    (rightHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType rightBranch))
        rightBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.eitherMatch scrutinee leftBranch rightBranch)))
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.eitherMatch_HEq_congr
    (Ty.weaken_subst_singleton leftType newType singletonRaw)
    (Ty.weaken_subst_singleton rightType newType singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton leftRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightRaw singletonRaw)
    scrutineeHEq leftHEq rightHEq

/-- Identity reflexivity preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_refl_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.refl (context := context) carrier rawWitness)))
      (Term.refl (context := context) carrier rawWitness) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.refl_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton rawWitness singletonRaw)

/-- Identity elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_idJ_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.id carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseCase))
        baseCase)
    (witnessHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType witness))
        witness) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.idJ baseCase witness)))
      (Term.idJ baseCase witness) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.idJ_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton rightEndpoint singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton baseRaw singletonRaw)
    (RawTerm.weaken_subst_singleton witnessRaw singletonRaw)
    baseCaseHEq witnessHEq

/-- Observational reflexivity preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_oeqRefl_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.oeqRefl (context := context) carrier rawWitness)))
      (Term.oeqRefl (context := context) carrier rawWitness) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.oeqRefl_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton rawWitness singletonRaw)

/-- Observational equality elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_oeqJ_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseCase))
        baseCase)
    (witnessHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType witness))
        witness) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.oeqJ baseCase witness)))
      (Term.oeqJ baseCase witness) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.oeqJ_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton rightEndpoint singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton baseRaw singletonRaw)
    (RawTerm.weaken_subst_singleton witnessRaw singletonRaw)
    baseCaseHEq witnessHEq

/-- Strict identity reflexivity preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_idStrictRefl_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.idStrictRefl (context := context) modeIsStrict carrier
            rawWitness)))
      (Term.idStrictRefl (context := context) modeIsStrict carrier
        rawWitness) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.idStrictRefl_HEq_congr modeIsStrict
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton rawWitness singletonRaw)

/-- Strict identity recursion preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_idStrictRec_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw)
    (baseCaseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseCase))
        baseCase)
    (witnessHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType witness))
        witness) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.idStrictRec modeIsStrict baseCase witness)))
      (Term.idStrictRec modeIsStrict baseCase witness) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.idStrictRec_HEq_congr modeIsStrict
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton rightEndpoint singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton baseRaw singletonRaw)
    (RawTerm.weaken_subst_singleton witnessRaw singletonRaw)
    baseCaseHEq witnessHEq

/-- Universe-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_universeCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.universeCode (context := context) innerLevel outerLevel
            cumulOk levelLe)))
      (Term.universeCode (context := context) innerLevel outerLevel
        cumulOk levelLe) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.universeCode_HEq_congr innerLevel outerLevel cumulOk levelLe

/-- Arrow type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_arrowCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.arrowCode (context := context) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)))
      (Term.arrowCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.arrowCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton domainCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton codomainCodeRaw singletonRaw)

/-- Pi type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_piTyCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1))
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.piTyCode (context := context) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)))
      (Term.piTyCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.piTyCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton domainCodeRaw singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift codomainCodeRaw singletonRaw)

/-- Sigma type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_sigmaTyCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1))
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.sigmaTyCode (context := context) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)))
      (Term.sigmaTyCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.sigmaTyCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton domainCodeRaw singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift codomainCodeRaw singletonRaw)

/-- Product type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_productCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.productCode (context := context) outerLevel levelLe
            firstCodeRaw secondCodeRaw)))
      (Term.productCode (context := context) outerLevel levelLe
        firstCodeRaw secondCodeRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.productCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton firstCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton secondCodeRaw singletonRaw)

/-- Sum type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_sumCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.sumCode (context := context) outerLevel levelLe
            leftCodeRaw rightCodeRaw)))
      (Term.sumCode (context := context) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.sumCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton leftCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightCodeRaw singletonRaw)

/-- List type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_listCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.listCode (context := context) outerLevel levelLe
            elementCodeRaw)))
      (Term.listCode (context := context) outerLevel levelLe
        elementCodeRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.listCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton elementCodeRaw singletonRaw)

/-- Option type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_optionCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.optionCode (context := context) outerLevel levelLe
            elementCodeRaw)))
      (Term.optionCode (context := context) outerLevel levelLe
        elementCodeRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.optionCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton elementCodeRaw singletonRaw)

/-- Either type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_eitherCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.eitherCode (context := context) outerLevel levelLe
            leftCodeRaw rightCodeRaw)))
      (Term.eitherCode (context := context) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.eitherCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton leftCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightCodeRaw singletonRaw)

/-- Identity type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_idCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.idCode (context := context) outerLevel levelLe typeCodeRaw
            leftRaw rightRaw)))
      (Term.idCode (context := context) outerLevel levelLe typeCodeRaw
        leftRaw rightRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.idCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton typeCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton leftRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightRaw singletonRaw)

/-- Equivalence type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_equivCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.equivCode (context := context) outerLevel levelLe
            leftTypeCodeRaw rightTypeCodeRaw)))
      (Term.equivCode (context := context) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.equivCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton leftTypeCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightTypeCodeRaw singletonRaw)

/-- Canonical identity equivalences preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_equivReflId_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.equivReflId (context := context) carrier)))
      (Term.equivReflId (context := context) carrier) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.equivReflId_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)

/-- Id-typed identity equivalence witnesses preserve weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_equivReflIdAtId_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
            carrier carrierRaw)))
      (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
        carrier carrierRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.equivReflIdAtId_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton carrierRaw singletonRaw)

/-- Id-typed funext reflexivity witnesses preserve weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_funextReflAtId_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1))
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.funextReflAtId (context := context) domainType codomainType
            applyRaw)))
      (Term.funextReflAtId (context := context) domainType codomainType
        applyRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.funextReflAtId_HEq_congr
    (Ty.weaken_subst_singleton domainType newType singletonRaw)
    (Ty.weaken_subst_singleton codomainType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift applyRaw singletonRaw)

/-- Glue introduction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_glueIntro_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness baseRaw partialRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw)
    (baseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseValue))
        baseValue)
    (partialHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType partialValue))
        partialValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.glueIntro modeIsUnivalent baseType boundaryWitness
            baseValue partialValue)))
      (Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.glueIntro_HEq_congr modeIsUnivalent
    (Ty.weaken_subst_singleton baseType newType singletonRaw)
    (RawTerm.weaken_subst_singleton boundaryWitness singletonRaw)
    (RawTerm.weaken_subst_singleton baseRaw singletonRaw)
    (RawTerm.weaken_subst_singleton partialRaw singletonRaw)
    baseHEq partialHEq

/-- Cubical transport preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_transp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term context sourceType sourceRaw)
    (pathHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType typePath))
        typePath)
    (sourceHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType sourceValue))
        sourceValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.transp modeIsUnivalent universeLevel universeLevelLt
            sourceType targetType sourceTypeRaw targetTypeRaw typePath
            sourceValue)))
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw typePath
        sourceValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.transp_HEq_congr modeIsUnivalent universeLevel universeLevelLt
    (Ty.weaken_subst_singleton sourceType newType singletonRaw)
    (Ty.weaken_subst_singleton targetType newType singletonRaw)
    (RawTerm.weaken_subst_singleton sourceTypeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton targetTypeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton pathRaw singletonRaw)
    (RawTerm.weaken_subst_singleton sourceRaw singletonRaw)
    pathHEq sourceHEq

/-- Homogeneous composition preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_hcomp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw)
    (sidesHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType sidesValue))
        sidesValue)
    (capHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType capValue))
        capValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.hcomp modeIsUnivalent sidesValue capValue)))
      (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.hcomp_HEq_congr modeIsUnivalent
    (Ty.weaken_subst_singleton carrierType newType singletonRaw)
    (RawTerm.weaken_subst_singleton sidesRaw singletonRaw)
    (RawTerm.weaken_subst_singleton capRaw singletonRaw)
    sidesHEq capHEq

/-- Record introduction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_recordIntro_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (firstField : Term context singleFieldType firstRaw)
    (firstHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType firstField))
        firstField) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.recordIntro firstField)))
      (Term.recordIntro firstField) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.recordIntro_HEq_congr
    (Ty.weaken_subst_singleton singleFieldType newType singletonRaw)
    (RawTerm.weaken_subst_singleton firstRaw singletonRaw)
    firstHEq

/-- Refinement introduction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_refineIntro_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw)
    (baseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseValue))
        baseValue)
    (proofHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType predicateProof))
        predicateProof) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.refineIntro predicate baseValue predicateProof)))
      (Term.refineIntro predicate baseValue predicateProof) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.refineIntro_HEq_congr
    (Ty.weaken_subst_singleton baseType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift predicate singletonRaw)
    (RawTerm.weaken_subst_singleton valueRaw singletonRaw)
    (RawTerm.weaken_subst_singleton proofRaw singletonRaw)
    baseHEq proofHEq

/-- Refinement elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_refineElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (refinedHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType refinedValue))
        refinedValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.refineElim refinedValue)))
      (Term.refineElim refinedValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.refineElim_HEq_congr
    (Ty.weaken_subst_singleton baseType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift predicate singletonRaw)
    (RawTerm.weaken_subst_singleton refinedRaw singletonRaw)
    refinedHEq

/-- Codata unfold preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_codataUnfold_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw)
    (stateHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType initialState))
        initialState)
    (transitionHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType transition))
        transition) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.codataUnfold initialState transition)))
      (Term.codataUnfold initialState transition) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.codataUnfold_HEq_congr
    (Ty.weaken_subst_singleton stateType newType singletonRaw)
    (Ty.weaken_subst_singleton outputType newType singletonRaw)
    (RawTerm.weaken_subst_singleton stateRaw singletonRaw)
    (RawTerm.weaken_subst_singleton transitionRaw singletonRaw)
    stateHEq transitionHEq

/-- Session send preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_sessionSend_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (payload : Term context payloadType payloadRaw)
    (channelHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType channel))
        channel)
    (payloadHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType payload))
        payload) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.sessionSend protocolStep channel payload)))
      (Term.sessionSend protocolStep channel payload) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.sessionSend_HEq_congr
    (RawTerm.weaken_subst_singleton protocolStep singletonRaw)
    (Ty.weaken_subst_singleton payloadType newType singletonRaw)
    (RawTerm.weaken_subst_singleton channelRaw singletonRaw)
    (RawTerm.weaken_subst_singleton payloadRaw singletonRaw)
    channelHEq payloadHEq

/-- Session receive preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_sessionRecv_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep channelRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (channelHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType channel))
        channel) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.sessionRecv channel)))
      (Term.sessionRecv channel) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.sessionRecv_HEq_congr
    (RawTerm.weaken_subst_singleton protocolStep singletonRaw)
    (RawTerm.weaken_subst_singleton channelRaw singletonRaw)
    channelHEq

/-- Univalence-to-equivalence extraction preserves weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_uaToEquiv_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (proof :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw)
    (proofHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType proof))
        proof) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw
            rightTyRaw proof)))
      (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw
        rightTyRaw proof) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.uaToEquiv_HEq_congr
    (Ty.weaken_subst_singleton leftTy newType singletonRaw)
    (Ty.weaken_subst_singleton rightTy newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftTyRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightTyRaw singletonRaw)
    (RawTerm.weaken_subst_singleton proofRaw singletonRaw)
    proofHEq

/-- Path application preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_pathApp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint pathRaw intervalRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw)
    (pathHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType pathTerm))
        pathTerm)
    (intervalHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType intervalTerm))
        intervalTerm) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.pathApp modeIsUnivalent pathTerm intervalTerm)))
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.pathApp_HEq_congr modeIsUnivalent
    (Ty.weaken_subst_singleton carrierType newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton rightEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton pathRaw singletonRaw)
    (RawTerm.weaken_subst_singleton intervalRaw singletonRaw)
    pathHEq intervalHEq

/-- Glue elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_glueElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType gluedValue))
        gluedValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.glueElim modeIsUnivalent gluedValue)))
      (Term.glueElim modeIsUnivalent gluedValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.glueElim_HEq_congr modeIsUnivalent
    (Ty.weaken_subst_singleton baseType newType singletonRaw)
    (RawTerm.weaken_subst_singleton boundaryWitness singletonRaw)
    (RawTerm.weaken_subst_singleton gluedRaw singletonRaw)
    gluedHEq

/-- Record projection preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_recordProj_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (recordValue : Term context (Ty.record singleFieldType) recordRaw)
    (recordHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType recordValue))
        recordValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.recordProj recordValue)))
      (Term.recordProj recordValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.recordProj_HEq_congr
    (Ty.weaken_subst_singleton singleFieldType newType singletonRaw)
    (RawTerm.weaken_subst_singleton recordRaw singletonRaw)
    recordHEq

/-- Codata destruction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_codataDest_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw)
    (codataHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType codataValue))
        codataValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.codataDest codataValue)))
      (Term.codataDest codataValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.codataDest_HEq_congr
    (Ty.weaken_subst_singleton stateType newType singletonRaw)
    (Ty.weaken_subst_singleton outputType newType singletonRaw)
    (RawTerm.weaken_subst_singleton codataRaw singletonRaw)
    codataHEq

/-- Equivalence application preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_equivApp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentValueRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentValue : Term context carrierA argumentValueRaw)
    (equivHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType equivTerm))
        equivTerm)
    (argumentHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType argumentValue))
        argumentValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.equivApp equivTerm argumentValue)))
      (Term.equivApp equivTerm argumentValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.equivApp_HEq_congr
    (Ty.weaken_subst_singleton carrierA newType singletonRaw)
    (Ty.weaken_subst_singleton carrierB newType singletonRaw)
    (RawTerm.weaken_subst_singleton equivRaw singletonRaw)
    (RawTerm.weaken_subst_singleton argumentValueRaw singletonRaw)
    equivHEq argumentHEq

/-- Univalence equivalence application preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_equivApply_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentValueRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentValue : Term context carrierA argumentValueRaw)
    (equivHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType equivTerm))
        equivTerm)
    (argumentHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType argumentValue))
        argumentValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.equivApply equivTerm argumentValue)))
      (Term.equivApply equivTerm argumentValue) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.equivApply_HEq_congr
    (Ty.weaken_subst_singleton carrierA newType singletonRaw)
    (Ty.weaken_subst_singleton carrierB newType singletonRaw)
    (RawTerm.weaken_subst_singleton equivRaw singletonRaw)
    (RawTerm.weaken_subst_singleton argumentValueRaw singletonRaw)
    equivHEq argumentHEq

/-- Heterogeneous univalence introduction preserves weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_uaIntroHet_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (equivWitness :
      Term context (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivWitnessHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType equivWitness))
        equivWitness) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
            equivWitness)))
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
        equivWitness) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
    (Ty.weaken_subst_singleton carrierA newType singletonRaw)
    (Ty.weaken_subst_singleton carrierB newType singletonRaw)
    (RawTerm.weaken_subst_singleton carrierARaw singletonRaw)
    (RawTerm.weaken_subst_singleton carrierBRaw singletonRaw)
    (RawTerm.weaken_subst_singleton forwardRaw singletonRaw)
    (RawTerm.weaken_subst_singleton backwardRaw singletonRaw)
    equivWitnessHEq

/-- Heterogeneous funext introduction preserves weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_funextIntroHet_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1))
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.funextIntroHet (context := context) domainType codomainType
            applyARaw applyBRaw)))
      (Term.funextIntroHet (context := context) domainType codomainType
        applyARaw applyBRaw) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.funextIntroHet_HEq_congr
    (Ty.weaken_subst_singleton domainType newType singletonRaw)
    (Ty.weaken_subst_singleton codomainType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift applyARaw singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift applyBRaw singletonRaw)

/-- Universe cumulativity preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_cumulUp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {lowerLevel higherLevel : UniverseLevel}
    {cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat}
    {levelLeLow : lowerLevel.toNat + 1 ≤ level}
    {levelLeHigh : higherLevel.toNat + 1 ≤ level}
    {codeRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (typeCodeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType typeCode))
        typeCode) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.cumulUp lowerLevel higherLevel cumulMonotone
            levelLeLow levelLeHigh typeCode)))
      (Term.cumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.cumulUp_HEq_congr
    (RawTerm.weaken_subst_singleton codeRaw singletonRaw)
    typeCodeHEq

/-! ## Cast-aware HEq scaffolding for Term.subst_compose

The full `Term.subst_compose` (HEq, 29 cases) is a substantial cascade
because each `lam`/`lamPi`/`appPi`/`pair`/`snd` case has internal Ty
casts that must be aligned across the two formulations.  Following the
W7-analysis: HEq cascade hits a factorization limit at typed Term level.

We attempt the cascade incrementally.  Simple constructor families
(no internal cast on the recursive call) work cleanly; cast-bearing
families are handled with the HEq tactic helpers from
`Tools/Tactics/HEq`. -/

end LeanFX2
