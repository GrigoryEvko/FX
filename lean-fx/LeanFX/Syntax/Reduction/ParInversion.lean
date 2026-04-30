import LeanFX.Syntax.Reduction.ParSubst
import LeanFX.Syntax.ToRaw

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Typed parallel-step source-inversion lemmas.

For each "normal-form-shaped" Term constructor `C`, prove
`Step.par C target → target = C` (modulo args).  Together with
`Step.parStar.<C>_source_inv` (lifted by induction over `parStar`),
these are the key ingredients for the 17 Deep βι case helpers in
`Step.par.cd_lemma_star`.

### Strategy: HEq-generalized induction with toRaw refutation

`cases parStep` directly fails Lean 4's dependent-elimination check
for βι ctors with subst-typed indices.  But generalized
`induction parStep` followed by:
  * `cases typeEq` for type-mismatch ctors (refutes via Ty
    constructor disagreement);
  * `cases typeEq; cases (eq_of_heq srcHEq)` for free-source ctors
    (refutes via Term ctor mismatch at concrete type);
  * `exfalso` + `Term.toRaw_cast` + `cases rawEq` for subst-source
    ctors (refutes via RawTerm ctor mismatch in the toRaw projection),
discharges all 56 cases.

The third path is the breakthrough that sidesteps the dep-elim wall:
it goes through `Term.toRaw` (which doesn't depend on type indices)
and refutes at raw level, where ctor mismatch is decidable. -/

/-- Refute a `HEq sourceTerm Term.boolTrue` when the source's
`toRaw` is not `RawTerm.boolTrue`.  This is the helper for the
6 subst-source βι ctor cases. -/
private theorem refuteViaToRawBoolTrue
    {mode : Mode} {level scope_a : Nat} {ctx_a : Ctx mode level scope_a}
    {sourceType : Ty level scope_a}
    (sourceTerm : Term ctx_a sourceType)
    (typeEq : sourceType = Ty.bool)
    (sourceHEq : HEq sourceTerm
        (@Term.boolTrue mode level scope_a ctx_a))
    (sourceToRaw_neq_boolTrue :
        sourceTerm.toRaw ≠ RawTerm.boolTrue) :
    False := by
  have srcEq : (typeEq ▸ sourceTerm) = Term.boolTrue := by
    apply eq_of_heq
    apply HEq.trans (HEq.symm _) sourceHEq
    exact (eqRec_heq typeEq _).symm
  have rawEq : (typeEq ▸ sourceTerm).toRaw =
               (Term.boolTrue (mode := mode) (level := level) (scope := scope_a)
                              (context := ctx_a)).toRaw :=
    congrArg Term.toRaw srcEq
  rw [Term.toRaw_cast] at rawEq
  exact sourceToRaw_neq_boolTrue rawEq

/-- Generalized typed source-inversion for `Term.boolTrue`. -/
theorem Step.par.boolTrue_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.bool)
    (parStep : Step.par source target) :
    HEq source (@Term.boolTrue mode level scope ctx) →
    HEq target (@Term.boolTrue mode level scope ctx) := by
  induction parStep with
  | refl term => intro sourceEq; exact sourceEq
  -- Type-mismatch ctors.
  | lam => intro _; cases typeEq
  | lamPi => intro _; cases typeEq
  | pair => intro _; cases typeEq
  | natSucc => intro _; cases typeEq
  | listCons => intro _; cases typeEq
  | optionSome => intro _; cases typeEq
  | eitherInl => intro _; cases typeEq
  | eitherInr => intro _; cases typeEq
  | etaArrow => intro _; cases typeEq
  | etaSigma => intro _; cases typeEq
  -- Free-source ctors.
  | app =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | fst =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | boolElim =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | natElim =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | natRec =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | listElim =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | optionMatch =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | eitherMatch =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | idJ =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaBoolElimTrue =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaBoolElimFalse =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaNatElimZero =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaNatElimSucc =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaNatRecZero =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaNatRecSucc =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaListElimNil =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaListElimCons =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaOptionMatchNone =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaOptionMatchSome =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaEitherMatchInl =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaEitherMatchInr =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaIdJRefl =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | betaApp =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | betaFstPair =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | betaAppDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | betaFstPairDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaBoolElimTrueDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaBoolElimFalseDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaNatElimZeroDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaNatElimSuccDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaNatRecZeroDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaNatRecSuccDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaListElimNilDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaListElimConsDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaOptionMatchNoneDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaOptionMatchSomeDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaEitherMatchInlDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaEitherMatchInrDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  | iotaIdJReflDeep =>
      intro srcHEq; cases typeEq; cases (eq_of_heq srcHEq)
  -- Subst-source ctors: refute via Term.toRaw.
  | appPi functionStep argumentStep functionIH argumentIH =>
      intro srcHEq
      exfalso
      rename_i scope_a ctx_a domain_a cod_a f f' a a'
      apply refuteViaToRawBoolTrue
        (@Term.appPi mode level scope_a ctx_a domain_a cod_a f a)
        typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd pairStep pairIH =>
      intro srcHEq
      exfalso
      rename_i scope_a ctx_a first_a second_a p p'
      apply refuteViaToRawBoolTrue
        (@Term.snd mode level scope_a ctx_a first_a second_a p)
        typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi bodyStep argStep bodyIH argIH =>
      intro srcHEq
      exfalso
      rename_i scope_a ctx_a domain_a cod_a body body' arg arg'
      apply refuteViaToRawBoolTrue
        (@Term.appPi mode level scope_a ctx_a domain_a cod_a
           (Term.lamPi body) arg)
        typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep functionStep argStep functionIH argIH =>
      intro srcHEq
      exfalso
      rename_i scope_a ctx_a domain_a cod_a function body arg arg'
      apply refuteViaToRawBoolTrue
        (@Term.appPi mode level scope_a ctx_a domain_a cod_a function arg)
        typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair firstVal secondStep secondIH =>
      intro srcHEq
      exfalso
      rename_i scope_a ctx_a first_a second_a secondVal secondVal'
      apply refuteViaToRawBoolTrue
        (@Term.snd mode level scope_a ctx_a first_a second_a
           (Term.pair firstVal secondVal))
        typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep pairStep pairIH =>
      intro srcHEq
      exfalso
      rename_i scope_a ctx_a first_a second_a pairTerm firstVal secondVal
      apply refuteViaToRawBoolTrue
        (@Term.snd mode level scope_a ctx_a first_a second_a pairTerm)
        typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h

/-- Typed source-inversion for `Step.par` with `Term.boolTrue` source. -/
theorem Step.par.boolTrue_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {target : Term ctx Ty.bool}
    (parStep : Step.par (@Term.boolTrue mode level scope ctx) target) :
    target = Term.boolTrue :=
  eq_of_heq (Step.par.boolTrue_source_inv_general rfl parStep HEq.rfl)

/-- Generalized Step.parStar source-inversion for `Term.boolTrue`.
Generalize the source via Eq so `induction chain` can land. -/
theorem Step.parStar.boolTrue_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {source target : Term ctx Ty.bool}
    (sourceEq : source = Term.boolTrue)
    (chain : Step.parStar source target) :
    target = Term.boolTrue := by
  induction chain with
  | refl _ => exact sourceEq
  | trans firstStep restChain restIH =>
      cases sourceEq
      have stepEq := Step.par.boolTrue_source_inv firstStep
      cases stepEq
      exact restIH rfl

/-- Step.parStar source-inversion for `Term.boolTrue`. -/
theorem Step.parStar.boolTrue_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {target : Term ctx Ty.bool}
    (chain : Step.parStar (@Term.boolTrue mode level scope ctx) target) :
    target = Term.boolTrue :=
  Step.parStar.boolTrue_source_inv_general rfl chain

end LeanFX.Syntax
