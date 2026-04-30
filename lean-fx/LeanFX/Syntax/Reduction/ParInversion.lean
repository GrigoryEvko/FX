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

/-- Refute a `HEq sourceTerm targetTerm` when the source's `toRaw`
disagrees with the target's `toRaw`.  Generic over the target;
each source-inversion specializes the target to `Term.boolTrue`,
`Term.boolFalse`, `Term.natZero`, etc.

The proof's three-step rewrite (HEq→Eq via `▸`, congrArg toRaw,
strip cast via `Term.toRaw_cast`) is the SAME for every Term
constant — the parameter `targetTerm` carries the only variation.
This is what factors the 13 individual inversions into one shared
helper. -/
private theorem refuteViaToRaw
    {mode : Mode} {level scope_a : Nat} {ctx_a : Ctx mode level scope_a}
    {sourceType targetType : Ty level scope_a}
    (sourceTerm : Term ctx_a sourceType)
    (targetTerm : Term ctx_a targetType)
    (typeEq : sourceType = targetType)
    (sourceHEq : HEq sourceTerm targetTerm)
    (sourceToRaw_neq_targetToRaw :
        sourceTerm.toRaw ≠ targetTerm.toRaw) :
    False := by
  have srcEq : (typeEq ▸ sourceTerm) = targetTerm := by
    apply eq_of_heq
    apply HEq.trans (HEq.symm _) sourceHEq
    exact (eqRec_heq typeEq _).symm
  have rawEq : (typeEq ▸ sourceTerm).toRaw = targetTerm.toRaw :=
    congrArg Term.toRaw srcEq
  rw [Term.toRaw_cast] at rawEq
  exact sourceToRaw_neq_targetToRaw rawEq

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
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolTrue typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolTrue typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolTrue typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolTrue typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolTrue typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolTrue typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

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

/-! ## boolFalse inversion (mirror of boolTrue) -/

/-- Generalized typed source-inversion for `Term.boolFalse`. -/
theorem Step.par.boolFalse_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.bool)
    (parStep : Step.par source target) :
    HEq source (@Term.boolFalse mode level scope ctx) →
    HEq target (@Term.boolFalse mode level scope ctx) := by
  induction parStep with
  | refl term => intro sourceEq; exact sourceEq
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolFalse typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolFalse typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolFalse typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolFalse typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolFalse typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.boolFalse typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.boolFalse` source. -/
theorem Step.par.boolFalse_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {target : Term ctx Ty.bool}
    (parStep : Step.par (@Term.boolFalse mode level scope ctx) target) :
    target = Term.boolFalse :=
  eq_of_heq (Step.par.boolFalse_source_inv_general rfl parStep HEq.rfl)

/-- Generalized Step.parStar source-inversion for `Term.boolFalse`. -/
theorem Step.parStar.boolFalse_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {source target : Term ctx Ty.bool}
    (sourceEq : source = Term.boolFalse)
    (chain : Step.parStar source target) :
    target = Term.boolFalse := by
  induction chain with
  | refl _ => exact sourceEq
  | trans firstStep restChain restIH =>
      cases sourceEq
      have stepEq := Step.par.boolFalse_source_inv firstStep
      cases stepEq
      exact restIH rfl

/-- Step.parStar source-inversion for `Term.boolFalse`. -/
theorem Step.parStar.boolFalse_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {target : Term ctx Ty.bool}
    (chain : Step.parStar (@Term.boolFalse mode level scope ctx) target) :
    target = Term.boolFalse :=
  Step.parStar.boolFalse_source_inv_general rfl chain

/-! ## natZero inversion

Compact form using `case` for the 6 subst-source ctors and `all_goals`
for the remaining 50 (refl handled explicitly to pass through the
HEq).  The combined `cases typeEq; cases (eq_of_heq srcHEq)` discharges
both type-mismatch (cases typeEq refutes via Ty ctor mismatch) and
free-source (cases typeEq substitutes, cases sourceHEq refutes via
Term ctor mismatch) ctors uniformly. -/

/-- Generalized typed source-inversion for `Term.natZero`. -/
theorem Step.par.natZero_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.nat)
    (parStep : Step.par source target) :
    HEq source (@Term.natZero mode level scope ctx) →
    HEq target (@Term.natZero mode level scope ctx) := by
  induction parStep with
  | refl term => intro sourceEq; exact sourceEq
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.natZero typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.natZero typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.natZero typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.natZero typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.natZero typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.natZero typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.natZero` source. -/
theorem Step.par.natZero_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {target : Term ctx Ty.nat}
    (parStep : Step.par (@Term.natZero mode level scope ctx) target) :
    target = Term.natZero :=
  eq_of_heq (Step.par.natZero_source_inv_general rfl parStep HEq.rfl)

/-- Generalized Step.parStar source-inversion for `Term.natZero`. -/
theorem Step.parStar.natZero_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {source target : Term ctx Ty.nat}
    (sourceEq : source = Term.natZero)
    (chain : Step.parStar source target) :
    target = Term.natZero := by
  induction chain with
  | refl _ => exact sourceEq
  | trans firstStep restChain restIH =>
      cases sourceEq
      have stepEq := Step.par.natZero_source_inv firstStep
      cases stepEq
      exact restIH rfl

/-- Step.parStar source-inversion for `Term.natZero`. -/
theorem Step.parStar.natZero_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {target : Term ctx Ty.nat}
    (chain : Step.parStar (@Term.natZero mode level scope ctx) target) :
    target = Term.natZero :=
  Step.parStar.natZero_source_inv_general rfl chain

/-! ## listNil inversion -/

/-- Generalized typed source-inversion for `Term.listNil`. -/
theorem Step.par.listNil_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.list elementType)
    (parStep : Step.par source target) :
    HEq source (@Term.listNil mode level scope ctx elementType) →
    HEq target (@Term.listNil mode level scope ctx elementType) := by
  induction parStep with
  | refl term => intro sourceEq; exact sourceEq
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.listNil typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.listNil typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.listNil typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.listNil typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.listNil typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.listNil typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.listNil` source. -/
theorem Step.par.listNil_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {target : Term ctx (Ty.list elementType)}
    (parStep : Step.par
        (@Term.listNil mode level scope ctx elementType) target) :
    target = Term.listNil :=
  eq_of_heq (Step.par.listNil_source_inv_general rfl parStep HEq.rfl)

/-- Generalized Step.parStar source-inversion for `Term.listNil`. -/
theorem Step.parStar.listNil_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {source target : Term ctx (Ty.list elementType)}
    (sourceEq : source = Term.listNil)
    (chain : Step.parStar source target) :
    target = Term.listNil := by
  induction chain with
  | refl _ => exact sourceEq
  | trans firstStep restChain restIH =>
      cases sourceEq
      have stepEq := Step.par.listNil_source_inv firstStep
      cases stepEq
      exact restIH rfl

/-- Step.parStar source-inversion for `Term.listNil`. -/
theorem Step.parStar.listNil_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {target : Term ctx (Ty.list elementType)}
    (chain : Step.parStar
        (@Term.listNil mode level scope ctx elementType) target) :
    target = Term.listNil :=
  Step.parStar.listNil_source_inv_general rfl chain

/-! ## optionNone inversion -/

/-- Generalized typed source-inversion for `Term.optionNone`. -/
theorem Step.par.optionNone_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.option elementType)
    (parStep : Step.par source target) :
    HEq source (@Term.optionNone mode level scope ctx elementType) →
    HEq target (@Term.optionNone mode level scope ctx elementType) := by
  induction parStep with
  | refl term => intro sourceEq; exact sourceEq
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.optionNone typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.optionNone typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.optionNone typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.optionNone typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.optionNone typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ Term.optionNone typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.optionNone` source. -/
theorem Step.par.optionNone_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {target : Term ctx (Ty.option elementType)}
    (parStep : Step.par
        (@Term.optionNone mode level scope ctx elementType) target) :
    target = Term.optionNone :=
  eq_of_heq (Step.par.optionNone_source_inv_general rfl parStep HEq.rfl)

/-- Generalized Step.parStar source-inversion for `Term.optionNone`. -/
theorem Step.parStar.optionNone_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {source target : Term ctx (Ty.option elementType)}
    (sourceEq : source = Term.optionNone)
    (chain : Step.parStar source target) :
    target = Term.optionNone := by
  induction chain with
  | refl _ => exact sourceEq
  | trans firstStep restChain restIH =>
      cases sourceEq
      have stepEq := Step.par.optionNone_source_inv firstStep
      cases stepEq
      exact restIH rfl

/-- Step.parStar source-inversion for `Term.optionNone`. -/
theorem Step.parStar.optionNone_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {target : Term ctx (Ty.option elementType)}
    (chain : Step.parStar
        (@Term.optionNone mode level scope ctx elementType) target) :
    target = Term.optionNone :=
  Step.parStar.optionNone_source_inv_general rfl chain

end LeanFX.Syntax
