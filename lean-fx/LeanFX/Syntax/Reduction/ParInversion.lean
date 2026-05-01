import LeanFX.Syntax.Reduction.ParSubst
import LeanFX.Syntax.ToRaw
import LeanFX.Syntax.Reduction.ParBi

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
theorem refuteViaToRaw
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

/-! ## refl inversion (constant-style — `rawTerm` endpoint is fixed)

`Term.refl rawTerm` has type `Ty.id carrier rawTerm rawTerm`, where
the endpoint is a `RawTerm` (not a typed Term).  The constructor has
no Term subterms, so the inversion is constant-style: target = refl
(same endpoint). -/

/-- Generalized typed source-inversion for `Term.refl`. -/
theorem Step.par.refl_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope}
    {endpoint : RawTerm scope}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.id carrier endpoint endpoint)
    (parStep : Step.par source target) :
    HEq source (@Term.refl mode level scope ctx carrier endpoint) →
    HEq target (@Term.refl mode level scope ctx carrier endpoint) := by
  induction parStep with
  | refl term => intro sourceEq; exact sourceEq
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.refl endpoint) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.refl endpoint) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.refl endpoint) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.refl endpoint) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.refl endpoint) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.refl endpoint) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.refl` source. -/
theorem Step.par.refl_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope}
    {endpoint : RawTerm scope}
    {target : Term ctx (Ty.id carrier endpoint endpoint)}
    (parStep : Step.par
        (@Term.refl mode level scope ctx carrier endpoint) target) :
    target = Term.refl endpoint :=
  eq_of_heq (Step.par.refl_source_inv_general rfl parStep HEq.rfl)

/-- Generalized Step.parStar source-inversion for `Term.refl`. -/
theorem Step.parStar.refl_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope}
    {endpoint : RawTerm scope}
    {source target : Term ctx (Ty.id carrier endpoint endpoint)}
    (sourceEq : source = Term.refl endpoint)
    (chain : Step.parStar source target) :
    target = Term.refl endpoint := by
  induction chain with
  | refl _ => exact sourceEq
  | trans firstStep restChain restIH =>
      cases sourceEq
      have stepEq := Step.par.refl_source_inv firstStep
      cases stepEq
      exact restIH rfl

/-- Step.parStar source-inversion for `Term.refl`. -/
theorem Step.parStar.refl_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope}
    {endpoint : RawTerm scope}
    {target : Term ctx (Ty.id carrier endpoint endpoint)}
    (chain : Step.parStar
        (@Term.refl mode level scope ctx carrier endpoint) target) :
    target = Term.refl endpoint :=
  Step.parStar.refl_source_inv_general rfl chain

/-! ## natSucc structural inversion

For non-constant heads (natSucc, listCons, optionSome, eitherInl,
eitherInr), the inversion is structural: target preserves the head and
the inner step is extracted as an existential.

η-rules don't reduce these heads (η is for arrow/sigma), so the
inversion holds at plain `Step.parStar` level without `isBi` gating.

The natSucc constructor case extracts the inner step directly; refl
gives `Step.par.refl predecessor` for the inner. -/

/-- Generalized typed source-inversion for `Term.natSucc`. -/
theorem Step.par.natSucc_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {predecessor : Term ctx Ty.nat}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.nat)
    (parStep : Step.par source target) :
    HEq source (@Term.natSucc mode level scope ctx predecessor) →
    ∃ (predecessor' : Term ctx Ty.nat),
        HEq target (@Term.natSucc mode level scope ctx predecessor') ∧
        Step.par predecessor predecessor' := by
  induction parStep with
  | refl term =>
      intro sourceHEq
      exact ⟨predecessor, sourceHEq, Step.par.refl predecessor⟩
  | natSucc innerStep _ =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      exact ⟨_, HEq.rfl, innerStep⟩
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.natSucc predecessor) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.natSucc predecessor) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.natSucc predecessor) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.natSucc predecessor) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.natSucc predecessor) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.natSucc predecessor) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.natSucc` source. -/
theorem Step.par.natSucc_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {predecessor : Term ctx Ty.nat}
    {target : Term ctx Ty.nat}
    (parStep : Step.par
        (@Term.natSucc mode level scope ctx predecessor) target) :
    ∃ (predecessor' : Term ctx Ty.nat),
        target = Term.natSucc predecessor' ∧
        Step.par predecessor predecessor' := by
  obtain ⟨predecessor', targetHEq, innerStep⟩ :=
    Step.par.natSucc_source_inv_general rfl parStep HEq.rfl
  exact ⟨predecessor', eq_of_heq targetHEq, innerStep⟩

/-- Step.parStar source-inversion for `Term.natSucc`.  Iterates
single-step inversion through the chain. -/
theorem Step.parStar.natSucc_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {predecessor : Term ctx Ty.nat}
    {target : Term ctx Ty.nat}
    (chain : Step.parStar
        (@Term.natSucc mode level scope ctx predecessor) target) :
    ∃ (predecessor' : Term ctx Ty.nat),
        target = Term.natSucc predecessor' ∧
        Step.parStar predecessor predecessor' := by
  -- Generalize over the source so `induction chain` lands without
  -- dependent-elimination conflicts.
  generalize sourceEq :
      (@Term.natSucc mode level scope ctx predecessor) = sourceTerm
      at chain
  induction chain generalizing predecessor with
  | refl _ =>
      cases sourceEq
      exact ⟨predecessor, rfl, Step.parStar.refl predecessor⟩
  | trans firstStep restChain restIH =>
      cases sourceEq
      obtain ⟨pred₁, eq₁, step₁⟩ := Step.par.natSucc_source_inv firstStep
      obtain ⟨pred', eq', restStar⟩ := restIH eq₁.symm
      exact ⟨pred', eq', Step.parStar.trans step₁ restStar⟩

/-! ## listCons structural inversion (two subterms: head + tail) -/

/-- Generalized typed source-inversion for `Term.listCons`. -/
theorem Step.par.listCons_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {headTerm : Term ctx elementType}
    {tailTerm : Term ctx (Ty.list elementType)}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.list elementType)
    (parStep : Step.par source target) :
    HEq source
        (@Term.listCons mode level scope ctx elementType headTerm tailTerm) →
    ∃ (head' : Term ctx elementType)
      (tail' : Term ctx (Ty.list elementType)),
        HEq target
            (@Term.listCons mode level scope ctx elementType head' tail') ∧
        Step.par headTerm head' ∧ Step.par tailTerm tail' := by
  induction parStep with
  | refl term =>
      intro sourceHEq
      exact ⟨headTerm, tailTerm, sourceHEq,
             Step.par.refl headTerm, Step.par.refl tailTerm⟩
  | listCons headStep tailStep _ _ =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      exact ⟨_, _, HEq.rfl, headStep, tailStep⟩
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.listCons headTerm tailTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.listCons headTerm tailTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.listCons headTerm tailTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.listCons headTerm tailTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.listCons headTerm tailTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.listCons headTerm tailTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.listCons` source. -/
theorem Step.par.listCons_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {headTerm : Term ctx elementType}
    {tailTerm : Term ctx (Ty.list elementType)}
    {target : Term ctx (Ty.list elementType)}
    (parStep : Step.par
        (@Term.listCons mode level scope ctx elementType headTerm tailTerm)
        target) :
    ∃ (head' : Term ctx elementType)
      (tail' : Term ctx (Ty.list elementType)),
        target = Term.listCons head' tail' ∧
        Step.par headTerm head' ∧ Step.par tailTerm tail' := by
  obtain ⟨head', tail', targetHEq, headStep, tailStep⟩ :=
    Step.par.listCons_source_inv_general rfl parStep HEq.rfl
  exact ⟨head', tail', eq_of_heq targetHEq, headStep, tailStep⟩

/-- Step.parStar source-inversion for `Term.listCons`. -/
theorem Step.parStar.listCons_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {headTerm : Term ctx elementType}
    {tailTerm : Term ctx (Ty.list elementType)}
    {target : Term ctx (Ty.list elementType)}
    (chain : Step.parStar
        (@Term.listCons mode level scope ctx elementType headTerm tailTerm)
        target) :
    ∃ (head' : Term ctx elementType)
      (tail' : Term ctx (Ty.list elementType)),
        target = Term.listCons head' tail' ∧
        Step.parStar headTerm head' ∧ Step.parStar tailTerm tail' := by
  generalize sourceEq :
      (@Term.listCons mode level scope ctx elementType headTerm tailTerm)
      = sourceTerm at chain
  induction chain generalizing headTerm tailTerm with
  | refl _ =>
      cases sourceEq
      exact ⟨headTerm, tailTerm, rfl,
             Step.parStar.refl headTerm, Step.parStar.refl tailTerm⟩
  | trans firstStep restChain restIH =>
      cases sourceEq
      obtain ⟨head₁, tail₁, eq₁, headStep₁, tailStep₁⟩ :=
        Step.par.listCons_source_inv firstStep
      obtain ⟨head', tail', eq', headStar, tailStar⟩ := restIH eq₁.symm
      exact ⟨head', tail', eq',
             Step.parStar.trans headStep₁ headStar,
             Step.parStar.trans tailStep₁ tailStar⟩

/-! ## optionSome structural inversion (single subterm: value) -/

/-- Generalized typed source-inversion for `Term.optionSome`. -/
theorem Step.par.optionSome_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueTerm : Term ctx elementType}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.option elementType)
    (parStep : Step.par source target) :
    HEq source
        (@Term.optionSome mode level scope ctx elementType valueTerm) →
    ∃ (value' : Term ctx elementType),
        HEq target
            (@Term.optionSome mode level scope ctx elementType value') ∧
        Step.par valueTerm value' := by
  induction parStep with
  | refl term =>
      intro sourceHEq
      exact ⟨valueTerm, sourceHEq, Step.par.refl valueTerm⟩
  | optionSome valueStep _ =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      exact ⟨_, HEq.rfl, valueStep⟩
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.optionSome valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.optionSome valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.optionSome valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.optionSome valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.optionSome valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.optionSome valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.optionSome` source. -/
theorem Step.par.optionSome_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueTerm : Term ctx elementType}
    {target : Term ctx (Ty.option elementType)}
    (parStep : Step.par
        (@Term.optionSome mode level scope ctx elementType valueTerm)
        target) :
    ∃ (value' : Term ctx elementType),
        target = Term.optionSome value' ∧
        Step.par valueTerm value' := by
  obtain ⟨value', targetHEq, valueStep⟩ :=
    Step.par.optionSome_source_inv_general rfl parStep HEq.rfl
  exact ⟨value', eq_of_heq targetHEq, valueStep⟩

/-- Step.parStar source-inversion for `Term.optionSome`. -/
theorem Step.parStar.optionSome_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueTerm : Term ctx elementType}
    {target : Term ctx (Ty.option elementType)}
    (chain : Step.parStar
        (@Term.optionSome mode level scope ctx elementType valueTerm)
        target) :
    ∃ (value' : Term ctx elementType),
        target = Term.optionSome value' ∧
        Step.parStar valueTerm value' := by
  generalize sourceEq :
      (@Term.optionSome mode level scope ctx elementType valueTerm)
      = sourceTerm at chain
  induction chain generalizing valueTerm with
  | refl _ =>
      cases sourceEq
      exact ⟨valueTerm, rfl, Step.parStar.refl valueTerm⟩
  | trans firstStep restChain restIH =>
      cases sourceEq
      obtain ⟨value₁, eq₁, valueStep₁⟩ :=
        Step.par.optionSome_source_inv firstStep
      obtain ⟨value', eq', valueStar⟩ := restIH eq₁.symm
      exact ⟨value', eq', Step.parStar.trans valueStep₁ valueStar⟩

/-! ## eitherInl / eitherInr structural inversions -/

/-- Generalized typed source-inversion for `Term.eitherInl`. -/
theorem Step.par.eitherInl_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx leftType}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.either leftType rightType)
    (parStep : Step.par source target) :
    HEq source
        (@Term.eitherInl mode level scope ctx leftType rightType valueTerm) →
    ∃ (value' : Term ctx leftType),
        HEq target
            (@Term.eitherInl mode level scope ctx leftType rightType
                value') ∧
        Step.par valueTerm value' := by
  induction parStep with
  | refl term =>
      intro sourceHEq
      exact ⟨valueTerm, sourceHEq, Step.par.refl valueTerm⟩
  | eitherInl valueStep _ =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      exact ⟨_, HEq.rfl, valueStep⟩
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInl (rightType := rightType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInl (rightType := rightType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInl (rightType := rightType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInl (rightType := rightType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInl (rightType := rightType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInl (rightType := rightType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.eitherInl` source. -/
theorem Step.par.eitherInl_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx leftType}
    {target : Term ctx (Ty.either leftType rightType)}
    (parStep : Step.par
        (@Term.eitherInl mode level scope ctx leftType rightType valueTerm)
        target) :
    ∃ (value' : Term ctx leftType),
        target = Term.eitherInl (rightType := rightType) value' ∧
        Step.par valueTerm value' := by
  obtain ⟨value', targetHEq, valueStep⟩ :=
    Step.par.eitherInl_source_inv_general rfl parStep HEq.rfl
  exact ⟨value', eq_of_heq targetHEq, valueStep⟩

/-- Step.parStar source-inversion for `Term.eitherInl`. -/
theorem Step.parStar.eitherInl_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx leftType}
    {target : Term ctx (Ty.either leftType rightType)}
    (chain : Step.parStar
        (@Term.eitherInl mode level scope ctx leftType rightType valueTerm)
        target) :
    ∃ (value' : Term ctx leftType),
        target = Term.eitherInl (rightType := rightType) value' ∧
        Step.parStar valueTerm value' := by
  generalize sourceEq :
      (@Term.eitherInl mode level scope ctx leftType rightType valueTerm)
      = sourceTerm at chain
  induction chain generalizing valueTerm with
  | refl _ =>
      cases sourceEq
      exact ⟨valueTerm, rfl, Step.parStar.refl valueTerm⟩
  | trans firstStep restChain restIH =>
      cases sourceEq
      obtain ⟨value₁, eq₁, valueStep₁⟩ :=
        Step.par.eitherInl_source_inv firstStep
      obtain ⟨value', eq', valueStar⟩ := restIH eq₁.symm
      exact ⟨value', eq', Step.parStar.trans valueStep₁ valueStar⟩

/-- Generalized typed source-inversion for `Term.eitherInr`. -/
theorem Step.par.eitherInr_source_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx rightType}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.either leftType rightType)
    (parStep : Step.par source target) :
    HEq source
        (@Term.eitherInr mode level scope ctx leftType rightType valueTerm) →
    ∃ (value' : Term ctx rightType),
        HEq target
            (@Term.eitherInr mode level scope ctx leftType rightType
                value') ∧
        Step.par valueTerm value' := by
  induction parStep with
  | refl term =>
      intro sourceHEq
      exact ⟨valueTerm, sourceHEq, Step.par.refl valueTerm⟩
  | eitherInr valueStep _ =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      exact ⟨_, HEq.rfl, valueStep⟩
  | appPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInr (leftType := leftType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | snd =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInr (leftType := leftType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPi =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInr (leftType := leftType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaAppPiDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInr (leftType := leftType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPair =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInr (leftType := leftType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | betaSndPairDeep =>
      intro srcHEq; exfalso
      apply refuteViaToRaw _ (Term.eitherInr (leftType := leftType)
        valueTerm) typeEq srcHEq
      intro h; simp only [Term.toRaw] at h; cases h
  | _ => intro srcHEq; cases typeEq <;> cases (eq_of_heq srcHEq)

/-- Typed source-inversion for `Step.par` with `Term.eitherInr` source. -/
theorem Step.par.eitherInr_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx rightType}
    {target : Term ctx (Ty.either leftType rightType)}
    (parStep : Step.par
        (@Term.eitherInr mode level scope ctx leftType rightType valueTerm)
        target) :
    ∃ (value' : Term ctx rightType),
        target = Term.eitherInr (leftType := leftType) value' ∧
        Step.par valueTerm value' := by
  obtain ⟨value', targetHEq, valueStep⟩ :=
    Step.par.eitherInr_source_inv_general rfl parStep HEq.rfl
  exact ⟨value', eq_of_heq targetHEq, valueStep⟩

/-- Step.parStar source-inversion for `Term.eitherInr`. -/
theorem Step.parStar.eitherInr_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx rightType}
    {target : Term ctx (Ty.either leftType rightType)}
    (chain : Step.parStar
        (@Term.eitherInr mode level scope ctx leftType rightType valueTerm)
        target) :
    ∃ (value' : Term ctx rightType),
        target = Term.eitherInr (leftType := leftType) value' ∧
        Step.parStar valueTerm value' := by
  generalize sourceEq :
      (@Term.eitherInr mode level scope ctx leftType rightType valueTerm)
      = sourceTerm at chain
  induction chain generalizing valueTerm with
  | refl _ =>
      cases sourceEq
      exact ⟨valueTerm, rfl, Step.parStar.refl valueTerm⟩
  | trans firstStep restChain restIH =>
      cases sourceEq
      obtain ⟨value₁, eq₁, valueStep₁⟩ :=
        Step.par.eitherInr_source_inv firstStep
      obtain ⟨value', eq', valueStar⟩ := restIH eq₁.symm
      exact ⟨value', eq', Step.parStar.trans valueStep₁ valueStar⟩

/-! ## Lam target inversion under isBi gating.

The key insight (per `Step.par.toRawBridge`): inducting on
`Step.par.isBi parStep` automatically OMITS etaArrow / etaSigma
because the isBi predicate has no constructors for them.  This
sidesteps the dep-elim wall that blocks `cases (h : Step.par.isBi
(Step.par.etaArrow _))` — we never reach those cases. -/

/-- Generalized lam target inversion under isBi.  The HEq
generalization sidesteps Lean 4's restriction that `induction`
target type indices be variables. -/
theorem Step.par.lam_target_inv_isBi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body : Term (ctx.cons domainType) codomainType.weaken}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.arrow domainType codomainType)
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    HEq sourceTerm
        (@Term.lam mode level scope ctx domainType codomainType body) →
    ∃ (body' : Term (ctx.cons domainType) codomainType.weaken),
        HEq targetTerm
            (@Term.lam mode level scope ctx domainType codomainType body') ∧
        Step.par body body' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨body, sourceHEq, Step.par.refl body⟩
  | lam _bodyBi _bodyIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i bodyStep
      exact ⟨_, HEq.rfl, bodyStep⟩
  | lamPi _bodyBi _bodyIH =>
      -- Source = Term.lamPi body, type = Ty.piTy domain codomain.
      -- typeEq forces termType = Ty.arrow domain' codomain', so the
      -- source type Ty.piTy ≠ Ty.arrow refutes via Ty ctor mismatch.
      intro _
      cases typeEq
  | _ =>
      intro sourceHEq
      exfalso
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (apply refuteViaToRaw _ (Term.lam body) typeEq sourceHEq;
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Single-step lam target inversion under isBi gating. -/
theorem Step.par.lam_target_inv_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body : Term (ctx.cons domainType) codomainType.weaken}
    {target : Term ctx (Ty.arrow domainType codomainType)}
    {parStep : Step.par
        (@Term.lam mode level scope ctx domainType codomainType body) target}
    (stepBi : Step.par.isBi parStep) :
    ∃ (body' : Term (ctx.cons domainType) codomainType.weaken),
        target = Term.lam body' ∧ Step.par body body' := by
  obtain ⟨body', targetHEq, innerStep⟩ :=
    Step.par.lam_target_inv_isBi_general rfl stepBi HEq.rfl
  exact ⟨body', eq_of_heq targetHEq, innerStep⟩

/-! ## Lam target inversion (chain version under isBi gating). -/

/-- Generalized chain lam target inversion under isBi.

The breakthrough: induct on `chainBi` (the `Step.parStar.isBi` Prop
witness) directly — NOT on the underlying chain.  Inducting on
chainBi gives concrete chain shapes per case (refl / trans), and
chainBi has no etaArrow/etaSigma ctors so η is automatically
omitted — same technique as the single-step version.

Keeping `body` universally quantified INSIDE the conclusion lets
the IH be re-instantiated with the intermediate body produced by
the single-step lam target inversion at each chain link. -/
theorem Step.parStar.lam_target_inv_isBi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.arrow domainType codomainType)
    {chain : Step.parStar sourceTerm targetTerm}
    (chainBi : Step.parStar.isBi chain) :
    ∀ (body : Term (ctx.cons domainType) codomainType.weaken),
    HEq sourceTerm
        (@Term.lam mode level scope ctx domainType codomainType body) →
    ∃ (body' : Term (ctx.cons domainType) codomainType.weaken),
        HEq targetTerm
            (@Term.lam mode level scope ctx domainType codomainType body') ∧
        Step.parStar body body' := by
  induction chainBi with
  | refl term =>
      intro body sourceHEq
      exact ⟨body, sourceHEq, Step.parStar.refl body⟩
  | trans firstBi _restBi restIH =>
      intro body sourceHEq
      obtain ⟨bodyMid, secondHEq, midStep⟩ :=
        Step.par.lam_target_inv_isBi_general typeEq firstBi sourceHEq
      obtain ⟨body', targetHEq, restStep⟩ :=
        restIH bodyMid secondHEq
      exact ⟨body', targetHEq,
             Step.parStar.trans midStep restStep⟩

/-- Single-step chain lam target inversion under isBi gating. -/
theorem Step.parStar.lam_target_inv_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body : Term (ctx.cons domainType) codomainType.weaken}
    {target : Term ctx (Ty.arrow domainType codomainType)}
    {chain : Step.parStar
        (@Term.lam mode level scope ctx domainType codomainType body) target}
    (chainBi : Step.parStar.isBi chain) :
    ∃ (body' : Term (ctx.cons domainType) codomainType.weaken),
        target = Term.lam body' ∧ Step.parStar body body' := by
  obtain ⟨body', targetHEq, innerStep⟩ :=
    Step.parStar.lam_target_inv_isBi_general (chain := chain) rfl chainBi body HEq.rfl
  exact ⟨body', eq_of_heq targetHEq, innerStep⟩

/-! ## LamPi target inversion (Π-binder analogue of lam).

Π-binder (Term.lamPi : Term ctx (Ty.piTy domain codomain)) where
codomainType depends on the bound variable.  Body type is
codomainType (NOT codomainType.weaken).  Same recipe as lam: HEq
generalization sidesteps the dep-elim wall, refuteViaToRaw handles
the 5 subst-target ctors, induction on isBi omits η. -/

/-- Generalized Π-binder target inversion under isBi. -/
theorem Step.par.lamPi_target_inv_isBi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body : Term (ctx.cons domainType) codomainType}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.piTy domainType codomainType)
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    HEq sourceTerm
        (@Term.lamPi mode level scope ctx domainType codomainType body) →
    ∃ (body' : Term (ctx.cons domainType) codomainType),
        HEq targetTerm
            (@Term.lamPi mode level scope ctx domainType codomainType body') ∧
        Step.par body body' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨body, sourceHEq, Step.par.refl body⟩
  | lamPi _bodyBi _bodyIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i bodyStep
      exact ⟨_, HEq.rfl, bodyStep⟩
  | lam _bodyBi _bodyIH =>
      -- Source = Term.lam body, type = Ty.arrow domain codomain.
      -- typeEq forces termType = Ty.piTy ... — Ty ctor mismatch.
      intro _
      cases typeEq
  | _ =>
      intro sourceHEq
      exfalso
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (apply refuteViaToRaw _ (Term.lamPi body) typeEq sourceHEq;
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Single-step Π-binder target inversion under isBi gating. -/
theorem Step.par.lamPi_target_inv_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body : Term (ctx.cons domainType) codomainType}
    {target : Term ctx (Ty.piTy domainType codomainType)}
    {parStep : Step.par
        (@Term.lamPi mode level scope ctx domainType codomainType body) target}
    (stepBi : Step.par.isBi parStep) :
    ∃ (body' : Term (ctx.cons domainType) codomainType),
        target = Term.lamPi body' ∧ Step.par body body' := by
  obtain ⟨body', targetHEq, innerStep⟩ :=
    Step.par.lamPi_target_inv_isBi_general rfl stepBi HEq.rfl
  exact ⟨body', eq_of_heq targetHEq, innerStep⟩

/-! ## LamPi target inversion (chain version). -/

/-- Generalized chain Π-binder target inversion under isBi.  Same
recipe as `Step.parStar.lam_target_inv_isBi_general`. -/
theorem Step.parStar.lamPi_target_inv_isBi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.piTy domainType codomainType)
    {chain : Step.parStar sourceTerm targetTerm}
    (chainBi : Step.parStar.isBi chain) :
    ∀ (body : Term (ctx.cons domainType) codomainType),
    HEq sourceTerm
        (@Term.lamPi mode level scope ctx domainType codomainType body) →
    ∃ (body' : Term (ctx.cons domainType) codomainType),
        HEq targetTerm
            (@Term.lamPi mode level scope ctx domainType codomainType body') ∧
        Step.parStar body body' := by
  induction chainBi with
  | refl term =>
      intro body sourceHEq
      exact ⟨body, sourceHEq, Step.parStar.refl body⟩
  | trans firstBi _restBi restIH =>
      intro body sourceHEq
      obtain ⟨bodyMid, secondHEq, midStep⟩ :=
        Step.par.lamPi_target_inv_isBi_general typeEq firstBi sourceHEq
      obtain ⟨body', targetHEq, restStep⟩ :=
        restIH bodyMid secondHEq
      exact ⟨body', targetHEq,
             Step.parStar.trans midStep restStep⟩

/-- Single-step chain Π-binder target inversion under isBi gating. -/
theorem Step.parStar.lamPi_target_inv_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body : Term (ctx.cons domainType) codomainType}
    {target : Term ctx (Ty.piTy domainType codomainType)}
    {chain : Step.parStar
        (@Term.lamPi mode level scope ctx domainType codomainType body) target}
    (chainBi : Step.parStar.isBi chain) :
    ∃ (body' : Term (ctx.cons domainType) codomainType),
        target = Term.lamPi body' ∧ Step.parStar body body' := by
  obtain ⟨body', targetHEq, innerStep⟩ :=
    Step.parStar.lamPi_target_inv_isBi_general
      (chain := chain) rfl chainBi body HEq.rfl
  exact ⟨body', eq_of_heq targetHEq, innerStep⟩

/-! ## Pair target inversion (under isBi-chain gating). -/

/-- Generalized pair target inversion under isBi.  Same template
as lam: induct on `stepBi`, using HEq generalization for the
target type indices. -/
theorem Step.par.pair_target_inv_isBi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal : Term ctx firstType}
    {secondVal : Term ctx (secondType.subst0 firstType)}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.sigmaTy firstType secondType)
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    HEq sourceTerm
        (@Term.pair mode level scope ctx firstType secondType
            firstVal secondVal) →
    ∃ (firstVal' : Term ctx firstType)
      (secondVal' : Term ctx (secondType.subst0 firstType)),
        HEq targetTerm
            (@Term.pair mode level scope ctx firstType secondType
                firstVal' secondVal') ∧
        Step.par firstVal firstVal' ∧
        Step.par secondVal secondVal' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨firstVal, secondVal, sourceHEq,
             Step.par.refl firstVal, Step.par.refl secondVal⟩
  | pair _firstBi _secondBi _firstIH _secondIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i firstStep secondStep
      exact ⟨_, _, HEq.rfl, firstStep, secondStep⟩
  | _ =>
      intro sourceHEq
      exfalso
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (apply refuteViaToRaw _ (Term.pair firstVal secondVal)
              typeEq sourceHEq;
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Single-step pair target inversion under isBi gating. -/
theorem Step.par.pair_target_inv_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal : Term ctx firstType}
    {secondVal : Term ctx (secondType.subst0 firstType)}
    {target : Term ctx (Ty.sigmaTy firstType secondType)}
    {parStep : Step.par
        (@Term.pair mode level scope ctx firstType secondType
            firstVal secondVal) target}
    (stepBi : Step.par.isBi parStep) :
    ∃ (firstVal' : Term ctx firstType)
      (secondVal' : Term ctx (secondType.subst0 firstType)),
        target = Term.pair firstVal' secondVal' ∧
        Step.par firstVal firstVal' ∧
        Step.par secondVal secondVal' := by
  obtain ⟨firstVal', secondVal', targetHEq, firstStep, secondStep⟩ :=
    Step.par.pair_target_inv_isBi_general rfl stepBi HEq.rfl
  exact ⟨firstVal', secondVal', eq_of_heq targetHEq, firstStep, secondStep⟩

/-! ## Pair target inversion (chain version under isBi gating). -/

/-- Generalized chain pair target inversion under isBi.  Same
recipe as `Step.parStar.lam_target_inv_isBi_general`: induct on
`chainBi` directly, keeping the components universally quantified
inside the goal so the IH absorbs intermediate values produced by
each chain link's single-step inversion. -/
theorem Step.parStar.pair_target_inv_isBi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.sigmaTy firstType secondType)
    {chain : Step.parStar sourceTerm targetTerm}
    (chainBi : Step.parStar.isBi chain) :
    ∀ (firstVal : Term ctx firstType)
      (secondVal : Term ctx (secondType.subst0 firstType)),
    HEq sourceTerm
        (@Term.pair mode level scope ctx firstType secondType
            firstVal secondVal) →
    ∃ (firstVal' : Term ctx firstType)
      (secondVal' : Term ctx (secondType.subst0 firstType)),
        HEq targetTerm
            (@Term.pair mode level scope ctx firstType secondType
                firstVal' secondVal') ∧
        Step.parStar firstVal firstVal' ∧
        Step.parStar secondVal secondVal' := by
  induction chainBi with
  | refl term =>
      intro firstVal secondVal sourceHEq
      exact ⟨firstVal, secondVal, sourceHEq,
             Step.parStar.refl firstVal,
             Step.parStar.refl secondVal⟩
  | trans firstBi _restBi restIH =>
      intro firstVal secondVal sourceHEq
      obtain ⟨firstMid, secondMid, secondHEq, firstStep, secondStep⟩ :=
        Step.par.pair_target_inv_isBi_general typeEq firstBi sourceHEq
      obtain ⟨firstVal', secondVal', targetHEq, firstStar, secondStar⟩ :=
        restIH firstMid secondMid secondHEq
      exact ⟨firstVal', secondVal', targetHEq,
             Step.parStar.trans firstStep firstStar,
             Step.parStar.trans secondStep secondStar⟩

/-- Single-step chain pair target inversion under isBi gating. -/
theorem Step.parStar.pair_target_inv_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal : Term ctx firstType}
    {secondVal : Term ctx (secondType.subst0 firstType)}
    {target : Term ctx (Ty.sigmaTy firstType secondType)}
    {chain : Step.parStar
        (@Term.pair mode level scope ctx firstType secondType
            firstVal secondVal) target}
    (chainBi : Step.parStar.isBi chain) :
    ∃ (firstVal' : Term ctx firstType)
      (secondVal' : Term ctx (secondType.subst0 firstType)),
        target = Term.pair firstVal' secondVal' ∧
        Step.parStar firstVal firstVal' ∧
        Step.parStar secondVal secondVal' := by
  obtain ⟨firstVal', secondVal', targetHEq, firstStar, secondStar⟩ :=
    Step.parStar.pair_target_inv_isBi_general
      (chain := chain) rfl chainBi firstVal secondVal HEq.rfl
  exact ⟨firstVal', secondVal', eq_of_heq targetHEq, firstStar, secondStar⟩

end LeanFX.Syntax
