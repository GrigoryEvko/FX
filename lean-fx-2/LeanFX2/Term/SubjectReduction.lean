import LeanFX2.Reduction.StepStar

/-! # Term/SubjectReduction — type preservation for closed types

Closed types (`Ty.unit`, `Ty.bool`, `Ty.nat`) have no free type-
variable references and are fixed points of `Ty.weaken` and
`Ty.subst0` by definitional equality.  This makes subject
reduction at the `Step` level a trivial structural argument for
these types: every `Step` ctor's target type is computed from
the source type via operations that fix closed types.

## Why this matters

Without general subject reduction, lifting `Conv` cong rules to
unary canonical heads (`Conv.canonical_natSucc`,
`Conv.canonical_listCons`, ...) is blocked because the
existentially-quantified middle type in `Conv` cannot be
constrained to match the head's expected type.

For closed types, this lemma supplies the missing constraint:
`StepStar source mid → mid's type = source's type`.

## What's proved here

* `Step.preserves_ty_unit`: `Step (t : Term ctx Ty.unit _) _ → tgtType = Ty.unit`
* `Step.preserves_ty_bool`: same for `Ty.bool`
* `Step.preserves_ty_nat`: same for `Ty.nat`
* `StepStar.preserves_ty_unit / bool / nat`: chain extensions

## What's NOT proved here

General subject reduction for open or substitution-laden types
(arrow, piTy, sigmaTy, id, listType, etc.) needs richer
machinery (typed `Conv`-modulo subject reduction, or a full
metatheory).  Deferred to a later phase.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## Substitution invariance for closed-type results

If `T.subst0 α raw₁ = Ty.nat`, then `T.subst0 α raw₂ = Ty.nat`
for any other `raw₂` — because `Ty.nat` is a leaf ctor and the
raw argument is consulted only inside `Ty.id` endpoints, which
can never reduce to `Ty.nat` under substitution. -/
theorem Ty.subst0_raw_invariance_nat
    {someType : Ty level (scope + 1)} {argType : Ty level scope}
    {raw1 raw2 : RawTerm scope}
    (someTypeReducesToNat : someType.subst0 argType raw1 = Ty.nat) :
    someType.subst0 argType raw2 = Ty.nat := by
  cases someType with
  | unit => nomatch someTypeReducesToNat
  | bool => nomatch someTypeReducesToNat
  | nat => rfl
  | arrow _ _ => nomatch someTypeReducesToNat
  | piTy _ _ => nomatch someTypeReducesToNat
  | sigmaTy _ _ => nomatch someTypeReducesToNat
  | tyVar position =>
    cases position with
    | mk val isLt =>
      cases val with
      | zero => exact someTypeReducesToNat
      | succ k => nomatch someTypeReducesToNat
  | id _ _ _ => nomatch someTypeReducesToNat
  | listType _ => nomatch someTypeReducesToNat
  | optionType _ => nomatch someTypeReducesToNat
  | eitherType _ _ => nomatch someTypeReducesToNat

/-! ## Closed-type preservation: per-ctor case analysis

Each `Step` ctor's target type is one of:
* Same as source (cong rules — `appLeft`, `natSuccPred`, ...)
* `closedType.weaken.subst0 dom argRaw` for some `closedType`
  (β rules — `betaApp`, `betaSndPair`)
* `closedType.subst0 dom argRaw` for some `closedType`
  (`betaAppPi`, the dep β)
* `motiveType` for the ι rules — preserved when motive equals
  the source's type

For closed types like `Ty.nat`, all `weaken` and `subst0`
operations are `rfl` — these reduce by computation to the
original closed type.
-/

/-- Generalized form: every `Step` whose source has type `Ty.nat`
produces a target of type `Ty.nat`.  The source type is kept
as a variable to enable `induction` (Lean's dep-elim refuses to
case-split when the source type is fixed to `Ty.nat`).

Each `Step` ctor either preserves the source type structurally
(cong rules) or computes a new type via Ty.subst — for closed
types like `Ty.nat`, both reduce to the source type by `rfl`. -/
theorem Step.preserves_ty_nat
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceIsNat : sourceType = Ty.nat) :
    targetType = Ty.nat := by
  induction someStep
  all_goals
    first
      | exact sourceIsNat
      | (subst sourceIsNat; rfl)
      | rfl
      -- betaSndPair: source = sT.subst0 fT (fst (pair fr sr)),
      -- target = sT.subst0 fT fr.  Use raw-invariance lemma.
      | exact Ty.subst0_raw_invariance_nat sourceIsNat

/-! ## Closed-type analogs for Ty.unit and Ty.bool -/

/-- Substitution-raw-invariance for `Ty.unit`. -/
theorem Ty.subst0_raw_invariance_unit
    {someType : Ty level (scope + 1)} {argType : Ty level scope}
    {raw1 raw2 : RawTerm scope}
    (someTypeReducesToUnit : someType.subst0 argType raw1 = Ty.unit) :
    someType.subst0 argType raw2 = Ty.unit := by
  cases someType with
  | unit => rfl
  | bool => nomatch someTypeReducesToUnit
  | nat => nomatch someTypeReducesToUnit
  | arrow _ _ => nomatch someTypeReducesToUnit
  | piTy _ _ => nomatch someTypeReducesToUnit
  | sigmaTy _ _ => nomatch someTypeReducesToUnit
  | tyVar position =>
    cases position with
    | mk val isLt =>
      cases val with
      | zero => exact someTypeReducesToUnit
      | succ k => nomatch someTypeReducesToUnit
  | id _ _ _ => nomatch someTypeReducesToUnit
  | listType _ => nomatch someTypeReducesToUnit
  | optionType _ => nomatch someTypeReducesToUnit
  | eitherType _ _ => nomatch someTypeReducesToUnit

/-- Substitution-raw-invariance for `Ty.bool`. -/
theorem Ty.subst0_raw_invariance_bool
    {someType : Ty level (scope + 1)} {argType : Ty level scope}
    {raw1 raw2 : RawTerm scope}
    (someTypeReducesToBool : someType.subst0 argType raw1 = Ty.bool) :
    someType.subst0 argType raw2 = Ty.bool := by
  cases someType with
  | unit => nomatch someTypeReducesToBool
  | bool => rfl
  | nat => nomatch someTypeReducesToBool
  | arrow _ _ => nomatch someTypeReducesToBool
  | piTy _ _ => nomatch someTypeReducesToBool
  | sigmaTy _ _ => nomatch someTypeReducesToBool
  | tyVar position =>
    cases position with
    | mk val isLt =>
      cases val with
      | zero => exact someTypeReducesToBool
      | succ k => nomatch someTypeReducesToBool
  | id _ _ _ => nomatch someTypeReducesToBool
  | listType _ => nomatch someTypeReducesToBool
  | optionType _ => nomatch someTypeReducesToBool
  | eitherType _ _ => nomatch someTypeReducesToBool

/-- Subject reduction for `Ty.unit`: every `Step` whose source has
type `Ty.unit` produces a target of type `Ty.unit`. -/
theorem Step.preserves_ty_unit
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceIsUnit : sourceType = Ty.unit) :
    targetType = Ty.unit := by
  induction someStep
  all_goals
    first
      | exact sourceIsUnit
      | (subst sourceIsUnit; rfl)
      | rfl
      | exact Ty.subst0_raw_invariance_unit sourceIsUnit

/-- Subject reduction for `Ty.bool`: every `Step` whose source has
type `Ty.bool` produces a target of type `Ty.bool`. -/
theorem Step.preserves_ty_bool
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceIsBool : sourceType = Ty.bool) :
    targetType = Ty.bool := by
  induction someStep
  all_goals
    first
      | exact sourceIsBool
      | (subst sourceIsBool; rfl)
      | rfl
      | exact Ty.subst0_raw_invariance_bool sourceIsBool

/-! ## Lifts to StepStar -/

/-- Subject reduction extended to `StepStar` for `Ty.nat`. -/
theorem StepStar.preserves_ty_nat
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsNat : sourceType = Ty.nat) :
    targetType = Ty.nat := by
  induction chain with
  | refl _ => exact sourceIsNat
  | step head _ tailIH =>
      exact tailIH (Step.preserves_ty_nat head sourceIsNat)

/-- Subject reduction extended to `StepStar` for `Ty.unit`. -/
theorem StepStar.preserves_ty_unit
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsUnit : sourceType = Ty.unit) :
    targetType = Ty.unit := by
  induction chain with
  | refl _ => exact sourceIsUnit
  | step head _ tailIH =>
      exact tailIH (Step.preserves_ty_unit head sourceIsUnit)

/-- Subject reduction extended to `StepStar` for `Ty.bool`. -/
theorem StepStar.preserves_ty_bool
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsBool : sourceType = Ty.bool) :
    targetType = Ty.bool := by
  induction chain with
  | refl _ => exact sourceIsBool
  | step head _ tailIH =>
      exact tailIH (Step.preserves_ty_bool head sourceIsBool)

/-! ## Cong-rule lifters at `Ty.nat`

Subject reduction enables a single-binder cong rule
`StepStar.natSucc_lift`: any `StepStar` between nat-typed terms
lifts to a `StepStar` between their `natSucc`-wrappers.  This
is the workhorse for `Conv.canonical_natSucc`. -/

/-- Generalized lift: any `StepStar` chain whose source/target
are nat-typed lifts to a `StepStar` chain on the `natSucc`-wrappers.
The source/target types are kept as variables to enable induction;
the equalities `srcIsNat`/`tgtIsNat` thread through. -/
theorem StepStar.natSucc_lift_general
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsNat : srcTy = Ty.nat)
    (tgtIsNat : tgtTy = Ty.nat) :
    StepStar (Term.natSucc (srcIsNat ▸ srcTerm))
             (Term.natSucc (tgtIsNat ▸ tgtTerm)) := by
  induction someChain with
  | refl _ =>
      cases srcIsNat
      cases tgtIsNat
      exact StepStar.refl _
  | step head _ tailIH =>
      -- head : Step <chain-source> <chain-middle>; we know chain-source's
      -- type via srcIsNat (it's the outer srcTy = Ty.nat).
      have midIsNat : _ = Ty.nat := Step.preserves_ty_nat head srcIsNat
      cases srcIsNat
      cases midIsNat
      exact StepStar.step (Step.natSuccPred head) (tailIH rfl tgtIsNat)

/-- Lift a `StepStar` chain between nat-typed terms to a
`StepStar` chain between their `natSucc`-wrappers. -/
theorem StepStar.natSucc_lift
    {predRawSource predRawTarget : RawTerm scope}
    {predSource : Term context Ty.nat predRawSource}
    {predTarget : Term context Ty.nat predRawTarget}
    (chain : StepStar predSource predTarget) :
    StepStar (Term.natSucc predSource) (Term.natSucc predTarget) :=
  StepStar.natSucc_lift_general chain rfl rfl

end LeanFX2
