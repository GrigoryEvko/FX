import LeanFX2.Term.StrengtheningImage.RenameImageInterface
import LeanFX2.Term.Inversion
import LeanFX2.Term.PreservesTerm.InlineDestructors

/-! # Term/StrengtheningImage/TargetImageTotality

Target-direction typed image totality.

The shipped renaming-image interface (T1
`strengthenTyped?_rename_eq` and T3
`rename_image_iff_strengthenTyped?_some`) reasons in the
**source direction**: it takes an explicit
`sourceTerm : Term sourceCtx sourceType sourceRaw`,
renames it forward through a typed renaming, and proves
partial strengthening recovers the source.

Block B (`Step.par.preserves_rename_image`, #2022) requires
the *target direction*: given a `Term targetCtx (sourceType.rename rho)
(sourceRaw.rename rho)` that arrived from typed parallel reduction
(`Step.par`) but is not literally a `Term.rename` image, prove
partial strengthening still succeeds.

This file builds the target-direction headline incrementally,
starting with the closed-atomic unit case.  Each per-constructor
theorem here pulls the input term down to its unique
canonical-shape representative via the shipped `Term.<ctor>_unique`
inversion lemma in `Term/Inversion.lean`, then consumes the
dispatcher's definitional reduction at the corresponding arm.
The inversion-then-dispatch pattern avoids the `cases`-on-Term
fragility encountered when the `Term.var` arm is reachable and
`varType` is opaque to the tactic.
-/

namespace LeanFX2

namespace Term

/-- Target-direction totality at `Term.unit`.

Any typed term whose type index is `Ty.unit` and whose raw index
is `RawTerm.unit` strengthens through *every* context strengthening.

The proof routes through `Term.unit_unique` (shipped zero-axiom in
`Term/Inversion.lean`): the inversion lemma yields `HEq targetTerm
Term.unit`, which converts to an `Eq` because both sides share the
same indexed type `Term sourceCtx Ty.unit RawTerm.unit`.  After
substitution, the dispatcher's unit arm reduces by definition to
`some (partialStrengthenTypedUnit strengthening)`. -/
theorem partialStrengthenTyped?_isSome_target_unit
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (targetTerm :
      Term sourceCtx (Ty.unit (level := level) (scope := sourceScope))
        (RawTerm.unit (scope := sourceScope))) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  have heq :
      HEq targetTerm (Term.unit (context := sourceCtx) (level := level)) :=
    Term.unit_unique targetTerm
      (Term.unit (context := sourceCtx) (level := level))
  have targetEq :
      targetTerm = Term.unit (context := sourceCtx) (level := level) :=
    eq_of_heq heq
  subst targetEq
  rfl

/-- Target-direction totality at `Term.boolTrue`.

Mirror of `partialStrengthenTyped?_isSome_target_unit` with
`Term.boolTrue_unique` powering the inversion. -/
theorem partialStrengthenTyped?_isSome_target_boolTrue
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (targetTerm :
      Term sourceCtx (Ty.bool (level := level) (scope := sourceScope))
        (RawTerm.boolTrue (scope := sourceScope))) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  have heq :
      HEq targetTerm
        (Term.boolTrue (context := sourceCtx) (level := level)) :=
    Term.boolTrue_unique targetTerm
      (Term.boolTrue (context := sourceCtx) (level := level))
  have targetEq :
      targetTerm = Term.boolTrue (context := sourceCtx) (level := level) :=
    eq_of_heq heq
  subst targetEq
  rfl

/-- Target-direction totality at `Term.boolFalse`. -/
theorem partialStrengthenTyped?_isSome_target_boolFalse
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (targetTerm :
      Term sourceCtx (Ty.bool (level := level) (scope := sourceScope))
        (RawTerm.boolFalse (scope := sourceScope))) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  have heq :
      HEq targetTerm
        (Term.boolFalse (context := sourceCtx) (level := level)) :=
    Term.boolFalse_unique targetTerm
      (Term.boolFalse (context := sourceCtx) (level := level))
  have targetEq :
      targetTerm = Term.boolFalse (context := sourceCtx) (level := level) :=
    eq_of_heq heq
  subst targetEq
  rfl

/-- Target-direction totality at `Term.natZero`. -/
theorem partialStrengthenTyped?_isSome_target_natZero
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (targetTerm :
      Term sourceCtx (Ty.nat (level := level) (scope := sourceScope))
        (RawTerm.natZero (scope := sourceScope))) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  have heq :
      HEq targetTerm
        (Term.natZero (context := sourceCtx) (level := level)) :=
    Term.natZero_unique targetTerm
      (Term.natZero (context := sourceCtx) (level := level))
  have targetEq :
      targetTerm = Term.natZero (context := sourceCtx) (level := level) :=
    eq_of_heq heq
  subst targetEq
  rfl

/-- Target-direction totality at `Term.interval0`.

Consumes the `Term.interval0_unique` HEq inversion shipped in
`Term/Inversion.lean`. -/
theorem partialStrengthenTyped?_isSome_target_interval0
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (targetTerm :
      Term sourceCtx (Ty.interval (level := level) (scope := sourceScope))
        (RawTerm.interval0 (scope := sourceScope))) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  have heq :
      HEq targetTerm
        (Term.interval0 (context := sourceCtx) (level := level)) :=
    Term.interval0_unique targetTerm
      (Term.interval0 (context := sourceCtx) (level := level))
  have targetEq :
      targetTerm = Term.interval0 (context := sourceCtx) (level := level) :=
    eq_of_heq heq
  subst targetEq
  rfl

/-- Target-direction totality at `Term.interval1`. -/
theorem partialStrengthenTyped?_isSome_target_interval1
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (targetTerm :
      Term sourceCtx (Ty.interval (level := level) (scope := sourceScope))
        (RawTerm.interval1 (scope := sourceScope))) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  have heq :
      HEq targetTerm
        (Term.interval1 (context := sourceCtx) (level := level)) :=
    Term.interval1_unique targetTerm
      (Term.interval1 (context := sourceCtx) (level := level))
  have targetEq :
      targetTerm = Term.interval1 (context := sourceCtx) (level := level) :=
    eq_of_heq heq
  subst targetEq
  rfl

/-! ## Compound ctor: natSucc

The first compound (single-recursive) constructor in the target-
direction cascade.  Unlike closed-atomic ctors, `Term.natSucc`
carries a predecessor `Term sourceCtx Ty.nat predRaw` and the
dispatcher recursively strengthens the predecessor.  The proof
takes the predecessor's totality as an inductive hypothesis and
recovers the predecessor via `Term.natSuccDestruct`.

The dispatcher's natSucc arm cannot reduce definitionally to its
match-equation form (the `match X : ... with` colon-binding syntax
prevents kernel-level iota reduction on the outer recursive call).
We unfold the arm via `dsimp only [partialStrengthenTyped?]` —
unfolding `partialStrengthenTyped?` at a known constructor `Term.natSucc`
picks the corresponding arm at constant cost (no 78-case sweep,
since the head constructor is concrete).  The subsequent `split`
case-analyses the recursive call.  This mirrors the established
source-direction pattern at
`RenameImageUnary.lean`'s `strengthenTyped?_rename_isSome_natSucc_of_childIsSome`. -/
/-- Target-direction totality at `Term.natSucc`.

Takes the predecessor's totality (`predIH`) as an inductive
hypothesis, recovers the predecessor via `Term.natSuccDestruct`,
substitutes, then case-splits on the recursive call's outcome.
The `none` branch is discharged by absurdity against `predIH`;
the `some` branch closes by definitional reduction. -/
theorem partialStrengthenTyped?_isSome_target_natSucc
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {predRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.nat (level := level) (scope := sourceScope))
        (RawTerm.natSucc predRaw))
    (predIH :
      ∀ (predTerm :
            Term sourceCtx (Ty.nat (level := level) (scope := sourceScope))
              predRaw),
        (partialStrengthenTyped? predTerm strengthening).isSome = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨predTerm, heq⟩ := Term.natSuccDestruct targetTerm
  have targetEq : targetTerm = Term.natSucc predTerm := eq_of_heq heq
  subst targetEq
  have ihResult := predIH predTerm
  dsimp only [partialStrengthenTyped?]
  split
  next noPredSuccess =>
      rw [noPredSuccess] at ihResult
      cases ihResult
  next _ _ =>
      rfl

/-! ## Compound ctor: optionSome

Same single-recursive shape as `natSucc`.  `Term.optionSome` carries
a `valueTerm : Term sourceCtx elementType valueRaw`.  The dispatcher
recursively strengthens `valueTerm`; no type-level side condition
on `elementType` (recovered post-hoc from `valueResult.targetType`).
Proof mirrors `partialStrengthenTyped?_isSome_target_natSucc` via
`Term.optionSomeDestruct`. -/
/-- Target-direction totality at `Term.optionSome`. -/
theorem partialStrengthenTyped?_isSome_target_optionSome
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {valueRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.optionType elementType)
        (RawTerm.optionSome valueRaw))
    (valueIH :
      ∀ (valueTerm : Term sourceCtx elementType valueRaw),
        (partialStrengthenTyped? valueTerm strengthening).isSome = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨valueTerm, heq⟩ := Term.optionSomeDestruct targetTerm
  have targetEq : targetTerm = Term.optionSome valueTerm := eq_of_heq heq
  subst targetEq
  have ihResult := valueIH valueTerm
  dsimp only [partialStrengthenTyped?]
  split
  next noValueSuccess =>
      rw [noValueSuccess] at ihResult
      cases ihResult
  next _ _ =>
      rfl

/-! ## Compound ctors with type-side condition: eitherInl, eitherInr

`Term.eitherInl` carries a payload `valueTerm : Term sourceCtx
leftType valueRaw` and a phantom `rightType` index.  The dispatcher
must first strengthen the phantom side's `Ty` (here `rightType`)
since it appears in the reconstructed `Ty.eitherType` of the
`StrengtheningResult.targetType`.

For target-direction usage in the universal headline, the
phantom-side `Ty.partialStrengthen?` hypothesis is satisfied
automatically when target = source.rename rho (cf. existing
`Ty.partialStrengthen?_rename_some` in the source-direction
pipeline).  We expose the hypothesis here as a precondition;
the universal-headline driver discharges it from the
renaming-image assumption. -/
/-- Target-direction totality at `Term.eitherInl`. -/
theorem partialStrengthenTyped?_isSome_target_eitherInl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {valueRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.eitherType leftType rightType)
        (RawTerm.eitherInl valueRaw))
    (rightStrengthens :
      (rightType.partialStrengthen? strengthening.back).isSome = true)
    (valueIH :
      ∀ (valueTerm : Term sourceCtx leftType valueRaw),
        (partialStrengthenTyped? valueTerm strengthening).isSome = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨valueTerm, heq⟩ := Term.eitherInlDestruct targetTerm
  have targetEq :
      targetTerm = Term.eitherInl (rightType := rightType) valueTerm :=
    eq_of_heq heq
  subst targetEq
  have ihResult := valueIH valueTerm
  dsimp only [partialStrengthenTyped?]
  split
  next noRightSuccess =>
      rw [noRightSuccess] at rightStrengthens
      cases rightStrengthens
  next _ _ =>
      split
      next noValueSuccess =>
          rw [noValueSuccess] at ihResult
          cases ihResult
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.eitherInr`. -/
theorem partialStrengthenTyped?_isSome_target_eitherInr
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {valueRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.eitherType leftType rightType)
        (RawTerm.eitherInr valueRaw))
    (leftStrengthens :
      (leftType.partialStrengthen? strengthening.back).isSome = true)
    (valueIH :
      ∀ (valueTerm : Term sourceCtx rightType valueRaw),
        (partialStrengthenTyped? valueTerm strengthening).isSome = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨valueTerm, heq⟩ := Term.eitherInrDestruct targetTerm
  have targetEq :
      targetTerm = Term.eitherInr (leftType := leftType) valueTerm :=
    eq_of_heq heq
  subst targetEq
  have ihResult := valueIH valueTerm
  dsimp only [partialStrengthenTyped?]
  split
  next noLeftSuccess =>
      rw [noLeftSuccess] at leftStrengthens
      cases leftStrengthens
  next _ _ =>
      split
      next noValueSuccess =>
          rw [noValueSuccess] at ihResult
          cases ihResult
      next _ _ =>
          rfl

/-! ## Binary-recursive ctor: listCons

First binary (two-recursive) ctor in the target-direction cascade.
`Term.listCons` carries `headTerm` and `tailTerm`.  Dispatcher
recursively strengthens both with no type-level side condition.
Two IH hypotheses; two nested `split`s. -/
/-- Target-direction totality at `Term.listCons`. -/
theorem partialStrengthenTyped?_isSome_target_listCons
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {headRaw tailRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.listType elementType)
        (RawTerm.listCons headRaw tailRaw))
    (headIH :
      ∀ (headTerm : Term sourceCtx elementType headRaw),
        (partialStrengthenTyped? headTerm strengthening).isSome = true)
    (tailIH :
      ∀ (tailTerm :
            Term sourceCtx (Ty.listType elementType) tailRaw),
        (partialStrengthenTyped? tailTerm strengthening).isSome = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨headTerm, tailTerm, heq⟩ := Term.listConsDestruct targetTerm
  have targetEq : targetTerm = Term.listCons headTerm tailTerm :=
    eq_of_heq heq
  subst targetEq
  have headResult := headIH headTerm
  have tailResult := tailIH tailTerm
  dsimp only [partialStrengthenTyped?]
  split
  next noHeadSuccess =>
      rw [noHeadSuccess] at headResult
      cases headResult
  next _ _ =>
      split
      next noTailSuccess =>
          rw [noTailSuccess] at tailResult
          cases tailResult
      next _ _ =>
          rfl

/-! ## Binary-recursive ctor with dependent-type side condition: pair

`Term.pair` carries `firstValue : Term sourceCtx firstType firstRaw`
and `secondValue : Term sourceCtx (secondType.subst0 firstType
firstRaw) secondRaw`, where `secondType : Ty level (sourceScope + 1)`
lives under a binder.  The dispatcher's first action is to strengthen
`secondType` via `strengthening.back.lift` (lifting the partial
inverse across the binder), then two recursive calls.

This pattern combines the dependent-type side condition (cf. eitherInl)
with the binary recursion (cf. listCons).  The hypothesis name carries
`Lifted` to flag that the partial inverse is lifted across the binder. -/
/-- Target-direction totality at `Term.pair`. -/
theorem partialStrengthenTyped?_isSome_target_pair
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {firstRaw secondRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.sigmaTy firstType secondType)
        (RawTerm.pair firstRaw secondRaw))
    (secondTypeLiftedStrengthens :
      (secondType.partialStrengthen? strengthening.back.lift).isSome
        = true)
    (firstIH :
      ∀ (firstValue : Term sourceCtx firstType firstRaw),
        (partialStrengthenTyped? firstValue strengthening).isSome = true)
    (secondIH :
      ∀ (secondValue :
            Term sourceCtx
              (secondType.subst0 firstType firstRaw) secondRaw),
        (partialStrengthenTyped? secondValue strengthening).isSome
          = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨firstValue, secondValue, heq⟩ := Term.pairDestruct targetTerm
  have targetEq : targetTerm = Term.pair firstValue secondValue :=
    eq_of_heq heq
  subst targetEq
  have firstResult := firstIH firstValue
  have secondResult := secondIH secondValue
  dsimp only [partialStrengthenTyped?]
  split
  next noSecondTypeSuccess =>
      rw [noSecondTypeSuccess] at secondTypeLiftedStrengthens
      cases secondTypeLiftedStrengthens
  next _ _ =>
      split
      next noFirstSuccess =>
          rw [noFirstSuccess] at firstResult
          cases firstResult
      next _ _ =>
          split
          next noSecondSuccess =>
              rw [noSecondSuccess] at secondResult
              cases secondResult
          next _ _ =>
              rfl

/-! ## Type-preserving modal ctors: modIntro, modElim, subsume

These three ctors are type-preserving in the Layer-0 kernel
(Layer 6 may extend modIntro/subsume with mode-shifting variants;
see CLAUDE.md "forward-compat with mode-changing modal ctors").
Current dispatcher arm:

```
| @Term.modIntro _ _ _ _ _ _ innerTerm =>
    match partialStrengthenTyped? innerTerm strengthening with
    | none => none
    | some innerResult => some (partialStrengthenTypedModIntro innerResult)
```

Same single-recursive shape as `natSucc`, no type-level side
condition.  Three destructors live in
`Term/{Inversion,PreservesTerm/InlineDestructors}.lean`. -/
/-- Target-direction totality at `Term.modIntro`. -/
theorem partialStrengthenTyped?_isSome_target_modIntro
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {innerRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx innerType (RawTerm.modIntro innerRaw))
    (innerIH :
      ∀ (innerTerm : Term sourceCtx innerType innerRaw),
        (partialStrengthenTyped? innerTerm strengthening).isSome = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨innerTerm, heq⟩ := Term.modIntroDestruct targetTerm
  have targetEq : targetTerm = Term.modIntro innerTerm := eq_of_heq heq
  subst targetEq
  have ihResult := innerIH innerTerm
  dsimp only [partialStrengthenTyped?]
  split
  next noInnerSuccess =>
      rw [noInnerSuccess] at ihResult
      cases ihResult
  next _ _ =>
      rfl

/-- Target-direction totality at `Term.modElim`. -/
theorem partialStrengthenTyped?_isSome_target_modElim
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {innerRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx innerType (RawTerm.modElim innerRaw))
    (innerIH :
      ∀ (innerTerm : Term sourceCtx innerType innerRaw),
        (partialStrengthenTyped? innerTerm strengthening).isSome = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨innerTerm, heq⟩ := Term.modElimDestruct targetTerm
  have targetEq : targetTerm = Term.modElim innerTerm := eq_of_heq heq
  subst targetEq
  have ihResult := innerIH innerTerm
  dsimp only [partialStrengthenTyped?]
  split
  next noInnerSuccess =>
      rw [noInnerSuccess] at ihResult
      cases ihResult
  next _ _ =>
      rfl

/-- Target-direction totality at `Term.subsume`. -/
theorem partialStrengthenTyped?_isSome_target_subsume
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {innerRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx innerType (RawTerm.subsume innerRaw))
    (innerIH :
      ∀ (innerTerm : Term sourceCtx innerType innerRaw),
        (partialStrengthenTyped? innerTerm strengthening).isSome = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨innerTerm, heq⟩ := Term.subsumeDestruct targetTerm
  have targetEq : targetTerm = Term.subsume innerTerm := eq_of_heq heq
  subst targetEq
  have ihResult := innerIH innerTerm
  dsimp only [partialStrengthenTyped?]
  split
  next noInnerSuccess =>
      rw [noInnerSuccess] at ihResult
      cases ihResult
  next _ _ =>
      rfl

/-! ## Single-recursive ctor with type-wrapping: recordIntro

`Term.recordIntro` wraps `firstField : Term sourceCtx
singleFieldType firstRaw` in `Ty.record singleFieldType`.  Same
single-recursive shape as `optionSome` — no type-level side
condition.  Uses `Term.recordIntroDestruct` from
`Term/PreservesTerm/InlineDestructors.lean`. -/
/-- Target-direction totality at `Term.recordIntro`. -/
theorem partialStrengthenTyped?_isSome_target_recordIntro
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {firstRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.record singleFieldType)
        (RawTerm.recordIntro firstRaw))
    (fieldIH :
      ∀ (firstField : Term sourceCtx singleFieldType firstRaw),
        (partialStrengthenTyped? firstField strengthening).isSome
          = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨firstField, heq⟩ := Term.recordIntroDestruct targetTerm
  have targetEq : targetTerm = Term.recordIntro firstField := eq_of_heq heq
  subst targetEq
  have ihResult := fieldIH firstField
  dsimp only [partialStrengthenTyped?]
  split
  next noFieldSuccess =>
      rw [noFieldSuccess] at ihResult
      cases ihResult
  next _ _ =>
      rfl

/-! ## Binary-recursive with binder-side predicate: refineIntro

`Term.refineIntro` wraps `baseValue : Term context baseType
valueRaw` together with `predicateProof : Term context Ty.unit
proofRaw` to inhabit `Ty.refine baseType predicate`.  The
predicate is a `RawTerm (scope + 1)` (binder under refinement
variable), so the dispatcher's side condition uses
`strengthening.back.lift`.  Same triple-split shape as `pair`
but with a single base IH and a proof IH instead of dual data
IHs.  Uses `Term.refineIntroDestruct` from
`Term/PreservesTerm/InlineDestructors.lean`. -/
/-- Target-direction totality at `Term.refineIntro`. -/
theorem partialStrengthenTyped?_isSome_target_refineIntro
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    (predicate : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {valueRaw proofRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.refine baseType predicate)
        (RawTerm.refineIntro valueRaw proofRaw))
    (predicateLiftedStrengthens :
      (predicate.partialStrengthen? strengthening.back.lift).isSome
        = true)
    (baseIH :
      ∀ (baseValue : Term sourceCtx baseType valueRaw),
        (partialStrengthenTyped? baseValue strengthening).isSome = true)
    (proofIH :
      ∀ (predicateProof : Term sourceCtx Ty.unit proofRaw),
        (partialStrengthenTyped? predicateProof strengthening).isSome
          = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨baseValue, predicateProof, heq⟩ :=
    Term.refineIntroDestruct predicate targetTerm
  have targetEq :
      targetTerm = Term.refineIntro predicate baseValue predicateProof :=
    eq_of_heq heq
  subst targetEq
  have baseResult := baseIH baseValue
  have proofResult := proofIH predicateProof
  dsimp only [partialStrengthenTyped?]
  split
  next noPredicateSuccess =>
      rw [noPredicateSuccess] at predicateLiftedStrengthens
      cases predicateLiftedStrengthens
  next _ _ =>
      split
      next noBaseSuccess =>
          rw [noBaseSuccess] at baseResult
          cases baseResult
      next _ _ =>
          split
          next noProofSuccess =>
              rw [noProofSuccess] at proofResult
              cases proofResult
          next _ _ =>
              rfl

/-! ## Binary-recursive with two non-binder type sides: glueIntro

`Term.glueIntro` introduces a `Ty.glue baseType boundaryWitness`
value via a base part + partial part, gated by
`modeIsUnivalent : mode = Mode.univalent`.  Dispatcher arm
quadruple-splits over: baseType strengthening (back, non-binder),
boundaryWitness strengthening (back, non-binder), baseValue IH,
partialValue IH.  Mode hypothesis is forwarded to the destructor;
all four splits use plain `strengthening.back` (no `.lift`).

Uses `Term.glueIntroDestruct` from
`Term/PreservesTerm/InlineDestructors.lean`. -/
/-- Target-direction totality at `Term.glueIntro`. -/
theorem partialStrengthenTyped?_isSome_target_glueIntro
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {baseRaw partialRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.glue baseType boundaryWitness)
        (RawTerm.glueIntro baseRaw partialRaw))
    (baseTypeStrengthens :
      (baseType.partialStrengthen? strengthening.back).isSome = true)
    (boundaryStrengthens :
      (boundaryWitness.partialStrengthen? strengthening.back).isSome
        = true)
    (baseIH :
      ∀ (baseValue : Term sourceCtx baseType baseRaw),
        (partialStrengthenTyped? baseValue strengthening).isSome = true)
    (partialIH :
      ∀ (partialValue : Term sourceCtx baseType partialRaw),
        (partialStrengthenTyped? partialValue strengthening).isSome
          = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨baseValue, partialValue, heq⟩ :=
    Term.glueIntroDestruct modeIsUnivalent baseType boundaryWitness
      targetTerm
  have targetEq :
      targetTerm =
        Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue :=
    eq_of_heq heq
  subst targetEq
  have baseResult := baseIH baseValue
  have partialResult := partialIH partialValue
  dsimp only [partialStrengthenTyped?]
  split
  next noBaseType =>
      rw [noBaseType] at baseTypeStrengthens
      cases baseTypeStrengthens
  next _ _ =>
      split
      next noBoundary =>
          rw [noBoundary] at boundaryStrengthens
          cases boundaryStrengthens
      next _ _ =>
          split
          next noBase =>
              rw [noBase] at baseResult
              cases baseResult
          next _ _ =>
              split
              next noPartial =>
                  rw [noPartial] at partialResult
                  cases partialResult
              next _ _ =>
                  rfl

/-! ## Binary-recursive with single non-binder type side: codataUnfold

`Term.codataUnfold initialState transition` constructs a
`Ty.codata stateType outputType` value from an initial state and
a transition function `stateType -> outputType`.  Dispatcher arm
triple-splits over: outputType strengthening (back, non-binder),
initialState IH, transition IH.

Note: the dispatcher's outputType check uses
`strengthening.back` (NOT `.back.lift`) — codata outputs at the
same scope as the state, not under a binder.

Pattern category: binary-recursive with single non-binder type
side.  Triple-split.  Same shape as glueIntro minus the
boundary-witness side and the modeIsUnivalent hypothesis.

Uses `Term.codataUnfoldDestruct` from
`Term/PreservesTerm/InlineDestructors.lean`. -/
/-- Target-direction totality at `Term.codataUnfold`. -/
theorem partialStrengthenTyped?_isSome_target_codataUnfold
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {stateRaw transitionRaw : RawTerm sourceScope}
    (targetTerm :
      Term sourceCtx (Ty.codata stateType outputType)
        (RawTerm.codataUnfold stateRaw transitionRaw))
    (outputStrengthens :
      (outputType.partialStrengthen? strengthening.back).isSome = true)
    (stateIH :
      ∀ (initialState : Term sourceCtx stateType stateRaw),
        (partialStrengthenTyped? initialState strengthening).isSome
          = true)
    (transitionIH :
      ∀ (transition :
            Term sourceCtx (Ty.arrow stateType outputType) transitionRaw),
        (partialStrengthenTyped? transition strengthening).isSome
          = true) :
    (partialStrengthenTyped? targetTerm strengthening).isSome = true := by
  obtain ⟨initialState, transition, heq⟩ :=
    Term.codataUnfoldDestruct targetTerm
  have targetEq :
      targetTerm = Term.codataUnfold initialState transition :=
    eq_of_heq heq
  subst targetEq
  have stateResult := stateIH initialState
  have transitionResult := transitionIH transition
  dsimp only [partialStrengthenTyped?]
  split
  next noOutput =>
      rw [noOutput] at outputStrengthens
      cases outputStrengthens
  next _ _ =>
      split
      next noState =>
          rw [noState] at stateResult
          cases stateResult
      next _ _ =>
          split
          next noTransition =>
              rw [noTransition] at transitionResult
              cases transitionResult
          next _ _ =>
              rfl

/-! ## Sigma projections with existential secondType: fst, snd

`Term.fst pairTerm` and `Term.snd pairTerm` project from a
dependent sigma `Ty.sigmaTy firstType secondType` at `pairRaw`.
Because `secondType` is existential at the projected term's type
index (fst's output is `firstType` alone; snd's output is
`secondType.subst0 firstType ...`, dependent on the hidden fst),
the wrapper departs from the destructor-with-HEq pattern: it
takes pairTerm directly.  The universal driver knows secondType
from its case match on `Term.fst pairTerm` / `Term.snd pairTerm`
and passes pairTerm in concretely.

Both ctors triple-split over: firstType strengthening (back),
secondType strengthening (back.lift, binder-side), pairTerm IH. -/
/-- Target-direction totality at `Term.fst`. -/
theorem partialStrengthenTyped?_isSome_target_fst
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pairTerm :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (firstStrengthens :
      (firstType.partialStrengthen? strengthening.back).isSome = true)
    (secondLiftedStrengthens :
      (secondType.partialStrengthen? strengthening.back.lift).isSome
        = true)
    (pairIH :
      (partialStrengthenTyped? pairTerm strengthening).isSome = true) :
    (partialStrengthenTyped? (Term.fst pairTerm) strengthening).isSome
      = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noFirst =>
      rw [noFirst] at firstStrengthens
      cases firstStrengthens
  next _ _ =>
      split
      next noSecond =>
          rw [noSecond] at secondLiftedStrengthens
          cases secondLiftedStrengthens
      next _ _ =>
          split
          next noPair =>
              rw [noPair] at pairIH
              cases pairIH
          next _ _ =>
              rfl

/-- Target-direction totality at `Term.snd`. -/
theorem partialStrengthenTyped?_isSome_target_snd
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pairTerm :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (firstStrengthens :
      (firstType.partialStrengthen? strengthening.back).isSome = true)
    (secondLiftedStrengthens :
      (secondType.partialStrengthen? strengthening.back.lift).isSome
        = true)
    (pairIH :
      (partialStrengthenTyped? pairTerm strengthening).isSome = true) :
    (partialStrengthenTyped? (Term.snd pairTerm) strengthening).isSome
      = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noFirst =>
      rw [noFirst] at firstStrengthens
      cases firstStrengthens
  next _ _ =>
      split
      next noSecond =>
          rw [noSecond] at secondLiftedStrengthens
          cases secondLiftedStrengthens
      next _ _ =>
          split
          next noPair =>
              rw [noPair] at pairIH
              cases pairIH
          next _ _ =>
              rfl

/-! ## Eliminator projections: recordProj, refineElim

`Term.recordProj recordValue` projects the single field of a
record value, returning at `singleFieldType`.  `Term.refineElim
refinedValue` extracts the base value from a refinement.  Both
take pre-destructured subterm inputs (same shape as fst/snd) —
the subterm's raw form is existential at the output's index.

recordProj double-splits: singleFieldType strengthening (back)
+ recordValue IH.  refineElim triple-splits: baseType (back) +
predicate (back.lift, binder-side) + refinedValue IH. -/
/-- Target-direction totality at `Term.recordProj`. -/
theorem partialStrengthenTyped?_isSome_target_recordProj
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (recordValue :
      Term sourceCtx (Ty.record singleFieldType) recordRaw)
    (fieldStrengthens :
      (singleFieldType.partialStrengthen? strengthening.back).isSome
        = true)
    (recordIH :
      (partialStrengthenTyped? recordValue strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.recordProj recordValue)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noField =>
      rw [noField] at fieldStrengthens
      cases fieldStrengthens
  next _ _ =>
      split
      next noRecord =>
          rw [noRecord] at recordIH
          cases recordIH
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.refineElim`. -/
theorem partialStrengthenTyped?_isSome_target_refineElim
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw)
    (baseStrengthens :
      (baseType.partialStrengthen? strengthening.back).isSome = true)
    (predicateLiftedStrengthens :
      (predicate.partialStrengthen? strengthening.back.lift).isSome
        = true)
    (refinedIH :
      (partialStrengthenTyped? refinedValue strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.refineElim refinedValue)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noBase =>
      rw [noBase] at baseStrengthens
      cases baseStrengthens
  next _ _ =>
      split
      next noPredicate =>
          rw [noPredicate] at predicateLiftedStrengthens
          cases predicateLiftedStrengthens
      next _ _ =>
          split
          next noRefined =>
              rw [noRefined] at refinedIH
              cases refinedIH
          next _ _ =>
              rfl

end Term

end LeanFX2
