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

/-! ## Function application family: app, appPi, codataDest

These three ctors share the "pre-destructured binary recursion"
shape: two operand IHs + 1-2 non-binder type sides (or 1
non-binder + 1 binder-side for appPi).  All have existential raw
forms in their subterms, so the wrapper takes the subterms
directly.

* `app`: 4-split (domainType + codomainType non-binder
  + functionTerm IH + argumentTerm IH).
* `appPi`: 4-split (domainType + codomainType binder-side
  + functionTerm IH + argumentTerm IH).
* `codataDest`: 3-split (stateType + outputType non-binder
  + codataValue IH). -/
/-- Target-direction totality at `Term.app`. -/
theorem partialStrengthenTyped?_isSome_target_app
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (domainStrengthens :
      (domainType.partialStrengthen? strengthening.back).isSome = true)
    (codomainStrengthens :
      (codomainType.partialStrengthen? strengthening.back).isSome
        = true)
    (functionIH :
      (partialStrengthenTyped? functionTerm strengthening).isSome
        = true)
    (argumentIH :
      (partialStrengthenTyped? argumentTerm strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.app functionTerm argumentTerm)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noDomain =>
      rw [noDomain] at domainStrengthens
      cases domainStrengthens
  next _ _ =>
      split
      next noCodomain =>
          rw [noCodomain] at codomainStrengthens
          cases codomainStrengthens
      next _ _ =>
          split
          next noFunction =>
              rw [noFunction] at functionIH
              cases functionIH
          next _ _ =>
              split
              next noArgument =>
                  rw [noArgument] at argumentIH
                  cases argumentIH
              next _ _ =>
                  rfl

/-- Target-direction totality at `Term.appPi` (dependent Π
application).  Same 4-split shape as app but `codomainType`
lives at scope+1. -/
theorem partialStrengthenTyped?_isSome_target_appPi
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (domainStrengthens :
      (domainType.partialStrengthen? strengthening.back).isSome = true)
    (codomainLiftedStrengthens :
      (codomainType.partialStrengthen? strengthening.back.lift).isSome
        = true)
    (functionIH :
      (partialStrengthenTyped? functionTerm strengthening).isSome
        = true)
    (argumentIH :
      (partialStrengthenTyped? argumentTerm strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.appPi functionTerm argumentTerm)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noDomain =>
      rw [noDomain] at domainStrengthens
      cases domainStrengthens
  next _ _ =>
      split
      next noCodomain =>
          rw [noCodomain] at codomainLiftedStrengthens
          cases codomainLiftedStrengthens
      next _ _ =>
          split
          next noFunction =>
              rw [noFunction] at functionIH
              cases functionIH
          next _ _ =>
              split
              next noArgument =>
                  rw [noArgument] at argumentIH
                  cases argumentIH
              next _ _ =>
                  rfl

/-- Target-direction totality at `Term.codataDest`. -/
theorem partialStrengthenTyped?_isSome_target_codataDest
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw)
    (stateStrengthens :
      (stateType.partialStrengthen? strengthening.back).isSome = true)
    (outputStrengthens :
      (outputType.partialStrengthen? strengthening.back).isSome = true)
    (codataIH :
      (partialStrengthenTyped? codataValue strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.codataDest codataValue)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noState =>
      rw [noState] at stateStrengthens
      cases stateStrengthens
  next _ _ =>
      split
      next noOutput =>
          rw [noOutput] at outputStrengthens
          cases outputStrengthens
      next _ _ =>
          split
          next noCodata =>
              rw [noCodata] at codataIH
              cases codataIH
          next _ _ =>
              rfl

/-! ## Interval algebra family: intervalOpp, intervalMeet, intervalJoin

The three interval-algebra ctors all carry operand `Term`s at
the closed type `Ty.interval` and produce a result at the same
closed type.  No type-side condition is required — the dispatcher
recurses directly on operands.  All three use the pre-destructured
pattern (no HEq destructors needed; the universal driver supplies
the operands from its own case match). -/
/-- Target-direction totality at `Term.intervalOpp` (unary
interval operation).  Single-recursive: same shape as `natSucc`
but pre-destructured (no `Term.intervalOppDestruct` needed). -/
theorem partialStrengthenTyped?_isSome_target_intervalOpp
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerValue :
      Term sourceCtx (Ty.interval (level := level)
        (scope := sourceScope)) innerRaw)
    (innerIH :
      (partialStrengthenTyped? innerValue strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.intervalOpp innerValue)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noInner =>
      rw [noInner] at innerIH
      cases innerIH
  next _ _ =>
      rfl

/-- Target-direction totality at `Term.intervalMeet`.  Binary
recursion on two operands, no type-side. -/
theorem partialStrengthenTyped?_isSome_target_intervalMeet
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (leftValue :
      Term sourceCtx (Ty.interval (level := level)
        (scope := sourceScope)) leftRaw)
    (rightValue :
      Term sourceCtx (Ty.interval (level := level)
        (scope := sourceScope)) rightRaw)
    (leftIH :
      (partialStrengthenTyped? leftValue strengthening).isSome
        = true)
    (rightIH :
      (partialStrengthenTyped? rightValue strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.intervalMeet leftValue rightValue)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noLeft =>
      rw [noLeft] at leftIH
      cases leftIH
  next _ _ =>
      split
      next noRight =>
          rw [noRight] at rightIH
          cases rightIH
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.intervalJoin`.  Same
shape as `intervalMeet`. -/
theorem partialStrengthenTyped?_isSome_target_intervalJoin
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (leftValue :
      Term sourceCtx (Ty.interval (level := level)
        (scope := sourceScope)) leftRaw)
    (rightValue :
      Term sourceCtx (Ty.interval (level := level)
        (scope := sourceScope)) rightRaw)
    (leftIH :
      (partialStrengthenTyped? leftValue strengthening).isSome
        = true)
    (rightIH :
      (partialStrengthenTyped? rightValue strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.intervalJoin leftValue rightValue)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noLeft =>
      rw [noLeft] at leftIH
      cases leftIH
  next _ _ =>
      split
      next noRight =>
          rw [noRight] at rightIH
          cases rightIH
      next _ _ =>
          rfl

/-! ## Universe-code family: universeCode

`Term.universeCode` is "closed-atomic-with-attributes": it
carries no recursive operand — only attribute parameters
(`innerLevel`, `outerLevel`, `cumulOk`, `levelLe`).  The
dispatcher returns `some` directly with no recursion.  Same
shape as `interval0`/`unit` (closed-atomic) except via the
pre-destructured pattern (no HEq destructor needed). -/
/-- Target-direction totality at `Term.universeCode`. -/
theorem partialStrengthenTyped?_isSome_target_universeCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    (partialStrengthenTyped?
        (Term.universeCode (context := sourceCtx)
          innerLevel outerLevel cumulOk levelLe)
        strengthening).isSome = true := by
  rfl

/-! ## Identity-type introducers: refl, oeqRefl

`Term.refl` and `Term.oeqRefl` carry no operand `Term`s — only
explicit `(carrier : Ty)` + `(rawWitness : RawTerm)` data.  The
dispatcher takes both as carrier + raw sides, returning `some`
directly without recursion.  Pre-destructured (no HEq destructor
needed); two side strengthenings drive a double-split. -/
/-- Target-direction totality at `Term.refl` (HoTT/observational
identity introduction).  No operand IH; double-split over
`carrier` Ty-side and `rawWitness` raw-side. -/
theorem partialStrengthenTyped?_isSome_target_refl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (carrier : Ty level sourceScope)
    (rawWitness : RawTerm sourceScope)
    (carrierStrengthens :
      (carrier.partialStrengthen? strengthening.back).isSome = true)
    (witnessStrengthens :
      (rawWitness.partialStrengthen? strengthening.back).isSome = true) :
    (partialStrengthenTyped?
        (Term.refl (context := sourceCtx) carrier rawWitness)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noCarrier =>
      rw [noCarrier] at carrierStrengthens
      cases carrierStrengthens
  next _ _ =>
      split
      next noWitness =>
          rw [noWitness] at witnessStrengthens
          cases witnessStrengthens
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.oeqRefl` (observational
equality reflexivity).  Same shape as `refl`. -/
theorem partialStrengthenTyped?_isSome_target_oeqRefl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (carrier : Ty level sourceScope)
    (rawWitness : RawTerm sourceScope)
    (carrierStrengthens :
      (carrier.partialStrengthen? strengthening.back).isSome = true)
    (witnessStrengthens :
      (rawWitness.partialStrengthen? strengthening.back).isSome = true) :
    (partialStrengthenTyped?
        (Term.oeqRefl (context := sourceCtx) carrier rawWitness)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noCarrier =>
      rw [noCarrier] at carrierStrengthens
      cases carrierStrengthens
  next _ _ =>
      split
      next noWitness =>
          rw [noWitness] at witnessStrengthens
          cases witnessStrengthens
      next _ _ =>
          rfl

/-! ## Session communication primitives: sessionRecv, sessionSend

`Term.sessionRecv` reads from a session channel; `Term.sessionSend`
writes to it.  Both take a `channel : Term context
(Ty.session protocolStep) channelRaw`; sessionSend additionally
takes a `payload : Term context payloadType payloadRaw`.

The dispatcher arm for sessionSend takes `protocolStep` as an
explicit `RawTerm scope` argument (NOT implicit) so it appears
directly in the wrapper signature.  Both ctors require raw
strengthening of `protocolStep` (the session protocol step);
sessionSend additionally requires payloadType strengthening. -/
/-- Target-direction totality at `Term.sessionRecv`.  Single-
recursive on the channel operand + one raw-side strengthening on
`protocolStep`. -/
theorem partialStrengthenTyped?_isSome_target_sessionRecv
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep channelRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (protocolStrengthens :
      (protocolStep.partialStrengthen? strengthening.back).isSome = true)
    (channelIH :
      (partialStrengthenTyped? channel strengthening).isSome = true) :
    (partialStrengthenTyped?
        (Term.sessionRecv channel) strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noProtocol =>
      rw [noProtocol] at protocolStrengthens
      cases protocolStrengthens
  next _ _ =>
      split
      next noChannel =>
          rw [noChannel] at channelIH
          cases channelIH
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.sessionSend`.  Binary-
recursive (channel + payload).  Dispatcher arm splits over
`protocolStep` raw strengthening + channel IH + payload IH. -/
theorem partialStrengthenTyped?_isSome_target_sessionSend
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (protocolStep : RawTerm sourceScope)
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (payload : Term sourceCtx payloadType payloadRaw)
    (protocolStrengthens :
      (protocolStep.partialStrengthen? strengthening.back).isSome = true)
    (channelIH :
      (partialStrengthenTyped? channel strengthening).isSome = true)
    (payloadIH :
      (partialStrengthenTyped? payload strengthening).isSome = true) :
    (partialStrengthenTyped?
        (Term.sessionSend protocolStep channel payload) strengthening).isSome
      = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noProtocol =>
      rw [noProtocol] at protocolStrengthens
      cases protocolStrengthens
  next _ _ =>
      split
      next noChannel =>
          rw [noChannel] at channelIH
          cases channelIH
      next _ _ =>
          split
          next noPayload =>
              rw [noPayload] at payloadIH
              cases payloadIH
          next _ _ =>
              rfl

/-! ## Universe cumulativity: cumulUp

`Term.cumulUp` lifts a `typeCode : Term ctx (Ty.universe
lowerLevel _) codeRaw` to `Term ctx (Ty.universe higherLevel _)`
via cumulativity.  No type-side, no raw-side — only the typeCode
operand IH (the level attributes are erased once the typeCode IH
fires).  Single-recursive, attribute-heavy shape. -/
/-- Target-direction totality at `Term.cumulUp`. -/
theorem partialStrengthenTyped?_isSome_target_cumulUp
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {codeRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    (typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (codeIH :
      (partialStrengthenTyped? typeCode strengthening).isSome = true) :
    (partialStrengthenTyped?
        (Term.cumulUp lowerLevel higherLevel cumulMonotone
          levelLeLow levelLeHigh typeCode) strengthening).isSome
      = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noCode =>
      rw [noCode] at codeIH
      cases codeIH
  next _ _ =>
      rfl

/-! ## Equivalence- and funext-reflexivity family

Five ctors construct reflexivity witnesses for equivalence and
funext types.  None take operand `Term`s — only attribute params
(Ty + RawTerm), so wrappers are closed-atomic-with-sides shape.

* `equivReflId` — single Ty-side (`carrier`).  Single-split.
* `equivReflIdAtId` — Ty-side + Raw-side + 2 attributes.  Double-split.
* `funextRefl` — 2 Ty-sides + 1 lifted-Raw-side.  Triple-split.
* `funextReflAtId` — same shape as funextRefl.
* `idStrictRefl` — mode hypothesis + Ty-side + Raw-side.
  Double-split (mode forwarded as ctor parameter). -/
/-- Target-direction totality at `Term.equivReflId`. -/
theorem partialStrengthenTyped?_isSome_target_equivReflId
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (carrier : Ty level sourceScope)
    (carrierStrengthens :
      (carrier.partialStrengthen? strengthening.back).isSome = true) :
    (partialStrengthenTyped?
        (Term.equivReflId (context := sourceCtx) carrier)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noCarrier =>
      rw [noCarrier] at carrierStrengthens
      cases carrierStrengthens
  next _ _ =>
      rfl

/-- Target-direction totality at `Term.equivReflIdAtId`. -/
theorem partialStrengthenTyped?_isSome_target_equivReflIdAtId
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (carrierRaw : RawTerm sourceScope)
    (carrierStrengthens :
      (carrier.partialStrengthen? strengthening.back).isSome = true)
    (carrierRawStrengthens :
      (carrierRaw.partialStrengthen? strengthening.back).isSome = true) :
    (partialStrengthenTyped?
        (Term.equivReflIdAtId (context := sourceCtx)
          innerLevel innerLevelLt carrier carrierRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noCarrier =>
      rw [noCarrier] at carrierStrengthens
      cases carrierStrengthens
  next _ _ =>
      split
      next noCarrierRaw =>
          rw [noCarrierRaw] at carrierRawStrengthens
          cases carrierRawStrengthens
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.funextRefl`.

The dispatcher arm checks `applyRaw.partialStrengthen?
strengthening.back.lift` — `applyRaw` lives at `scope + 1` under
the function-body binder, so the lifted strengthening applies. -/
theorem partialStrengthenTyped?_isSome_target_funextRefl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (domainStrengthens :
      (domainType.partialStrengthen? strengthening.back).isSome = true)
    (codomainStrengthens :
      (codomainType.partialStrengthen? strengthening.back).isSome = true)
    (applyStrengthens :
      (applyRaw.partialStrengthen? strengthening.back.lift).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.funextRefl (context := sourceCtx)
          domainType codomainType applyRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noDomain =>
      rw [noDomain] at domainStrengthens
      cases domainStrengthens
  next _ _ =>
      split
      next noCodomain =>
          rw [noCodomain] at codomainStrengthens
          cases codomainStrengthens
      next _ _ =>
          split
          next noApply =>
              rw [noApply] at applyStrengthens
              cases applyStrengthens
          next _ _ =>
              rfl

/-- Target-direction totality at `Term.funextReflAtId`.  Same
shape as `funextRefl` — only the target type differs. -/
theorem partialStrengthenTyped?_isSome_target_funextReflAtId
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (domainStrengthens :
      (domainType.partialStrengthen? strengthening.back).isSome = true)
    (codomainStrengthens :
      (codomainType.partialStrengthen? strengthening.back).isSome = true)
    (applyStrengthens :
      (applyRaw.partialStrengthen? strengthening.back.lift).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.funextReflAtId (context := sourceCtx)
          domainType codomainType applyRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noDomain =>
      rw [noDomain] at domainStrengthens
      cases domainStrengthens
  next _ _ =>
      split
      next noCodomain =>
          rw [noCodomain] at codomainStrengthens
          cases codomainStrengthens
      next _ _ =>
          split
          next noApply =>
              rw [noApply] at applyStrengthens
              cases applyStrengthens
          next _ _ =>
              rfl

/-- Target-direction totality at `Term.idStrictRefl`. -/
theorem partialStrengthenTyped?_isSome_target_idStrictRefl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level sourceScope)
    (rawWitness : RawTerm sourceScope)
    (carrierStrengthens :
      (carrier.partialStrengthen? strengthening.back).isSome = true)
    (witnessStrengthens :
      (rawWitness.partialStrengthen? strengthening.back).isSome = true) :
    (partialStrengthenTyped?
        (Term.idStrictRefl (context := sourceCtx)
          modeIsStrict carrier rawWitness)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noCarrier =>
      rw [noCarrier] at carrierStrengthens
      cases carrierStrengthens
  next _ _ =>
      split
      next noWitness =>
          rw [noWitness] at witnessStrengthens
          cases witnessStrengthens
      next _ _ =>
          rfl

/-! ## TypeCode family (CUMUL-2.4 schematic-raw type-code ctors)

The 10 typeCode ctors construct value-shaped representatives of
the FX type formers at the `Ty.universe outerLevel levelLe`
type.  All carry:

* 2 attribute params: `outerLevel : UniverseLevel`,
  `levelLe : outerLevel.toNat + 1 ≤ level`.
* 1-3 schematic RawTerm-typed payloads (NOT Term operands).
* No operand IH — payloads are pure raws, strengthened directly
  via `partialStrengthen?`.

Three sub-shapes by payload count:

* Single-raw: listCode, optionCode (1-split).
* Binary-raw at back-back: arrowCode, productCode, sumCode,
  eitherCode, equivCode (2-split, all at `strengthening.back`).
* Binary-raw with binder-side: piTyCode, sigmaTyCode (2-split,
  codomain at `strengthening.back.lift`).
* Ternary-raw at back-back-back: idCode (3-split). -/
/-- Target-direction totality at `Term.arrowCode`. -/
theorem partialStrengthenTyped?_isSome_target_arrowCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope)
    (domainStrengthens :
      (domainCodeRaw.partialStrengthen? strengthening.back).isSome
        = true)
    (codomainStrengthens :
      (codomainCodeRaw.partialStrengthen? strengthening.back).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.arrowCode (context := sourceCtx)
          outerLevel levelLe domainCodeRaw codomainCodeRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noDomain =>
      rw [noDomain] at domainStrengthens
      cases domainStrengthens
  next _ _ =>
      split
      next noCodomain =>
          rw [noCodomain] at codomainStrengthens
          cases codomainStrengthens
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.piTyCode`.  Codomain
strengthens under the binder via `strengthening.back.lift`. -/
theorem partialStrengthenTyped?_isSome_target_piTyCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (domainStrengthens :
      (domainCodeRaw.partialStrengthen? strengthening.back).isSome
        = true)
    (codomainLiftedStrengthens :
      (codomainCodeRaw.partialStrengthen? strengthening.back.lift).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.piTyCode (context := sourceCtx)
          outerLevel levelLe domainCodeRaw codomainCodeRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noDomain =>
      rw [noDomain] at domainStrengthens
      cases domainStrengthens
  next _ _ =>
      split
      next noCodomain =>
          rw [noCodomain] at codomainLiftedStrengthens
          cases codomainLiftedStrengthens
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.sigmaTyCode`.  Same shape
as `piTyCode` — codomain under binder. -/
theorem partialStrengthenTyped?_isSome_target_sigmaTyCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (domainStrengthens :
      (domainCodeRaw.partialStrengthen? strengthening.back).isSome
        = true)
    (codomainLiftedStrengthens :
      (codomainCodeRaw.partialStrengthen? strengthening.back.lift).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.sigmaTyCode (context := sourceCtx)
          outerLevel levelLe domainCodeRaw codomainCodeRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noDomain =>
      rw [noDomain] at domainStrengthens
      cases domainStrengthens
  next _ _ =>
      split
      next noCodomain =>
          rw [noCodomain] at codomainLiftedStrengthens
          cases codomainLiftedStrengthens
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.productCode`. -/
theorem partialStrengthenTyped?_isSome_target_productCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope)
    (firstStrengthens :
      (firstCodeRaw.partialStrengthen? strengthening.back).isSome
        = true)
    (secondStrengthens :
      (secondCodeRaw.partialStrengthen? strengthening.back).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.productCode (context := sourceCtx)
          outerLevel levelLe firstCodeRaw secondCodeRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noFirst =>
      rw [noFirst] at firstStrengthens
      cases firstStrengthens
  next _ _ =>
      split
      next noSecond =>
          rw [noSecond] at secondStrengthens
          cases secondStrengthens
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.sumCode`. -/
theorem partialStrengthenTyped?_isSome_target_sumCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (leftStrengthens :
      (leftCodeRaw.partialStrengthen? strengthening.back).isSome = true)
    (rightStrengthens :
      (rightCodeRaw.partialStrengthen? strengthening.back).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.sumCode (context := sourceCtx)
          outerLevel levelLe leftCodeRaw rightCodeRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noLeft =>
      rw [noLeft] at leftStrengthens
      cases leftStrengthens
  next _ _ =>
      split
      next noRight =>
          rw [noRight] at rightStrengthens
          cases rightStrengthens
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.listCode`.  Single raw
payload — single-split. -/
theorem partialStrengthenTyped?_isSome_target_listCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (elementStrengthens :
      (elementCodeRaw.partialStrengthen? strengthening.back).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.listCode (context := sourceCtx)
          outerLevel levelLe elementCodeRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noElement =>
      rw [noElement] at elementStrengthens
      cases elementStrengthens
  next _ _ =>
      rfl

/-- Target-direction totality at `Term.optionCode`.  Same shape
as `listCode`. -/
theorem partialStrengthenTyped?_isSome_target_optionCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (elementStrengthens :
      (elementCodeRaw.partialStrengthen? strengthening.back).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.optionCode (context := sourceCtx)
          outerLevel levelLe elementCodeRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noElement =>
      rw [noElement] at elementStrengthens
      cases elementStrengthens
  next _ _ =>
      rfl

/-- Target-direction totality at `Term.eitherCode`. -/
theorem partialStrengthenTyped?_isSome_target_eitherCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (leftStrengthens :
      (leftCodeRaw.partialStrengthen? strengthening.back).isSome = true)
    (rightStrengthens :
      (rightCodeRaw.partialStrengthen? strengthening.back).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.eitherCode (context := sourceCtx)
          outerLevel levelLe leftCodeRaw rightCodeRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noLeft =>
      rw [noLeft] at leftStrengthens
      cases leftStrengthens
  next _ _ =>
      split
      next noRight =>
          rw [noRight] at rightStrengthens
          cases rightStrengthens
      next _ _ =>
          rfl

/-- Target-direction totality at `Term.idCode`.  Three raw
payloads (typeCodeRaw + leftRaw + rightRaw). -/
theorem partialStrengthenTyped?_isSome_target_idCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope)
    (typeStrengthens :
      (typeCodeRaw.partialStrengthen? strengthening.back).isSome = true)
    (leftStrengthens :
      (leftRaw.partialStrengthen? strengthening.back).isSome = true)
    (rightStrengthens :
      (rightRaw.partialStrengthen? strengthening.back).isSome = true) :
    (partialStrengthenTyped?
        (Term.idCode (context := sourceCtx)
          outerLevel levelLe typeCodeRaw leftRaw rightRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noType =>
      rw [noType] at typeStrengthens
      cases typeStrengthens
  next _ _ =>
      split
      next noLeft =>
          rw [noLeft] at leftStrengthens
          cases leftStrengthens
      next _ _ =>
          split
          next noRight =>
              rw [noRight] at rightStrengthens
              cases rightStrengthens
          next _ _ =>
              rfl

/-! ## Parametric leaves: listNil, optionNone

Both are "closed-atomic-with-Ty-side": carry an `elementType : Ty
level scope` IMPLICIT parameter and no operand IH.  Dispatcher
recurses on `elementType.partialStrengthen?` only.  Single-split.
elementType passed via named-implicit binding `(elementType := ...)`. -/
/-- Target-direction totality at `Term.listNil`. -/
theorem partialStrengthenTyped?_isSome_target_listNil
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (elementStrengthens :
      (elementType.partialStrengthen? strengthening.back).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.listNil (context := sourceCtx)
          (elementType := elementType))
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noElement =>
      rw [noElement] at elementStrengthens
      cases elementStrengthens
  next _ _ =>
      rfl

/-- Target-direction totality at `Term.optionNone`. -/
theorem partialStrengthenTyped?_isSome_target_optionNone
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (elementStrengthens :
      (elementType.partialStrengthen? strengthening.back).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.optionNone (context := sourceCtx)
          (elementType := elementType))
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noElement =>
      rw [noElement] at elementStrengthens
      cases elementStrengthens
  next _ _ =>
      rfl

/-! ## Equivalence applicators: equivApp, equivApply

Both are binary-recursive with two non-binder Ty sides (carrierA +
carrierB) and two operand IHs (equivTerm + argumentTerm).
Pre-destructured pattern.  Quadruple-split. -/
/-- Target-direction totality at `Term.equivApp`. -/
theorem partialStrengthenTyped?_isSome_target_equivApp
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (carrierAStrengthens :
      (carrierA.partialStrengthen? strengthening.back).isSome = true)
    (carrierBStrengthens :
      (carrierB.partialStrengthen? strengthening.back).isSome = true)
    (equivIH :
      (partialStrengthenTyped? equivTerm strengthening).isSome
        = true)
    (argumentIH :
      (partialStrengthenTyped? argumentTerm strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.equivApp equivTerm argumentTerm)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noCarrierA =>
      rw [noCarrierA] at carrierAStrengthens
      cases carrierAStrengthens
  next _ _ =>
      split
      next noCarrierB =>
          rw [noCarrierB] at carrierBStrengthens
          cases carrierBStrengthens
      next _ _ =>
          split
          next noEquiv =>
              rw [noEquiv] at equivIH
              cases equivIH
          next _ _ =>
              split
              next noArgument =>
                  rw [noArgument] at argumentIH
                  cases argumentIH
              next _ _ =>
                  rfl

/-- Target-direction totality at `Term.equivApply`.  Same shape
as `equivApp`. -/
theorem partialStrengthenTyped?_isSome_target_equivApply
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (carrierAStrengthens :
      (carrierA.partialStrengthen? strengthening.back).isSome = true)
    (carrierBStrengthens :
      (carrierB.partialStrengthen? strengthening.back).isSome = true)
    (equivIH :
      (partialStrengthenTyped? equivTerm strengthening).isSome
        = true)
    (argumentIH :
      (partialStrengthenTyped? argumentTerm strengthening).isSome
        = true) :
    (partialStrengthenTyped? (Term.equivApply equivTerm argumentTerm)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noCarrierA =>
      rw [noCarrierA] at carrierAStrengthens
      cases carrierAStrengthens
  next _ _ =>
      split
      next noCarrierB =>
          rw [noCarrierB] at carrierBStrengthens
          cases carrierBStrengthens
      next _ _ =>
          split
          next noEquiv =>
              rw [noEquiv] at equivIH
              cases equivIH
          next _ _ =>
              split
              next noArgument =>
                  rw [noArgument] at argumentIH
                  cases argumentIH
              next _ _ =>
                  rfl

/-- Target-direction totality at `Term.equivCode`. -/
theorem partialStrengthenTyped?_isSome_target_equivCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope)
    (leftStrengthens :
      (leftTypeCodeRaw.partialStrengthen? strengthening.back).isSome
        = true)
    (rightStrengthens :
      (rightTypeCodeRaw.partialStrengthen? strengthening.back).isSome
        = true) :
    (partialStrengthenTyped?
        (Term.equivCode (context := sourceCtx)
          outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw)
        strengthening).isSome = true := by
  dsimp only [partialStrengthenTyped?]
  split
  next noLeft =>
      rw [noLeft] at leftStrengthens
      cases leftStrengthens
  next _ _ =>
      split
      next noRight =>
          rw [noRight] at rightStrengthens
          cases rightStrengthens
      next _ _ =>
          rfl

end Term

end LeanFX2
