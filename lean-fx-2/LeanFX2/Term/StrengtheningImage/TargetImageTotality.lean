import LeanFX2.Term.StrengtheningImage.RenameImageInterface
import LeanFX2.Term.Inversion

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

end Term

end LeanFX2
