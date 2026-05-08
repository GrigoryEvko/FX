import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawParInversion

/-! # Term/PreservesTerm — Strong subject reduction with term construction

Given a typed source `sourceTerm : Term context sourceType sourceRaw` and
a raw parallel step `RawStep.par sourceRaw targetRaw`, this file
constructs a typed target `targetTerm : Term context sourceType
targetRaw` together with a typed parallel step
`Step.par sourceTerm targetTerm`.

This is the load-bearing prerequisite that unblocks every kernel
metatheorem depending on **typed confluence** (Phase 7 close-out, full
`Conv.trans`, M05 progress, M09 `Term.headStep?` completeness, D8.9
`check_sound`, decidable typed conversion).  Type-equality SR
(`Step.preserves_isClosedTy`, `Step.preserves_ty_*` in
`SubjectReductionGeneral.lean`) only ships the type-side of SR —
*term construction* needs additional inversion for every typed Term ctor.

## Architecture

We progress per Term ctor in tiers:

* **Tier 0** — atoms (raw form has no children).  `RawStep.par`
  inversion forces `targetRaw = sourceRaw`, so the target Term IS the
  source Term and the typed Step.par witness is `Step.par.refl
  sourceTerm`.  Atoms shipped here:
  `unit`, `boolTrue`, `boolFalse`, `natZero`, `listNil`, `optionNone`,
  `interval0`, `interval1`, `var`.

* **Tier 1** — unary cong.  Single child; the raw inversion gives a
  child raw step.  We recurse via the IH on the child.  *Pending*.

* **Tier 2+** — binary cong / β/ι rules.  *Pending*.

The headline statement `Term.preserves` aggregates all per-ctor
lemmas via induction on Term ctor.

## Headline shape

```
theorem RawStep.par.lift_<ctor>
    (sourceTerm : Term context sourceTy <ctorRaw>)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par <ctorRaw> targetRaw) :
    ∃ targetTerm : Term context sourceTy targetRaw,
      Step.par sourceTerm targetTerm
```

The `sourceTy` is left general so the lemma applies whenever a typed
Term inhabits the matching raw shape.  For atoms, the `Term` ctor pins
the type uniquely (`Term.unit` only inhabits `Ty.unit`), so the
recipient threads the equation forward.

## Why a separate file

Co-locating with `SubjectReduction.lean` would re-export through the
`Kernel.lean` umbrella.  Per CLAUDE.md, the kernel umbrella stays
narrow.  This file becomes a Layer 3 sibling alongside the existing
type-equality SR; downstream files that need term-construction SR
import it explicitly. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## Tier 0 — atoms

Each atom's typed Term ctor produces a fixed raw form.  The raw
inversion forces the target raw to coincide with the source.  We
return the source itself as the target via `Step.par.refl`.

The proof recipe is uniform: rewrite the existential's raw-index
parameter using the inversion's equation (`subst` / `cases`), then
return `⟨sourceTerm, Step.par.refl sourceTerm⟩`. -/

/-- **Tier 0 — Term.unit lift.**  `Term context Ty.unit RawTerm.unit`
plus a raw step from `RawTerm.unit` produces a typed target identical
to the source. -/
theorem RawStep.par.lift_unit
    (sourceTerm : Term context Ty.unit (RawTerm.unit : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.unit : RawTerm scope) targetRaw) :
    ∃ targetTerm : Term context Ty.unit targetRaw,
      Step.par sourceTerm targetTerm := by
  cases RawStep.par.unit_inv rawStep
  exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-- **Tier 0 — Term.boolTrue lift.** -/
theorem RawStep.par.lift_boolTrue
    (sourceTerm : Term context Ty.bool (RawTerm.boolTrue : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolTrue : RawTerm scope) targetRaw) :
    ∃ targetTerm : Term context Ty.bool targetRaw,
      Step.par sourceTerm targetTerm := by
  cases RawStep.par.boolTrue_inv rawStep
  exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-- **Tier 0 — Term.boolFalse lift.** -/
theorem RawStep.par.lift_boolFalse
    (sourceTerm : Term context Ty.bool (RawTerm.boolFalse : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolFalse : RawTerm scope) targetRaw) :
    ∃ targetTerm : Term context Ty.bool targetRaw,
      Step.par sourceTerm targetTerm := by
  cases RawStep.par.boolFalse_inv rawStep
  exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-- **Tier 0 — Term.natZero lift.** -/
theorem RawStep.par.lift_natZero
    (sourceTerm : Term context Ty.nat (RawTerm.natZero : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.natZero : RawTerm scope) targetRaw) :
    ∃ targetTerm : Term context Ty.nat targetRaw,
      Step.par sourceTerm targetTerm := by
  cases RawStep.par.natZero_inv rawStep
  exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-- **Tier 0 — Term.listNil lift.** -/
theorem RawStep.par.lift_listNil
    {elementType : Ty level scope}
    (sourceTerm :
      Term context (Ty.listType elementType) (RawTerm.listNil : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listNil : RawTerm scope) targetRaw) :
    ∃ targetTerm : Term context (Ty.listType elementType) targetRaw,
      Step.par sourceTerm targetTerm := by
  cases RawStep.par.listNil_inv rawStep
  exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-- **Tier 0 — Term.optionNone lift.** -/
theorem RawStep.par.lift_optionNone
    {elementType : Ty level scope}
    (sourceTerm :
      Term context (Ty.optionType elementType) (RawTerm.optionNone : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionNone : RawTerm scope) targetRaw) :
    ∃ targetTerm : Term context (Ty.optionType elementType) targetRaw,
      Step.par sourceTerm targetTerm := by
  cases RawStep.par.optionNone_inv rawStep
  exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-- **Tier 0 — Term.interval0 lift.** -/
theorem RawStep.par.lift_interval0
    (sourceTerm : Term context Ty.interval (RawTerm.interval0 : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval0 : RawTerm scope) targetRaw) :
    ∃ targetTerm : Term context Ty.interval targetRaw,
      Step.par sourceTerm targetTerm := by
  cases RawStep.par.interval0_inv rawStep
  exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-- **Tier 0 — Term.interval1 lift.** -/
theorem RawStep.par.lift_interval1
    (sourceTerm : Term context Ty.interval (RawTerm.interval1 : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval1 : RawTerm scope) targetRaw) :
    ∃ targetTerm : Term context Ty.interval targetRaw,
      Step.par sourceTerm targetTerm := by
  cases RawStep.par.interval1_inv rawStep
  exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-- **Tier 0 — Term.var lift.**  `RawStep.par.var_inv` forces the
target raw to be the same `RawTerm.var position` as the source. -/
theorem RawStep.par.lift_var
    {sourceType : Ty level scope} {position : Fin scope}
    (sourceTerm : Term context sourceType (RawTerm.var position))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.var position) targetRaw) :
    ∃ targetTerm : Term context sourceType targetRaw,
      Step.par sourceTerm targetTerm := by
  cases RawStep.par.var_inv rawStep
  exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-! ## Tier 1 — unary cong (no β/ι firing)

Ctors with a single Term child at the same scope.  No β/ι rule fires
from these heads; the raw inversion gives a single child reduction.
The lemma takes the child's lift as an explicit IH parameter — when
the headline `Term.preserves` is assembled, the IH is supplied by the
outer Term induction.  Until then, each Tier 1 lemma stands as a
*compositional* statement: "given the child's lift, the wrapper's lift
follows".

Recipe per ctor:
1. Run the raw inversion to extract child raw step.
2. Apply child IH to get a typed child target + child Step.par.
3. Wrap with the corresponding `Step.par.<ctor>` cong rule.

Each Tier 1 lemma is ~6 LoC.  Cluster: natSucc, optionSome, eitherInl,
eitherInr, recordIntro, intervalOpp, modIntro, subsume. -/

/-- **Tier 1 — Term.natSucc lift.**  IH-parameterized: given the
predecessor's lift, the natSucc lift follows. -/
theorem RawStep.par.lift_natSucc
    {predRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predRaw)
    (predLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par predRaw targetRawIH →
      ∃ predTarget : Term context Ty.nat targetRawIH,
        Step.par predecessor predTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.natSucc predRaw) targetRaw) :
    ∃ targetTerm : Term context Ty.nat targetRaw,
      Step.par (Term.natSucc predecessor) targetTerm := by
  obtain ⟨predTargetRaw, targetEq, predStep⟩ := RawStep.par.natSucc_inv rawStep
  obtain ⟨predTarget, predStepTyped⟩ := predLift predStep
  cases targetEq
  exact ⟨Term.natSucc predTarget, Step.par.natSucc predStepTyped⟩

/-- **Tier 1 — Term.optionSome lift.** -/
theorem RawStep.par.lift_optionSome
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context elementType targetRawIH,
        Step.par valueTerm valueTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionSome valueRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.optionType elementType) targetRaw,
      Step.par (Term.optionSome valueTerm) targetTerm := by
  obtain ⟨valueTargetRaw, targetEq, valueStep⟩ := RawStep.par.optionSome_inv rawStep
  obtain ⟨valueTarget, valueStepTyped⟩ := valueLift valueStep
  cases targetEq
  exact ⟨Term.optionSome valueTarget, Step.par.optionSome valueStepTyped⟩

/-- **Tier 1 — Term.eitherInl lift.** -/
theorem RawStep.par.lift_eitherInl
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context leftType targetRawIH,
        Step.par valueTerm valueTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.eitherInl valueRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.eitherType leftType rightType) targetRaw,
      Step.par (Term.eitherInl (rightType := rightType) valueTerm) targetTerm := by
  obtain ⟨valueTargetRaw, targetEq, valueStep⟩ := RawStep.par.eitherInl_inv rawStep
  obtain ⟨valueTarget, valueStepTyped⟩ := valueLift valueStep
  cases targetEq
  exact ⟨Term.eitherInl (rightType := rightType) valueTarget,
         Step.par.eitherInl valueStepTyped⟩

/-- **Tier 1 — Term.eitherInr lift.** -/
theorem RawStep.par.lift_eitherInr
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context rightType targetRawIH,
        Step.par valueTerm valueTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.eitherInr valueRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.eitherType leftType rightType) targetRaw,
      Step.par (Term.eitherInr (leftType := leftType) valueTerm) targetTerm := by
  obtain ⟨valueTargetRaw, targetEq, valueStep⟩ := RawStep.par.eitherInr_inv rawStep
  obtain ⟨valueTarget, valueStepTyped⟩ := valueLift valueStep
  cases targetEq
  exact ⟨Term.eitherInr (leftType := leftType) valueTarget,
         Step.par.eitherInr valueStepTyped⟩

/-- **Tier 1 — Term.intervalOpp lift.** -/
theorem RawStep.par.lift_intervalOpp
    {innerRaw : RawTerm scope}
    (innerValue : Term context Ty.interval innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context Ty.interval targetRawIH,
        Step.par innerValue innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalOpp innerRaw) targetRaw) :
    ∃ targetTerm : Term context Ty.interval targetRaw,
      Step.par (Term.intervalOpp innerValue) targetTerm := by
  obtain ⟨innerTargetRaw, targetEq, innerStep⟩ := RawStep.par.intervalOpp_inv rawStep
  obtain ⟨innerTarget, innerStepTyped⟩ := innerLift innerStep
  cases targetEq
  exact ⟨Term.intervalOpp innerTarget, Step.par.intervalOppCong innerStepTyped⟩

/-- **Tier 1 — Term.modIntro lift.** -/
theorem RawStep.par.lift_modIntro
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.modIntro innerRaw) targetRaw) :
    ∃ targetTerm : Term context innerType targetRaw,
      Step.par (Term.modIntro innerTerm) targetTerm := by
  obtain ⟨innerTargetRaw, targetEq, innerStep⟩ := RawStep.par.modIntro_inv rawStep
  obtain ⟨innerTarget, innerStepTyped⟩ := innerLift innerStep
  cases targetEq
  exact ⟨Term.modIntro innerTarget, Step.par.modIntro innerStepTyped⟩

/-- **Tier 1 — Term.subsume lift.** -/
theorem RawStep.par.lift_subsume
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.subsume innerRaw) targetRaw) :
    ∃ targetTerm : Term context innerType targetRaw,
      Step.par (Term.subsume innerTerm) targetTerm := by
  obtain ⟨innerTargetRaw, targetEq, innerStep⟩ := RawStep.par.subsume_inv rawStep
  obtain ⟨innerTarget, innerStepTyped⟩ := innerLift innerStep
  cases targetEq
  exact ⟨Term.subsume innerTarget, Step.par.subsume innerStepTyped⟩

/-- **Tier 1 — Term.recordIntro lift.** -/
theorem RawStep.par.lift_recordIntro
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw)
    (firstLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par firstRaw targetRawIH →
      ∃ firstTarget : Term context singleFieldType targetRawIH,
        Step.par firstField firstTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.recordIntro firstRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.record singleFieldType) targetRaw,
      Step.par (Term.recordIntro firstField) targetTerm := by
  obtain ⟨firstTargetRaw, targetEq, firstStep⟩ := RawStep.par.recordIntro_inv rawStep
  obtain ⟨firstTarget, firstStepTyped⟩ := firstLift firstStep
  cases targetEq
  exact ⟨Term.recordIntro firstTarget, Step.par.recordIntroCong firstStepTyped⟩

end LeanFX2
