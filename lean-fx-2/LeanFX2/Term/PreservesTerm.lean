import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Term.Inversion

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
  sourceTerm`.  Shipped (9): `unit`, `boolTrue`, `boolFalse`,
  `natZero`, `listNil`, `optionNone`, `interval0`, `interval1`, `var`.

* **Tier 1 unary** — single Term child at the same scope (no β/ι).
  Shipped (8): `natSucc`, `optionSome`, `eitherInl`, `eitherInr`,
  `intervalOpp`, `modIntro`, `subsume`, `recordIntro`.

* **Tier 1 binders** — single Term child at scope+1 under a binder.
  Shipped (3): `lam`, `lamPi`, `pathLam`.

* **Tier 1 single-child no-β** — Shipped (1): `sessionRecv`.

* **Tier 2 binary cong** — two Term children, both reducing in
  parallel.  Shipped (10): `intervalMeet`, `intervalJoin`,
  `glueIntro`, `hcomp`, `codataUnfold`, `sessionSend`, `listCons`,
  `equivApp`, `refineIntro`, `effectPerform`.

* **Tier 3 eliminators (constant motive)** — eliminator ctors where
  `motiveType : Ty level scope` (NOT scope+1), giving a fixed result
  type.  3-arm raw inversion: cong + iotaCanonical1 + iotaCanonical2;
  each iota arm uses a destructor (or inline suffices/free-index) to
  align the typed scrutinee with its canonical form, then dispatches
  to the matching deep ι rule.  Shipped (5): `natElim`, `natRec`,
  `listElim`, `optionMatch`, `eitherMatch`.

* **Tier 3 single-child β-firing eliminators** — eliminators where
  the introducer's payload is a single Term child.  2-arm raw
  inversion: cong + β-deep; β arm uses an inline destructor for the
  introducer.  Shipped (5): `modElim`, `recordProj`, `refineElim`,
  `glueElim`, `codataDest`.

* **Tier 3 cong-arm-only β-blocked ctors** — ctors whose β-firing
  raw arms hit a `Ty.weaken_subst_singleton` cast wall (the βApp/
  βAppPi/βPathApp target Term has type `codomain.weaken.subst0 ...`
  while the existential expects `codomain`; the `▸`-rewrite
  propagates through the existential's other type indices).  Shipped
  cong-only variants (4): `lift_app_cong`, `lift_appPi_cong`,
  `lift_pathApp_cong`, `lift_transp_cong`.

The headline statement `Term.preserves` aggregating all per-ctor
lemmas via induction on Term ctor is the natural close-out — but
requires resolving the schematic-payload value-ctor wall and the
β cast wall.  See "Pending ctors and their walls" below.

## Headline shape (per ctor)

```
theorem RawStep.par.lift_<ctor>
    (sourceTerm : Term context sourceTy <ctorRaw>)
    (childLifts : ...)         -- IH for each Term child
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par <ctorRaw> targetRaw) :
    ∃ targetTerm : Term context sourceTy targetRaw,
      Step.par sourceTerm targetTerm
```

The `childLifts` are explicit IH parameters — when assembled into the
headline `Term.preserves` via Term induction, the IH is supplied by
the inductive case.

## Pending ctors and their walls

These ctors don't ship per-ctor lifts at the headline shape; each
needs additional infrastructure or a different headline shape.

### Schematic-payload value ctors

`Term.refl carrier rawWitness` is a value Term whose only computational
content is the schematic raw payload `rawWitness`.  RawStep.par has a
cong rule `reflCong rwStep : par (refl rw) (refl wt)` that allows the
witness raw to step.  But the typed Step.par has NO cong rule for
`Term.refl` (since the witness isn't a typed Term, just a raw).  Thus
the only typed step from `Term.refl c rw` is `Step.par.refl _`,
forcing target = source.  But the raw step can yield a non-trivial
target.

This means `lift_refl` at fixed type is structurally false: when
`par rw wt` is non-refl, no typed Step.par witness exists.

Same wall for: `oeqRefl`, `idStrictRefl`, `equivReflId`, `funextRefl`,
`equivReflIdAtId`, `funextReflAtId`, `funextIntroHet`, `equivIntroHet`,
`uaIntroHet`, `arrowCode`, `piTyCode`, `sigmaTyCode`, `productCode`,
`sumCode`, `listCode`, `optionCode`, `eitherCode`, `idCode`,
`equivCode`, `universeCode`, `cumulUp`.

Resolution options:
  1. Add typed cong rules `Step.par.<ctor>Cong : RawStep.par on raw
     payload → Step.par at heterogeneous types`.  Invasive (changes
     Step.par's ctor count gates) but mathematically correct.
  2. Restrict the headline to "raw-stable" Term ctors only (skip
     these in induction).
  3. Use a HEq-shaped existential where the target Ty can differ
     from the source's.

### β cast wall (ctors with subst0-on-codomain cong rules)

`lift_app`, `lift_appPi`, `lift_pathApp`'s β arms produce target
Terms at substituted types (`codomainType.weaken.subst0 ...` =
`codomainType` propositionally via `Ty.weaken_subst_singleton`).
The `▸` cast propagates through Lean's goal in undesired directions.

Resolution options:
  1. Use HEq-shaped existential.
  2. Provide a `Term.cast` helper that surgically rewrites the Ty
     index without touching surrounding goal expressions.
  3. Use Step.par's two-Ty signature directly in the headline.
  4. Generalize the existential over Ty: `∃ tgtTy, Eq proof, ∃
     tgtTerm : Term ctx tgtTy targetRaw, Step.par ...`.

### Type-changing iota (idJ / oeqJ / idStrictRec)

Iota β fires when the witness raw-reduces to refl/oeqRefl/idStrictRefl.
The typed witness type (`Ty.id carrier left right` for distinct
endpoints) differs from the typed target (`Ty.id carrier wr wr` after
refl-firing).  Step.par's two-Ty signature handles this, but our
fixed-type existential doesn't.  Same resolution options as the β
cast wall.

### Type-changing motive (boolElim)

`Term.boolElim`'s motive `Ty.bool → Ty` lives at scope+1.  After
scrutinee step, the result type changes (`motive.subst0 Ty.bool
oldRaw` → `motive.subst0 Ty.bool newRaw`).  Same wall.

### pair / fst / snd (heterogeneous Step.par via subst-typed second)

`Term.pair fv sv`'s second has type `secondType.subst0 firstType
firstRaw`.  After firstRaw steps, the second's required type changes.
Step.par's two-Ty signature handles this; our fixed-type lift doesn't.

### universe / cumul ctors

`universeCode` is essentially Tier 0 (only refl applies — RawStep.par
has no `universeCode` ctor).  Could ship trivially.  `cumulUp` has a
`cumulUpInnerCong` but the inner code's type is at the lower
universe — same shape as binders/cong, would ship.

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

/-- **Tier 0 — Term.universeCode lift.**  `RawTerm.universeCode k` is
a nullary canonical with NO `RawStep.par` cong rule (only refl
applies).  Hence target raw = source raw. -/
theorem RawStep.par.lift_universeCode
    {sourceType : Ty level scope} {innerLevelNat : Nat}
    (sourceTerm :
      Term context sourceType (RawTerm.universeCode innerLevelNat))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.universeCode innerLevelNat : RawTerm scope) targetRaw) :
    ∃ targetTerm : Term context sourceType targetRaw,
      Step.par sourceTerm targetTerm := by
  cases rawStep
  case refl => exact ⟨sourceTerm, Step.par.refl sourceTerm⟩

/-- Inline inversion: `RawStep.par (cumulUpMarker rw) target → ∃ wt,
target = cumulUpMarker wt ∧ par rw wt`.  No β fires from
cumulUpMarker — only refl + cong arms. -/
theorem RawStep.par.cumulUpMarker_inv {scope : Nat}
    {sourceRaw : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.cumulUpMarker sourceRaw) target) :
    ∃ targetInner, target = RawTerm.cumulUpMarker targetInner ∧
      RawStep.par sourceRaw targetInner := by
  cases parallelStep with
  | refl _ => exact ⟨sourceRaw, rfl, RawStep.par.refl _⟩
  | cumulUpMarkerCong innerStep => exact ⟨_, rfl, innerStep⟩

/-- **Tier 1 — Term.cumulUp lift.**  Single inner Term child
(`typeCode` at `Ty.universe lowerLevel levelLeLow`).  No β fires from
cumulUp; only `Step.par.cumulUpInnerCong` applies. -/
theorem RawStep.par.lift_cumulUp
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (typeCodeLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par codeRaw targetRawIH →
      ∃ typeCodeTarget :
          Term context (Ty.universe lowerLevel levelLeLow) targetRawIH,
        Step.par typeCode typeCodeTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.cumulUpMarker codeRaw : RawTerm scope) targetRaw) :
    ∃ targetTerm :
        Term context (Ty.universe higherLevel levelLeHigh) targetRaw,
      Step.par
        (Term.cumulUp lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCode)
        targetTerm := by
  obtain ⟨codeTargetRaw, eq, codeStep⟩ := RawStep.par.cumulUpMarker_inv rawStep
  obtain ⟨codeTarget, codeStepTyped⟩ := typeCodeLift codeStep
  cases eq
  exact ⟨Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow levelLeHigh
                      codeTarget,
         Step.par.cumulUpInnerCong lowerLevel higherLevel cumulMonotone
                                   levelLeLow levelLeHigh codeStepTyped⟩

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

/-! ## Tier 1 — binder cong rules

Lambda-shaped ctors carry a body at scope+1 under the ctor's
introduced binder.  The IH lives at scope+1 with the extended
context.  No β fires from a bare lam/lamPi/pathLam — only when
applied (Tier 3 territory).

These ctors construct typed function values; the type is preserved
through the cong rule because the body at scope+1 keeps the same
codomain shape.

* `lam` / `lamPi` produce `Ty.arrow` / `Ty.piTy` shaped values.
* `pathLam` produces `Ty.path carrierType leftEndpoint rightEndpoint`
  with the body at `Ty.interval`-extended context. -/

/-- **Tier 1 — Term.lam lift.**  Body lives at the extended context
`context.cons domainType` and at `codomainType.weaken`. -/
theorem RawStep.par.lift_lam
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType.weaken bodyRaw)
    (bodyLift : ∀ {targetRawIH : RawTerm (scope + 1)},
      RawStep.par bodyRaw targetRawIH →
      ∃ bodyTarget : Term (context.cons domainType) codomainType.weaken targetRawIH,
        Step.par body bodyTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.lam bodyRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.arrow domainType codomainType) targetRaw,
      Step.par (Term.lam (codomainType := codomainType) body) targetTerm := by
  obtain ⟨bodyTargetRaw, targetEq, bodyStep⟩ := RawStep.par.lam_inv rawStep
  obtain ⟨bodyTarget, bodyStepTyped⟩ := bodyLift bodyStep
  cases targetEq
  exact ⟨Term.lam (codomainType := codomainType) bodyTarget,
         Step.par.lam bodyStepTyped⟩

/-- **Tier 1 — Term.lamPi lift.**  Body lives at the extended context
and the dependent codomain type lives at scope+1. -/
theorem RawStep.par.lift_lamPi
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType bodyRaw)
    (bodyLift : ∀ {targetRawIH : RawTerm (scope + 1)},
      RawStep.par bodyRaw targetRawIH →
      ∃ bodyTarget : Term (context.cons domainType) codomainType targetRawIH,
        Step.par body bodyTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.lam bodyRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.piTy domainType codomainType) targetRaw,
      Step.par (Term.lamPi (domainType := domainType) body) targetTerm := by
  obtain ⟨bodyTargetRaw, targetEq, bodyStep⟩ := RawStep.par.lam_inv rawStep
  obtain ⟨bodyTarget, bodyStepTyped⟩ := bodyLift bodyStep
  cases targetEq
  exact ⟨Term.lamPi (domainType := domainType) bodyTarget,
         Step.par.lamPi bodyStepTyped⟩

/-- **Tier 1 — Term.pathLam lift.** -/
theorem RawStep.par.lift_pathLam
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyLift : ∀ {targetRawIH : RawTerm (scope + 1)},
      RawStep.par bodyRaw targetRawIH →
      ∃ bodyTarget :
          Term (context.cons Ty.interval) carrierType.weaken targetRawIH,
        Step.par body bodyTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.pathLam bodyRaw) targetRaw) :
    ∃ targetTerm :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint) targetRaw,
      Step.par
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body)
        targetTerm := by
  obtain ⟨bodyTargetRaw, targetEq, bodyStep⟩ := RawStep.par.pathLam_inv rawStep
  obtain ⟨bodyTarget, bodyStepTyped⟩ := bodyLift bodyStep
  cases targetEq
  exact ⟨Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                      bodyTarget,
         Step.par.pathLam modeIsUnivalent bodyStepTyped⟩

/-! ## Tier 2 — binary cong rules (no β/ι firing from the head)

Two Term children at the same scope, both contributing independent
parallel reductions.  Same recipe as Tier 1 unary, but with two IHs.

Recipe per binary ctor:
  obtain ⟨_, _, eq, leftStep, rightStep⟩ := <ctor>_inv rawStep
  obtain ⟨leftT,  leftSt⟩  := leftLift  leftStep
  obtain ⟨rightT, rightSt⟩ := rightLift rightStep
  cases eq
  exact ⟨Term.<ctor> ... leftT rightT,
         Step.par.<ctor>Cong leftSt rightSt⟩

Shipped this batch:
  * intervalMeet — both at Ty.interval
  * intervalJoin — both at Ty.interval
  * glueIntro    — both at baseType
  * hcomp        — both at carrierType
  * codataUnfold — different types (state, transition)
  * sessionSend  — different types (channel = session, payload)
  * effectPerform — different types (operation, arguments) -/

/-- **Tier 2 — Term.intervalMeet lift.** -/
theorem RawStep.par.lift_intervalMeet
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget : Term context Ty.interval targetRawIH,
        Step.par leftValue leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget : Term context Ty.interval targetRawIH,
        Step.par rightValue rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalMeet leftRaw rightRaw) targetRaw) :
    ∃ targetTerm : Term context Ty.interval targetRaw,
      Step.par (Term.intervalMeet leftValue rightValue) targetTerm := by
  obtain ⟨leftTargetRaw, rightTargetRaw, eq, leftStep, rightStep⟩ :=
    RawStep.par.intervalMeet_inv rawStep
  obtain ⟨leftTarget, leftStepTyped⟩ := leftLift leftStep
  obtain ⟨rightTarget, rightStepTyped⟩ := rightLift rightStep
  cases eq
  exact ⟨Term.intervalMeet leftTarget rightTarget,
         Step.par.intervalMeetCong leftStepTyped rightStepTyped⟩

/-- **Tier 2 — Term.intervalJoin lift.** -/
theorem RawStep.par.lift_intervalJoin
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget : Term context Ty.interval targetRawIH,
        Step.par leftValue leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget : Term context Ty.interval targetRawIH,
        Step.par rightValue rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalJoin leftRaw rightRaw) targetRaw) :
    ∃ targetTerm : Term context Ty.interval targetRaw,
      Step.par (Term.intervalJoin leftValue rightValue) targetTerm := by
  obtain ⟨leftTargetRaw, rightTargetRaw, eq, leftStep, rightStep⟩ :=
    RawStep.par.intervalJoin_inv rawStep
  obtain ⟨leftTarget, leftStepTyped⟩ := leftLift leftStep
  obtain ⟨rightTarget, rightStepTyped⟩ := rightLift rightStep
  cases eq
  exact ⟨Term.intervalJoin leftTarget rightTarget,
         Step.par.intervalJoinCong leftStepTyped rightStepTyped⟩

/-- **Tier 2 — Term.glueIntro lift.** -/
theorem RawStep.par.lift_glueIntro
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context baseType targetRawIH,
        Step.par baseValue baseTarget)
    (partialLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par partialRaw targetRawIH →
      ∃ partialTarget : Term context baseType targetRawIH,
        Step.par partialValue partialTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.glueIntro baseRaw partialRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.glue baseType boundaryWitness) targetRaw,
      Step.par
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseValue
                        partialValue)
        targetTerm := by
  obtain ⟨baseTargetRaw, partialTargetRaw, eq, baseStep, partialStep⟩ :=
    RawStep.par.glueIntro_inv rawStep
  obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
  obtain ⟨partialTarget, partialStepTyped⟩ := partialLift partialStep
  cases eq
  exact ⟨Term.glueIntro modeIsUnivalent baseType boundaryWitness baseTarget
                        partialTarget,
         Step.par.glueIntroCong modeIsUnivalent baseStepTyped partialStepTyped⟩

/-- **Tier 2 — Term.hcomp lift.** -/
theorem RawStep.par.lift_hcomp
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw)
    (sidesLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par sidesRaw targetRawIH →
      ∃ sidesTarget : Term context carrierType targetRawIH,
        Step.par sidesValue sidesTarget)
    (capLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par capRaw targetRawIH →
      ∃ capTarget : Term context carrierType targetRawIH,
        Step.par capValue capTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.hcomp sidesRaw capRaw) targetRaw) :
    ∃ targetTerm : Term context carrierType targetRaw,
      Step.par (Term.hcomp modeIsUnivalent sidesValue capValue) targetTerm := by
  obtain ⟨sidesTargetRaw, capTargetRaw, eq, sidesStep, capStep⟩ :=
    RawStep.par.hcomp_inv rawStep
  obtain ⟨sidesTarget, sidesStepTyped⟩ := sidesLift sidesStep
  obtain ⟨capTarget, capStepTyped⟩ := capLift capStep
  cases eq
  exact ⟨Term.hcomp modeIsUnivalent sidesTarget capTarget,
         Step.par.hcompCong modeIsUnivalent sidesStepTyped capStepTyped⟩

/-- **Tier 2 — Term.codataUnfold lift.** -/
theorem RawStep.par.lift_codataUnfold
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw)
    (stateLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par stateRaw targetRawIH →
      ∃ stateTarget : Term context stateType targetRawIH,
        Step.par initialState stateTarget)
    (transitionLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par transitionRaw targetRawIH →
      ∃ transitionTarget :
          Term context (Ty.arrow stateType outputType) targetRawIH,
        Step.par transition transitionTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.codataUnfold stateRaw transitionRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.codata stateType outputType) targetRaw,
      Step.par (Term.codataUnfold initialState transition) targetTerm := by
  obtain ⟨stateTargetRaw, transitionTargetRaw, eq, stateStep, transitionStep⟩ :=
    RawStep.par.codataUnfold_inv rawStep
  obtain ⟨stateTarget, stateStepTyped⟩ := stateLift stateStep
  obtain ⟨transitionTarget, transitionStepTyped⟩ := transitionLift transitionStep
  cases eq
  exact ⟨Term.codataUnfold stateTarget transitionTarget,
         Step.par.codataUnfoldCong stateStepTyped transitionStepTyped⟩

/-- **Tier 2 — Term.sessionSend lift.** -/
theorem RawStep.par.lift_sessionSend
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (payload : Term context payloadType payloadRaw)
    (channelLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par channelRaw targetRawIH →
      ∃ channelTarget : Term context (Ty.session protocolStep) targetRawIH,
        Step.par channel channelTarget)
    (payloadLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par payloadRaw targetRawIH →
      ∃ payloadTarget : Term context payloadType targetRawIH,
        Step.par payload payloadTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.sessionSend channelRaw payloadRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.session protocolStep) targetRaw,
      Step.par (Term.sessionSend protocolStep channel payload) targetTerm := by
  obtain ⟨channelTargetRaw, payloadTargetRaw, eq, channelStep, payloadStep⟩ :=
    RawStep.par.sessionSend_inv rawStep
  obtain ⟨channelTarget, channelStepTyped⟩ := channelLift channelStep
  obtain ⟨payloadTarget, payloadStepTyped⟩ := payloadLift payloadStep
  cases eq
  exact ⟨Term.sessionSend protocolStep channelTarget payloadTarget,
         Step.par.sessionSendCong channelStepTyped payloadStepTyped⟩

/-- **Tier 2 — Term.listCons lift.**  Two children: head (elementType)
and tail (listType elementType). -/
theorem RawStep.par.lift_listCons
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (headLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par headRaw targetRawIH →
      ∃ headTarget : Term context elementType targetRawIH,
        Step.par headTerm headTarget)
    (tailLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par tailRaw targetRawIH →
      ∃ tailTarget : Term context (Ty.listType elementType) targetRawIH,
        Step.par tailTerm tailTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listCons headRaw tailRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.listType elementType) targetRaw,
      Step.par (Term.listCons headTerm tailTerm) targetTerm := by
  obtain ⟨headTargetRaw, tailTargetRaw, eq, headStep, tailStep⟩ :=
    RawStep.par.listCons_inv rawStep
  obtain ⟨headTarget, headStepTyped⟩ := headLift headStep
  obtain ⟨tailTarget, tailStepTyped⟩ := tailLift tailStep
  cases eq
  exact ⟨Term.listCons headTarget tailTarget,
         Step.par.listCons headStepTyped tailStepTyped⟩

/-- **Tier 2 — Term.equivApp lift.**  Two children: equiv (Ty.equiv A B)
and argument (A); result type B. -/
theorem RawStep.par.lift_equivApp
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw)
    (equivLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par equivRaw targetRawIH →
      ∃ equivTarget : Term context (Ty.equiv carrierA carrierB) targetRawIH,
        Step.par equivTerm equivTarget)
    (argumentLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentRaw targetRawIH →
      ∃ argumentTarget : Term context carrierA targetRawIH,
        Step.par argumentTerm argumentTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.equivApp equivRaw argumentRaw) targetRaw) :
    ∃ targetTerm : Term context carrierB targetRaw,
      Step.par (Term.equivApp equivTerm argumentTerm) targetTerm := by
  obtain ⟨equivTargetRaw, argumentTargetRaw, eq, equivStep, argumentStep⟩ :=
    RawStep.par.equivApp_inv rawStep
  obtain ⟨equivTarget, equivStepTyped⟩ := equivLift equivStep
  obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
  cases eq
  exact ⟨Term.equivApp equivTarget argumentTarget,
         Step.par.equivAppCong equivStepTyped argumentStepTyped⟩

/-- **Tier 1 — Term.sessionRecv lift.**  Single Term child (channel),
no β fires. -/
theorem RawStep.par.lift_sessionRecv
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (channelLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par channelRaw targetRawIH →
      ∃ channelTarget : Term context (Ty.session protocolStep) targetRawIH,
        Step.par channel channelTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.sessionRecv channelRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.session protocolStep) targetRaw,
      Step.par (Term.sessionRecv channel) targetTerm := by
  obtain ⟨channelTargetRaw, eq, channelStep⟩ := RawStep.par.sessionRecv_inv rawStep
  obtain ⟨channelTarget, channelStepTyped⟩ := channelLift channelStep
  cases eq
  exact ⟨Term.sessionRecv channelTarget,
         Step.par.sessionRecvCong channelStepTyped⟩

/-- **Tier 2 — Term.refineIntro lift.**  Two children: value (baseType)
and predicateProof (Ty.unit). -/
theorem RawStep.par.lift_refineIntro
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context baseType targetRawIH,
        Step.par baseValue valueTarget)
    (proofLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par proofRaw targetRawIH →
      ∃ proofTarget : Term context Ty.unit targetRawIH,
        Step.par predicateProof proofTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refineIntro valueRaw proofRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.refine baseType predicate) targetRaw,
      Step.par (Term.refineIntro predicate baseValue predicateProof) targetTerm := by
  obtain ⟨valueTargetRaw, proofTargetRaw, eq, valueStep, proofStep⟩ :=
    RawStep.par.refineIntro_inv rawStep
  obtain ⟨valueTarget, valueStepTyped⟩ := valueLift valueStep
  obtain ⟨proofTarget, proofStepTyped⟩ := proofLift proofStep
  cases eq
  exact ⟨Term.refineIntro predicate valueTarget proofTarget,
         Step.par.refineIntroCong valueStepTyped proofStepTyped⟩

/-! ## Tier 3 — eliminators with constant motive

Eliminators where `motiveType : Ty level scope` (NOT scope+1) — the
result type is `motiveType` regardless of the scrutinee's raw form.
Hence the lift can stay at fixed type even when the scrutinee
parallel-reduces.

The raw inversion has THREE arms: cong + iota-canonical (one per
canonical scrutinee form).  We dispatch each arm to the matching typed
Step.par cong / iota rule.  The iota arms use the deep variants
(iota*Deep) which take a `Step.par scrutinee canonicalTerm` premise —
this is exactly what the scrutinee IH produces (after the
`Term.<canonical>_unique` HEq → eq conversion).

For natElim's iotaSucc arm, the raw scrutinee parallel-reduces to
`RawTerm.natSucc predRaw`.  The typed scrutinee IH applied to this
step yields a typed term at `Term ctx Ty.nat (natSucc predRaw)`.
Pattern-matching on this typed term forces it to be of the form
`Term.natSucc predTarget` for some typed predTarget. -/

/-- **Tier 3 — Term.natElim lift.**  Three-arm raw inversion handles
cong + iotaZero + iotaSucc.  motiveType at scope (constant), so
target type is fixed at `motiveType`. -/
theorem RawStep.par.lift_natElim
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget : Term context (Ty.arrow Ty.nat motiveType) targetRawIH,
        Step.par succBranch succTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.natElim scrutineeRaw zeroRaw succRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.natElim scrutinee zeroBranch succBranch) targetTerm := by
  rcases RawStep.par.natElim_inv rawStep with
    ⟨scrutTargetRaw, zeroTargetRaw, succTargetRaw, eq, scrutStep, zeroStep, succStep⟩
    | ⟨zeroTargetRaw, eq, scrutToZero, zeroStep⟩
    | ⟨predTargetRaw, succTargetRaw, eq, scrutToSucc, succStep⟩
  · -- cong arm
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
    cases eq
    exact ⟨Term.natElim scrutTarget zeroTarget succTarget,
           Step.par.natElim scrutStepTyped zeroStepTyped succStepTyped⟩
  · -- iotaZero arm: scrutinee →* natZero, target = zero result
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToZero
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    -- Use uniqueness to force scrutTarget = Term.natZero (HEq → eq at fixed type)
    have heq :
        HEq scrutTarget (Term.natZero (context := context)) :=
      Term.natZero_unique scrutTarget Term.natZero
    have scrutEq : scrutTarget = (Term.natZero (context := context)) := eq_of_heq heq
    rw [scrutEq] at scrutStepTyped
    cases eq
    exact ⟨zeroTarget,
           Step.par.iotaNatElimZeroDeep succBranch scrutStepTyped zeroStepTyped⟩
  · -- iotaSucc arm: scrutinee →* natSucc predRaw, target = app succ predRaw
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToSucc
    obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
    -- scrutTarget : Term ctx Ty.nat (natSucc predTargetRaw) — must be Term.natSucc _
    -- Use the destructor (suffices/free-index pattern) to extract the
    -- predecessor at fixed Ty.nat type.
    obtain ⟨predecessor, predecessorHeq⟩ := Term.natSuccDestruct scrutTarget
    have predecessorEq : scrutTarget = Term.natSucc predecessor :=
      eq_of_heq predecessorHeq
    rw [predecessorEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app succTarget predecessor,
           Step.par.iotaNatElimSuccDeep zeroBranch scrutStepTyped succStepTyped⟩

/-- **Tier 3 — Term.natRec lift.**  Same shape as natElim but with
the recursive succ branch type `Ty.arrow Ty.nat (Ty.arrow motiveType
motiveType)` and the iotaSucc target shape `app (app succ pred)
(natRec pred zero succ)`. -/
theorem RawStep.par.lift_natRec
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget :
          Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
                       targetRawIH,
        Step.par succBranch succTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.natRec scrutineeRaw zeroRaw succRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.natRec scrutinee zeroBranch succBranch) targetTerm := by
  rcases RawStep.par.natRec_inv rawStep with
    ⟨scrutTargetRaw, zeroTargetRaw, succTargetRaw, eq, scrutStep, zeroStep, succStep⟩
    | ⟨zeroTargetRaw, eq, scrutToZero, zeroStep⟩
    | ⟨predRaw, zeroTargetRaw, succTargetRaw, eq, scrutToSucc, zeroStep, succStep⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
    cases eq
    exact ⟨Term.natRec scrutTarget zeroTarget succTarget,
           Step.par.natRec scrutStepTyped zeroStepTyped succStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToZero
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    have heq :
        HEq scrutTarget (Term.natZero (context := context)) :=
      Term.natZero_unique scrutTarget Term.natZero
    have scrutEq : scrutTarget = (Term.natZero (context := context)) := eq_of_heq heq
    rw [scrutEq] at scrutStepTyped
    cases eq
    exact ⟨zeroTarget,
           Step.par.iotaNatRecZeroDeep succBranch scrutStepTyped zeroStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToSucc
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
    obtain ⟨predecessor, predecessorHeq⟩ := Term.natSuccDestruct scrutTarget
    have predecessorEq : scrutTarget = Term.natSucc predecessor :=
      eq_of_heq predecessorHeq
    rw [predecessorEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app (Term.app succTarget predecessor)
                    (Term.natRec predecessor zeroTarget succTarget),
           Step.par.iotaNatRecSuccDeep scrutStepTyped zeroStepTyped succStepTyped⟩

/-- **Tier 3 — Term.listElim lift.**  Three-arm raw inversion: cong
+ iotaNil + iotaCons.  motiveType at scope, listType elementType
scrutinee. -/
theorem RawStep.par.lift_listElim
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.listType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (nilLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par nilRaw targetRawIH →
      ∃ nilTarget : Term context motiveType targetRawIH,
        Step.par nilBranch nilTarget)
    (consLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par consRaw targetRawIH →
      ∃ consTarget :
          Term context
            (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
            targetRawIH,
        Step.par consBranch consTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.listElim scrutineeRaw nilRaw consRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.listElim scrutinee nilBranch consBranch) targetTerm := by
  rcases RawStep.par.listElim_inv rawStep with
    ⟨scrutTargetRaw, nilTargetRaw, consTargetRaw, eq, scrutStep, nilStep, consStep⟩
    | ⟨nilTargetRaw, eq, scrutToNil, nilStep⟩
    | ⟨headRaw, tailRaw, consTargetRaw, eq, scrutToCons, consStep⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨nilTarget, nilStepTyped⟩ := nilLift nilStep
    obtain ⟨consTarget, consStepTyped⟩ := consLift consStep
    cases eq
    exact ⟨Term.listElim scrutTarget nilTarget consTarget,
           Step.par.listElim scrutStepTyped nilStepTyped consStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToNil
    obtain ⟨nilTarget, nilStepTyped⟩ := nilLift nilStep
    -- scrutTarget : Term ctx (listType elementType) listNil — must be Term.listNil.
    -- Use suffices/free-index destructor to bypass dep-elim on var arm.
    have scrutEq :
        scrutTarget = (Term.listNil (context := context) (elementType := elementType)) := by
      suffices key :
          ∀ {someType : Ty level scope}
            (genericTerm : Term context someType (RawTerm.listNil (scope := scope))),
            someType = Ty.listType elementType →
            HEq genericTerm
                (Term.listNil (context := context) (elementType := elementType)) by
        exact eq_of_heq (key scrutTarget rfl)
      intro someType genericTerm someTypeIsListType
      cases genericTerm
      rename_i innerElement
      have elementEq : innerElement = elementType :=
        Ty.listType.inj someTypeIsListType
      cases elementEq
      exact HEq.rfl
    rw [scrutEq] at scrutStepTyped
    cases eq
    exact ⟨nilTarget,
           Step.par.iotaListElimNilDeep consBranch scrutStepTyped nilStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToCons
    obtain ⟨consTarget, consStepTyped⟩ := consLift consStep
    obtain ⟨headTerm, tailTerm, headHeq⟩ := Term.listConsDestruct scrutTarget
    have headEq : scrutTarget = Term.listCons headTerm tailTerm :=
      eq_of_heq headHeq
    rw [headEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app (Term.app consTarget headTerm) tailTerm,
           Step.par.iotaListElimConsDeep nilBranch scrutStepTyped consStepTyped⟩

/-- **Tier 3 — Term.optionMatch lift.** -/
theorem RawStep.par.lift_optionMatch
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.optionType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (noneLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par noneRaw targetRawIH →
      ∃ noneTarget : Term context motiveType targetRawIH,
        Step.par noneBranch noneTarget)
    (someLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par someRaw targetRawIH →
      ∃ someTarget :
          Term context (Ty.arrow elementType motiveType) targetRawIH,
        Step.par someBranch someTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.optionMatch scrutineeRaw noneRaw someRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.optionMatch scrutinee noneBranch someBranch) targetTerm := by
  rcases RawStep.par.optionMatch_inv rawStep with
    ⟨scrutTargetRaw, noneTargetRaw, someTargetRaw, eq, scrutStep, noneStep, someStep⟩
    | ⟨noneTargetRaw, eq, scrutToNone, noneStep⟩
    | ⟨valueRaw, someTargetRaw, eq, scrutToSome, someStep⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨noneTarget, noneStepTyped⟩ := noneLift noneStep
    obtain ⟨someTarget, someStepTyped⟩ := someLift someStep
    cases eq
    exact ⟨Term.optionMatch scrutTarget noneTarget someTarget,
           Step.par.optionMatch scrutStepTyped noneStepTyped someStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToNone
    obtain ⟨noneTarget, noneStepTyped⟩ := noneLift noneStep
    -- scrutTarget : Term ctx (optionType elementType) optionNone
    have scrutEq :
        scrutTarget = (Term.optionNone (context := context)
                                       (elementType := elementType)) := by
      suffices key :
          ∀ {someType : Ty level scope}
            (genericTerm : Term context someType (RawTerm.optionNone (scope := scope))),
            someType = Ty.optionType elementType →
            HEq genericTerm
                (Term.optionNone (context := context) (elementType := elementType)) by
        exact eq_of_heq (key scrutTarget rfl)
      intro someType genericTerm someTypeIsOptionType
      cases genericTerm
      rename_i innerElement
      have elementEq : innerElement = elementType :=
        Ty.optionType.inj someTypeIsOptionType
      cases elementEq
      exact HEq.rfl
    rw [scrutEq] at scrutStepTyped
    cases eq
    exact ⟨noneTarget,
           Step.par.iotaOptionMatchNoneDeep someBranch scrutStepTyped noneStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToSome
    obtain ⟨someTarget, someStepTyped⟩ := someLift someStep
    obtain ⟨valueTerm, valueHeq⟩ := Term.optionSomeDestruct scrutTarget
    have valueEq : scrutTarget = Term.optionSome valueTerm := eq_of_heq valueHeq
    rw [valueEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app someTarget valueTerm,
           Step.par.iotaOptionMatchSomeDeep noneBranch scrutStepTyped someStepTyped⟩

/-- **Tier 3 — Term.eitherMatch lift.** -/
theorem RawStep.par.lift_eitherMatch
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget :
          Term context (Ty.eitherType leftType rightType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget :
          Term context (Ty.arrow leftType motiveType) targetRawIH,
        Step.par leftBranch leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget :
          Term context (Ty.arrow rightType motiveType) targetRawIH,
        Step.par rightBranch rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.eitherMatch scrutinee leftBranch rightBranch) targetTerm := by
  rcases RawStep.par.eitherMatch_inv rawStep with
    ⟨scrutTargetRaw, leftTargetRaw, rightTargetRaw, eq, scrutStep, leftStep, rightStep⟩
    | ⟨valueRaw, leftTargetRaw, eq, scrutToInl, leftStep⟩
    | ⟨valueRaw, rightTargetRaw, eq, scrutToInr, rightStep⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨leftTarget, leftStepTyped⟩ := leftLift leftStep
    obtain ⟨rightTarget, rightStepTyped⟩ := rightLift rightStep
    cases eq
    exact ⟨Term.eitherMatch scrutTarget leftTarget rightTarget,
           Step.par.eitherMatch scrutStepTyped leftStepTyped rightStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToInl
    obtain ⟨leftTarget, leftStepTyped⟩ := leftLift leftStep
    obtain ⟨valueTerm, valueHeq⟩ := Term.eitherInlDestruct scrutTarget
    have valueEq :
        scrutTarget = (Term.eitherInl (rightType := rightType) valueTerm) :=
      eq_of_heq valueHeq
    rw [valueEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app leftTarget valueTerm,
           Step.par.iotaEitherMatchInlDeep rightBranch scrutStepTyped leftStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToInr
    obtain ⟨rightTarget, rightStepTyped⟩ := rightLift rightStep
    obtain ⟨valueTerm, valueHeq⟩ := Term.eitherInrDestruct scrutTarget
    have valueEq :
        scrutTarget = (Term.eitherInr (leftType := leftType) valueTerm) :=
      eq_of_heq valueHeq
    rw [valueEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app rightTarget valueTerm,
           Step.par.iotaEitherMatchInrDeep leftBranch scrutStepTyped rightStepTyped⟩

/-- **Tier 2 — Term.effectPerform lift.**  Two children: operationTag
(Ty.effect argumentCarrier effectTag) and arguments (argumentCarrier).  -/
theorem RawStep.par.lift_effectPerform
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    (operationTag :
      Term context (Ty.effect operationSignature.argumentCarrier effectTag)
                   operationRaw)
    (arguments :
      Term context operationSignature.argumentCarrier argumentsRaw)
    (operationLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par operationRaw targetRawIH →
      ∃ operationTarget :
          Term context (Ty.effect operationSignature.argumentCarrier effectTag)
                       targetRawIH,
        Step.par operationTag operationTarget)
    (argumentsLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentsRaw targetRawIH →
      ∃ argumentsTarget :
          Term context operationSignature.argumentCarrier targetRawIH,
        Step.par arguments argumentsTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.effectPerform operationRaw argumentsRaw) targetRaw) :
    ∃ targetTerm :
        Term context (Ty.effect operationSignature.resultCarrier effectTag)
                     targetRaw,
      Step.par
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments)
        targetTerm := by
  obtain ⟨operationTargetRaw, argumentsTargetRaw, eq, operationStep, argumentsStep⟩ :=
    RawStep.par.effectPerform_inv rawStep
  obtain ⟨operationTarget, operationStepTyped⟩ := operationLift operationStep
  obtain ⟨argumentsTarget, argumentsStepTyped⟩ := argumentsLift argumentsStep
  cases eq
  exact ⟨Term.effectPerform effectTag effectRow operationSignature
                            canPerformOperation operationTarget argumentsTarget,
         Step.par.effectPerformCong operationStepTyped argumentsStepTyped⟩

/-! ## Inline destructors for canonical-head Term values

These destructors mirror the ones in `Term/Inversion.lean`
(natSuccDestruct, listConsDestruct, optionSomeDestruct,
eitherInlDestruct, eitherInrDestruct, pairDestruct) for ctors not
yet covered upstream — each follows the suffices/free-the-index
pattern documented in `feedback_lean_free_type_via_suffices.md` to
sidestep the `Ty.X = varType ctx pos` dep-elim wall.

Inline in this file because they're consumed only by the lift
theorems below; promoting to Inversion.lean is a future cleanup. -/

/-- Destructor for `Term.modIntro`: from a typed Term whose raw form
is `RawTerm.modIntro innerRaw`, extract the typed inner. -/
def Term.modIntroDestruct
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (someTerm : Term context innerType (RawTerm.modIntro innerRaw)) :
    Σ' (innerTerm : Term context innerType innerRaw),
       HEq someTerm (Term.modIntro innerTerm) := by
  cases someTerm
  rename_i innerTerm
  exact ⟨innerTerm, HEq.rfl⟩

/-- Destructor for `Term.recordIntro`. -/
def Term.recordIntroDestruct
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.record singleFieldType) (RawTerm.recordIntro firstRaw)) :
    Σ' (firstField : Term context singleFieldType firstRaw),
       HEq someTerm (Term.recordIntro firstField) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.recordIntro firstRaw)),
        someType = Ty.record singleFieldType →
        Σ' (firstField : Term context singleFieldType firstRaw),
           HEq genericTerm (Term.recordIntro firstField) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsRecord
  cases genericTerm
  rename_i innerSingleField firstField
  have singleFieldEq : innerSingleField = singleFieldType :=
    Ty.record.inj someTypeIsRecord
  cases singleFieldEq
  exact ⟨firstField, HEq.rfl⟩

/-- Destructor for `Term.refineIntro`. -/
def Term.refineIntroDestruct
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.refine baseType predicate)
        (RawTerm.refineIntro valueRaw proofRaw)) :
    Σ' (baseValue : Term context baseType valueRaw)
       (predicateProof : Term context Ty.unit proofRaw),
       HEq someTerm (Term.refineIntro predicate baseValue predicateProof) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.refineIntro valueRaw proofRaw)),
        someType = Ty.refine baseType predicate →
        Σ' (baseValue : Term context baseType valueRaw)
           (predicateProof : Term context Ty.unit proofRaw),
           HEq genericTerm (Term.refineIntro predicate baseValue predicateProof) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsRefine
  cases genericTerm
  rename_i innerBase innerPredicate baseValue predicateProof
  have refineEq := Ty.refine.inj someTypeIsRefine
  cases refineEq.1
  cases refineEq.2
  exact ⟨baseValue, predicateProof, HEq.rfl⟩

/-- Destructor for `Term.glueIntro`. -/
def Term.glueIntroDestruct
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.glue baseType boundaryWitness)
        (RawTerm.glueIntro baseRaw partialRaw)) :
    Σ' (baseValue : Term context baseType baseRaw)
       (partialValue : Term context baseType partialRaw),
       HEq someTerm
            (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseValue
                            partialValue) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.glueIntro baseRaw partialRaw)),
        someType = Ty.glue baseType boundaryWitness →
        Σ' (baseValue : Term context baseType baseRaw)
           (partialValue : Term context baseType partialRaw),
           HEq genericTerm
                (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseValue
                                partialValue) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsGlue
  cases genericTerm
  rename_i innerMode innerBase innerBoundary baseValue partialValue
  have glueEq := Ty.glue.inj someTypeIsGlue
  cases glueEq.1
  cases glueEq.2
  exact ⟨baseValue, partialValue, HEq.rfl⟩

/-- Destructor for `Term.lam` (non-dep arrow).  Disambiguated from
`Term.lamPi`, `Term.funextRefl`, `Term.funextReflAtId`, and
`Term.funextIntroHet` (all with raw `RawTerm.lam ...`) by the fixed
`Ty.arrow` source-type index — the latter three have `Ty.id` or
`Ty.piTy` shaped types. -/
def Term.lamDestruct
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (someTerm :
      Term context (Ty.arrow domainType codomainType) (RawTerm.lam bodyRaw)) :
    Σ' (body : Term (context.cons domainType) codomainType.weaken bodyRaw),
       HEq someTerm (Term.lam (codomainType := codomainType) body) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.lam bodyRaw)),
        someType = Ty.arrow domainType codomainType →
        Σ' (body : Term (context.cons domainType) codomainType.weaken bodyRaw),
           HEq genericTerm (Term.lam (codomainType := codomainType) body) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsArrow
  cases genericTerm
  case lam innerDomain innerCodomain body =>
    have arrowEq := Ty.arrow.inj someTypeIsArrow
    cases arrowEq.1
    cases arrowEq.2
    exact ⟨body, HEq.rfl⟩
  case lamPi innerDomain innerCodomain body =>
    -- Ty.piTy ≠ Ty.arrow shape mismatch
    nomatch someTypeIsArrow
  case funextRefl _ _ _ => nomatch someTypeIsArrow
  case funextReflAtId _ _ _ => nomatch someTypeIsArrow
  case funextIntroHet _ _ _ _ => nomatch someTypeIsArrow

/-- Destructor for `Term.codataUnfold`. -/
def Term.codataUnfoldDestruct
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.codata stateType outputType)
        (RawTerm.codataUnfold stateRaw transitionRaw)) :
    Σ' (initialState : Term context stateType stateRaw)
       (transition : Term context (Ty.arrow stateType outputType) transitionRaw),
       HEq someTerm (Term.codataUnfold initialState transition) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.codataUnfold stateRaw transitionRaw)),
        someType = Ty.codata stateType outputType →
        Σ' (initialState : Term context stateType stateRaw)
           (transition : Term context (Ty.arrow stateType outputType) transitionRaw),
           HEq genericTerm (Term.codataUnfold initialState transition) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsCodata
  cases genericTerm
  rename_i innerState innerOutput initialState transition
  have codataEq := Ty.codata.inj someTypeIsCodata
  cases codataEq.1
  cases codataEq.2
  exact ⟨initialState, transition, HEq.rfl⟩

/-! ## Tier 3 — eliminator lifts with shallow β (single-child)

Single-Term-child eliminators where β fires when the child is the
matching canonical introducer.  Two-arm raw inversion: cong + β-deep.

Recipe per β-firing eliminator:
  rcases <head>_inv rawStep with
    ⟨..., eq, congStep⟩
    | ⟨..., eq, βStep⟩
  case 1 (cong arm): apply childLift to congStep, wrap with Step.par.<elim>Cong
  case 2 (β arm): apply childLift to βStep (which yields a Term at
    canonical type), use the corresponding destructor to extract
    the canonical payload, then apply Step.par.beta<elim><Intro>Deep -/

/-- **Tier 3 — Term.transp lift, cong arm only.**  The transp_inv has
3 disjuncts: cong + transpReflBeta (constant-pathLam fires) +
transpReflBetaDeep.  The β arms require the path argument to develop
to a `RawTerm.pathLam typeRaw.weaken` form — checking this at the
typed level requires alignment between the pathLam's body-raw and the
schematic typeRaw payload, deferred. -/
theorem RawStep.par.lift_transp_cong
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    (typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term context sourceType sourceRaw)
    (typePathLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pathRaw targetRawIH →
      ∃ typePathTarget :
          Term context
            (Ty.path (Ty.universe universeLevel universeLevelLt)
              sourceTypeRaw targetTypeRaw)
            targetRawIH,
        Step.par typePath typePathTarget)
    (sourceValueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par sourceRaw targetRawIH →
      ∃ sourceValueTarget : Term context sourceType targetRawIH,
        Step.par sourceValue sourceValueTarget)
    {pathTargetRaw sourceTargetRaw : RawTerm scope}
    (pathStep : RawStep.par pathRaw pathTargetRaw)
    (sourceStep : RawStep.par sourceRaw sourceTargetRaw) :
    ∃ targetTerm :
        Term context targetType (RawTerm.transp pathTargetRaw sourceTargetRaw),
      Step.par
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType sourceTypeRaw targetTypeRaw typePath sourceValue)
        targetTerm := by
  obtain ⟨typePathTarget, typePathStepTyped⟩ := typePathLift pathStep
  obtain ⟨sourceValueTarget, sourceValueStepTyped⟩ := sourceValueLift sourceStep
  exact ⟨Term.transp modeIsUnivalent universeLevel universeLevelLt
                     sourceType targetType
                     sourceTypeRaw targetTypeRaw typePathTarget sourceValueTarget,
         Step.par.transpCong modeIsUnivalent universeLevel universeLevelLt
                             sourceType targetType sourceTypeRaw targetTypeRaw
                             typePathStepTyped sourceValueStepTyped⟩

/-- **Tier 3 — Term.pathApp lift, cong arm only.**  The β-arms
(betaPathApp / betaPathReflApp) require body-substitution casts —
deferred per the lift_app comment. -/
theorem RawStep.par.lift_pathApp_cong
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw)
    (pathLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pathRaw targetRawIH →
      ∃ pathTarget :
          Term context (Ty.path carrierType leftEndpoint rightEndpoint) targetRawIH,
        Step.par pathTerm pathTarget)
    (intervalLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par intervalRaw targetRawIH →
      ∃ intervalTarget : Term context Ty.interval targetRawIH,
        Step.par intervalTerm intervalTarget)
    {pathTargetRaw intervalTargetRaw : RawTerm scope}
    (pathStep : RawStep.par pathRaw pathTargetRaw)
    (intervalStep : RawStep.par intervalRaw intervalTargetRaw) :
    ∃ targetTerm :
        Term context carrierType (RawTerm.pathApp pathTargetRaw intervalTargetRaw),
      Step.par (Term.pathApp modeIsUnivalent pathTerm intervalTerm) targetTerm := by
  obtain ⟨pathTarget, pathStepTyped⟩ := pathLift pathStep
  obtain ⟨intervalTarget, intervalStepTyped⟩ := intervalLift intervalStep
  exact ⟨Term.pathApp modeIsUnivalent pathTarget intervalTarget,
         Step.par.pathApp modeIsUnivalent pathStepTyped intervalStepTyped⟩

/-- **Tier 3 — Term.appPi lift, cong arm only.**  Source/target Ty
shapes are identical (both `codomainType.subst0 domainType <argRaw>`)
when the function step is non-β; the β arm has the same cast wall as
`lift_app` (deferred). -/
theorem RawStep.par.lift_appPi_cong
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par functionRaw targetRawIH →
      ∃ functionTarget :
          Term context (Ty.piTy domainType codomainType) targetRawIH,
        Step.par functionTerm functionTarget)
    (argumentLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentRaw targetRawIH →
      ∃ argumentTarget : Term context domainType targetRawIH,
        Step.par argumentTerm argumentTarget)
    {functionTargetRaw argumentTargetRaw : RawTerm scope}
    (functionStep : RawStep.par functionRaw functionTargetRaw)
    (argumentStep : RawStep.par argumentRaw argumentTargetRaw) :
    ∃ targetTerm :
        Term context (codomainType.subst0 domainType argumentTargetRaw)
                     (RawTerm.app functionTargetRaw argumentTargetRaw),
      Step.par (Term.appPi functionTerm argumentTerm) targetTerm := by
  obtain ⟨functionTarget, functionStepTyped⟩ := functionLift functionStep
  obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
  exact ⟨Term.appPi functionTarget argumentTarget,
         Step.par.appPi functionStepTyped argumentStepTyped⟩

/-- **Tier 3 — Term.app lift, cong arm only.**  The β arm of
`RawStep.par.app_inv` requires casting between `codomainType.weaken.
subst0 ...` and `codomainType` (related by
`Ty.weaken_subst_singleton`); the `▸`-rewrite propagates through the
existential's type binder.  A clean solution requires a HEq-shaped
existential or a more flexible cast helper — deferred to a future
phase.

This cong-only variant covers the case where `RawStep.par fnRaw
fnTargetRaw` does NOT reach a `RawTerm.lam` form — which is the
shape of every non-β raw step from `RawTerm.app`.  Specifically, when
the function's raw step is `refl` or any `app`-cong, the βApp arm of
the inversion does not fire; only the cong arm fires.

For the general case (including β-firing), use a richer headline that
allows the target Ty to differ via HEq — pending. -/
theorem RawStep.par.lift_app_cong
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par functionRaw targetRawIH →
      ∃ functionTarget :
          Term context (Ty.arrow domainType codomainType) targetRawIH,
        Step.par functionTerm functionTarget)
    (argumentLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentRaw targetRawIH →
      ∃ argumentTarget : Term context domainType targetRawIH,
        Step.par argumentTerm argumentTarget)
    {functionTargetRaw argumentTargetRaw : RawTerm scope}
    (functionStep : RawStep.par functionRaw functionTargetRaw)
    (argumentStep : RawStep.par argumentRaw argumentTargetRaw) :
    ∃ targetTerm :
        Term context codomainType (RawTerm.app functionTargetRaw argumentTargetRaw),
      Step.par (Term.app functionTerm argumentTerm) targetTerm := by
  obtain ⟨functionTarget, functionStepTyped⟩ := functionLift functionStep
  obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
  exact ⟨Term.app functionTarget argumentTarget,
         Step.par.app functionStepTyped argumentStepTyped⟩
theorem RawStep.par.lift_modElim
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.modElim innerRaw) targetRaw) :
    ∃ targetTerm : Term context innerType targetRaw,
      Step.par (Term.modElim innerTerm) targetTerm := by
  rcases RawStep.par.modElim_inv rawStep with
    ⟨innerTargetRaw, eq, innerStep⟩
    | ⟨payloadTarget, eq, innerToModIntro⟩
  · obtain ⟨innerTarget, innerStepTyped⟩ := innerLift innerStep
    cases eq
    exact ⟨Term.modElim innerTarget, Step.par.modElim innerStepTyped⟩
  · obtain ⟨innerCanonical, innerStepTyped⟩ := innerLift innerToModIntro
    obtain ⟨payload, payloadHeq⟩ := Term.modIntroDestruct innerCanonical
    have payloadEq : innerCanonical = Term.modIntro payload := eq_of_heq payloadHeq
    rw [payloadEq] at innerStepTyped
    cases eq
    exact ⟨payload, Step.par.betaModElimIntroDeep innerStepTyped⟩

/-- **Tier 3 — Term.recordProj lift.**  Two-arm: cong + betaRecordProjIntro. -/
theorem RawStep.par.lift_recordProj
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw)
    (recordLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par recordRaw targetRawIH →
      ∃ recordTarget :
          Term context (Ty.record singleFieldType) targetRawIH,
        Step.par recordValue recordTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.recordProj recordRaw) targetRaw) :
    ∃ targetTerm : Term context singleFieldType targetRaw,
      Step.par (Term.recordProj recordValue) targetTerm := by
  rcases RawStep.par.recordProj_inv rawStep with
    ⟨recordTargetRaw, eq, recordStep⟩
    | ⟨firstTarget, eq, recordToIntro⟩
  · obtain ⟨recordTarget, recordStepTyped⟩ := recordLift recordStep
    cases eq
    exact ⟨Term.recordProj recordTarget, Step.par.recordProjCong recordStepTyped⟩
  · obtain ⟨recordCanonical, recordStepTyped⟩ := recordLift recordToIntro
    obtain ⟨firstField, firstHeq⟩ := Term.recordIntroDestruct recordCanonical
    have firstEq : recordCanonical = Term.recordIntro firstField := eq_of_heq firstHeq
    rw [firstEq] at recordStepTyped
    cases eq
    exact ⟨firstField, Step.par.betaRecordProjIntroDeep recordStepTyped⟩

/-- **Tier 3 — Term.refineElim lift.**  Two-arm: cong + betaRefineElimIntro.
The β arm extracts the typed value from a Term.refineIntro. -/
theorem RawStep.par.lift_refineElim
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (refinedLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par refinedRaw targetRawIH →
      ∃ refinedTarget :
          Term context (Ty.refine baseType predicate) targetRawIH,
        Step.par refinedValue refinedTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refineElim refinedRaw) targetRaw) :
    ∃ targetTerm : Term context baseType targetRaw,
      Step.par (Term.refineElim refinedValue) targetTerm := by
  rcases RawStep.par.refineElim_inv rawStep with
    ⟨refinedTargetRaw, eq, refinedStep⟩
    | ⟨valueTarget, proofTarget, eq, refinedToIntro⟩
  · obtain ⟨refinedTarget, refinedStepTyped⟩ := refinedLift refinedStep
    cases eq
    exact ⟨Term.refineElim refinedTarget,
           Step.par.refineElimCong refinedStepTyped⟩
  · obtain ⟨refinedCanonical, refinedStepTyped⟩ := refinedLift refinedToIntro
    obtain ⟨baseValue, predicateProof, valueHeq⟩ :=
      Term.refineIntroDestruct predicate refinedCanonical
    have valueEq :
        refinedCanonical = Term.refineIntro predicate baseValue predicateProof :=
      eq_of_heq valueHeq
    rw [valueEq] at refinedStepTyped
    cases eq
    exact ⟨baseValue, Step.par.betaRefineElimIntroDeep refinedStepTyped⟩

/-- **Tier 3 — Term.glueElim lift.**  Two-arm: cong + betaGlueElimIntro.
The β arm extracts the typed base from a Term.glueIntro. -/
theorem RawStep.par.lift_glueElim
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {gluedRaw : RawTerm scope}
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par gluedRaw targetRawIH →
      ∃ gluedTarget :
          Term context (Ty.glue baseType boundaryWitness) targetRawIH,
        Step.par gluedValue gluedTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.glueElim gluedRaw) targetRaw) :
    ∃ targetTerm : Term context baseType targetRaw,
      Step.par (Term.glueElim modeIsUnivalent gluedValue) targetTerm := by
  rcases RawStep.par.glueElim_inv rawStep with
    ⟨gluedTargetRaw, eq, gluedStep⟩
    | ⟨baseTarget, partialTarget, eq, gluedToIntro⟩
  · obtain ⟨gluedTarget, gluedStepTyped⟩ := gluedLift gluedStep
    cases eq
    exact ⟨Term.glueElim modeIsUnivalent gluedTarget,
           Step.par.glueElimCong modeIsUnivalent gluedStepTyped⟩
  · obtain ⟨gluedCanonical, gluedStepTyped⟩ := gluedLift gluedToIntro
    obtain ⟨baseValue, partialValue, glueHeq⟩ :=
      Term.glueIntroDestruct modeIsUnivalent baseType boundaryWitness gluedCanonical
    have glueEq :
        gluedCanonical = Term.glueIntro modeIsUnivalent baseType boundaryWitness
                                        baseValue partialValue :=
      eq_of_heq glueHeq
    rw [glueEq] at gluedStepTyped
    cases eq
    exact ⟨baseValue, Step.par.betaGlueElimIntroDeep modeIsUnivalent gluedStepTyped⟩

/-- **Tier 3 — Term.codataDest lift.**  Two-arm: cong + betaCodataDestUnfold.
The β arm extracts the typed initial state and transition from a
Term.codataUnfold; the iota target is `app transition initialState`. -/
theorem RawStep.par.lift_codataDest
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw)
    (codataLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par codataRaw targetRawIH →
      ∃ codataTarget :
          Term context (Ty.codata stateType outputType) targetRawIH,
        Step.par codataValue codataTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.codataDest codataRaw) targetRaw) :
    ∃ targetTerm : Term context outputType targetRaw,
      Step.par (Term.codataDest codataValue) targetTerm := by
  rcases RawStep.par.codataDest_inv rawStep with
    ⟨codataTargetRaw, eq, codataStep⟩
    | ⟨stateTarget, transitionTarget, eq, codataToUnfold⟩
  · obtain ⟨codataTarget, codataStepTyped⟩ := codataLift codataStep
    cases eq
    exact ⟨Term.codataDest codataTarget,
           Step.par.codataDestCong codataStepTyped⟩
  · obtain ⟨codataCanonical, codataStepTyped⟩ := codataLift codataToUnfold
    obtain ⟨initialState, transition, codataHeq⟩ :=
      Term.codataUnfoldDestruct codataCanonical
    have codataEq :
        codataCanonical = Term.codataUnfold initialState transition :=
      eq_of_heq codataHeq
    rw [codataEq] at codataStepTyped
    cases eq
    exact ⟨Term.app transition initialState,
           Step.par.betaCodataDestUnfoldDeep codataStepTyped⟩

/-! ## β cast wall demolition — full lifts via two-Ty existential

The fixed-target-Ty existential used by `lift_app_cong`,
`lift_appPi_cong`, `lift_pathApp_cong`, `lift_transp_cong` cannot
absorb the β arms of `app`, `appPi`, `pathApp`, `transp` because the
target Term's Ty index is `codomainType.weaken.subst0 substituent
argRaw` — propositionally equal to `codomainType` via
`Ty.weaken_subst_singleton`, but the `▸` cast propagates through the
existential's other Ty indices.

The fix: generalize the headline existential over the target Ty.
`Step.par`'s native two-Ty signature `{sourceType targetType : Ty
level scope}` accommodates this directly.

```
∃ (targetTy : Ty level scope) (targetTerm : Term context targetTy targetRaw),
  Step.par sourceTerm targetTerm
```

Each `lift_full_<ctor>` lemma uses this two-Ty existential and
absorbs both the cong arm and any β/ι arms uniformly.  When
assembled into the headline `Term.preserves`, the IH has the same
two-Ty shape, and child lifts are typed at the two-Ty existential
form. -/

/-- **β cast wall demolition — Term.app full lift.**  Two-Ty
existential absorbs both the cong arm (target at `codomainType`) and
the β-deep arm (target at `codomainType.weaken.subst0 ...` via
`Term.subst0`).  The function IH stays at fixed `Ty.arrow domainType
codomainType` — the function's type is invariant under reduction at
arrow type.  The argument IH stays at fixed `domainType`. -/
theorem RawStep.par.lift_full_app
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par functionRaw targetRawIH →
      ∃ functionTarget :
          Term context (Ty.arrow domainType codomainType) targetRawIH,
        Step.par functionTerm functionTarget)
    (argumentLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentRaw targetRawIH →
      ∃ argumentTarget : Term context domainType targetRawIH,
        Step.par argumentTerm argumentTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.app functionRaw argumentRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.app functionTerm argumentTerm) targetTerm := by
  rcases RawStep.par.app_inv rawStep with
    ⟨functionTargetRaw, argumentTargetRaw, eq, functionStep, argumentStep⟩
    | ⟨bodyTargetRaw, argumentTargetRaw, eq, functionToLam, argumentStep⟩
  · -- cong arm
    obtain ⟨functionTarget, functionStepTyped⟩ := functionLift functionStep
    obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
    cases eq
    exact ⟨codomainType, Term.app functionTarget argumentTarget,
           Step.par.app functionStepTyped argumentStepTyped⟩
  · -- β-deep arm: function raw-reduces to lam bodyTargetRaw
    obtain ⟨functionCanonical, functionStepTyped⟩ := functionLift functionToLam
    obtain ⟨argumentTarget, argumentStepTyped⟩ := argumentLift argumentStep
    -- functionCanonical : Term ctx (Ty.arrow domainType codomainType) (RawTerm.lam bodyTargetRaw)
    -- Use lamDestruct to extract the body
    obtain ⟨bodyTerm, bodyHeq⟩ := Term.lamDestruct functionCanonical
    have bodyEq : functionCanonical = Term.lam (codomainType := codomainType) bodyTerm :=
      eq_of_heq bodyHeq
    rw [bodyEq] at functionStepTyped
    cases eq
    refine ⟨codomainType.weaken.subst0 domainType argumentTargetRaw,
            Term.subst0 bodyTerm argumentTarget, ?_⟩
    exact Step.par.betaAppDeep
            (functionRawSource := bodyTargetRaw)
            functionStepTyped argumentStepTyped

/-- Destructor for `Term.pathLam`.  `RawTerm.pathLam bodyRaw` is
produced uniquely by `Term.pathLam`. -/
def Term.pathLamDestruct
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    (someTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
                   (RawTerm.pathLam bodyRaw)) :
    Σ' (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw),
       HEq someTerm
            (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                          body) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.pathLam bodyRaw)),
        someType = Ty.path carrierType leftEndpoint rightEndpoint →
        Σ' (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw),
           HEq genericTerm
                (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                              body) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsPath
  cases genericTerm
  rename_i innerMode innerCarrier innerLeft innerRight body
  have pathEq := Ty.path.inj someTypeIsPath
  cases pathEq.1
  cases pathEq.2.1
  cases pathEq.2.2
  exact ⟨body, HEq.rfl⟩

/-- **β cast wall demolition — Term.pathApp full lift.**  Two-Ty
existential absorbs both the cong arm (target at `carrierType`) and
the β-deep arm (target via `Term.subst0` at `carrierType.weaken.subst0
Ty.interval intervalTargetRaw`).  Per pathApp_inv, both betaPathApp
and betaPathReflApp arms route through the "path develops to pathLam"
disjunct, so we need only handle cong + pathLam-shape β. -/
theorem RawStep.par.lift_full_pathApp
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw)
    (pathLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pathRaw targetRawIH →
      ∃ pathTarget :
          Term context (Ty.path carrierType leftEndpoint rightEndpoint) targetRawIH,
        Step.par pathTerm pathTarget)
    (intervalLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par intervalRaw targetRawIH →
      ∃ intervalTarget : Term context Ty.interval targetRawIH,
        Step.par intervalTerm intervalTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.pathApp pathRaw intervalRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.pathApp modeIsUnivalent pathTerm intervalTerm) targetTerm := by
  rcases RawStep.par.pathApp_inv rawStep with
    ⟨pathTargetRaw, intervalTargetRaw, eq, pathStep, intervalStep⟩
    | ⟨bodyTargetRaw, intervalTargetRaw, eq, pathToLam, intervalStep⟩
  · -- cong arm
    obtain ⟨pathTarget, pathStepTyped⟩ := pathLift pathStep
    obtain ⟨intervalTarget, intervalStepTyped⟩ := intervalLift intervalStep
    cases eq
    refine ⟨carrierType, Term.pathApp modeIsUnivalent pathTarget intervalTarget, ?_⟩
    exact Step.par.pathApp modeIsUnivalent pathStepTyped intervalStepTyped
  · -- β-deep arm: path raw-reduces to pathLam bodyTargetRaw
    obtain ⟨pathCanonical, pathStepTyped⟩ := pathLift pathToLam
    obtain ⟨intervalTarget, intervalStepTyped⟩ := intervalLift intervalStep
    -- pathCanonical : Term ctx (Ty.path ...) (RawTerm.pathLam bodyTargetRaw)
    obtain ⟨bodyTerm, bodyHeq⟩ :=
      Term.pathLamDestruct modeIsUnivalent carrierType leftEndpoint rightEndpoint
                           pathCanonical
    have bodyEq :
        pathCanonical =
          Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                       bodyTerm :=
      eq_of_heq bodyHeq
    rw [bodyEq] at pathStepTyped
    cases eq
    refine ⟨carrierType.weaken.subst0 Ty.interval intervalTargetRaw,
            Term.subst0 bodyTerm intervalTarget, ?_⟩
    exact Step.par.betaPathAppDeep modeIsUnivalent
            (pathSource := pathTerm) (bodyTarget := bodyTerm)
            pathStepTyped intervalStepTyped

/-- Destructor for `Term.refl` at fixed `Ty.id carrier endpoint endpoint`.
Extracts an `Eq` between the witness raw and the endpoint, since
`Term.refl c w : Ty.id c w w` forces both endpoints = w. -/
def Term.reflDestruct
    {carrier : Ty level scope}
    {endpoint : RawTerm scope}
    {rawWitness : RawTerm scope}
    (someTerm :
      Term context (Ty.id carrier endpoint endpoint) (RawTerm.refl rawWitness)) :
    PLift (rawWitness = endpoint) := by
  -- Term.refl forces both endpoints equal to its rawWitness arg, so
  -- having the type say endpoint endpoint and the raw say rawWitness,
  -- we get rawWitness = endpoint by ctor inversion.
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.refl rawWitness)),
        someType = Ty.id carrier endpoint endpoint →
        PLift (rawWitness = endpoint) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsIdRefl
  cases genericTerm
  rename_i innerCarrier
  -- innerCarrier : Ty level scope; the ctor's type is
  --   Ty.id innerCarrier rawWitness rawWitness
  -- which equals (per someTypeIsIdRefl) Ty.id carrier endpoint endpoint.
  have idEq := Ty.id.inj someTypeIsIdRefl
  -- idEq.2.1 : rawWitness = endpoint (left endpoint match)
  exact ⟨idEq.2.1⟩

/-- Destructor for `Term.refl` at type `Ty.id carrier leftEndpoint
rightEndpoint` with raw `RawTerm.refl witnessRaw`.  Forces leftEndpoint
= rightEndpoint = witnessRaw and yields HEq alignment. -/
def Term.idReflDestruct
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint)
                   (RawTerm.refl witnessRaw)) :
    Σ' (witnessEqLeft : witnessRaw = leftEndpoint)
       (witnessEqRight : witnessRaw = rightEndpoint),
       HEq someTerm
            (Term.refl (context := context) carrier witnessRaw) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.refl witnessRaw)),
        someType = Ty.id carrier leftEndpoint rightEndpoint →
        Σ' (witnessEqLeft : witnessRaw = leftEndpoint)
           (witnessEqRight : witnessRaw = rightEndpoint),
           HEq genericTerm
                (Term.refl (context := context) carrier witnessRaw) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsId
  cases genericTerm
  rename_i innerCarrier
  have idEq := Ty.id.inj someTypeIsId
  cases idEq.1
  exact ⟨idEq.2.1, idEq.2.2, HEq.rfl⟩

/-! ## Σ-type ctors — fst, snd, pair (heterogeneous via two-Ty existential) -/

/-- **β cast wall demolition — Term.fst full lift.**  The fst target
type is `firstType` (constant); two-Ty form chosen for headline
parity.  Two-arm raw inversion: cong + β-deep (pair). -/
theorem RawStep.par.lift_full_fst
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pairRaw targetRawIH →
      ∃ pairTarget : Term context (Ty.sigmaTy firstType secondType) targetRawIH,
        Step.par pairTerm pairTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.fst pairRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.fst (secondType := secondType) pairTerm) targetTerm := by
  rcases RawStep.par.fst_inv rawStep with
    ⟨pairTargetRaw, eq, pairStep⟩
    | ⟨firstTargetRaw, secondTargetRaw, eq, pairToPair⟩
  · -- cong arm
    obtain ⟨pairTarget, pairStepTyped⟩ := pairLift pairStep
    cases eq
    refine ⟨firstType, Term.fst (secondType := secondType) pairTarget, ?_⟩
    exact Step.par.fst pairStepTyped
  · -- β-deep arm: pair raw-reduces to RawTerm.pair firstTargetRaw secondTargetRaw
    obtain ⟨pairCanonical, pairStepTyped⟩ := pairLift pairToPair
    obtain ⟨firstValue, secondValue, pairHeq⟩ := Term.pairDestruct pairCanonical
    have pairEq : pairCanonical = Term.pair firstValue secondValue := eq_of_heq pairHeq
    rw [pairEq] at pairStepTyped
    cases eq
    refine ⟨firstType, firstValue, ?_⟩
    exact Step.par.betaFstPairDeep pairStepTyped

/-- **β cast wall demolition — Term.snd full lift.**  The snd target
type is `secondType.subst0 firstType (RawTerm.fst pairRaw)`, then
after the cong arm, becomes `secondType.subst0 firstType (RawTerm.fst
pairTargetRaw)`; the two-Ty existential absorbs this gap.  In the β
arm, the snd target is the second component of the pair, at type
`secondType.subst0 firstType firstRawTarget` — different from
`secondType.subst0 firstType (RawTerm.fst pairRaw)` propositionally
but the existential lets us state the lift uniformly. -/
theorem RawStep.par.lift_full_snd
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pairRaw targetRawIH →
      ∃ pairTarget : Term context (Ty.sigmaTy firstType secondType) targetRawIH,
        Step.par pairTerm pairTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.snd pairRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.snd (secondType := secondType) pairTerm) targetTerm := by
  rcases RawStep.par.snd_inv rawStep with
    ⟨pairTargetRaw, eq, pairStep⟩
    | ⟨firstTargetRaw, secondTargetRaw, eq, pairToPair⟩
  · -- cong arm
    obtain ⟨pairTarget, pairStepTyped⟩ := pairLift pairStep
    cases eq
    refine ⟨secondType.subst0 firstType (RawTerm.fst pairTargetRaw),
            Term.snd (secondType := secondType) pairTarget, ?_⟩
    exact Step.par.snd pairStepTyped
  · -- β-deep arm: pair raw-reduces to RawTerm.pair firstTargetRaw secondTargetRaw
    obtain ⟨pairCanonical, pairStepTyped⟩ := pairLift pairToPair
    obtain ⟨firstValue, secondValue, pairHeq⟩ := Term.pairDestruct pairCanonical
    have pairEq : pairCanonical = Term.pair firstValue secondValue := eq_of_heq pairHeq
    rw [pairEq] at pairStepTyped
    cases eq
    refine ⟨secondType.subst0 firstType firstTargetRaw, secondValue, ?_⟩
    exact Step.par.betaSndPairDeep pairStepTyped

/-! ## Identity-type elimination — idJ, oeqJ, idStrictRec via two-Ty existential

These eliminators have a constant `motiveType` (at scope, NOT scope+1),
so the cong arm produces a target at `motiveType` directly.  The
iota-refl arm requires the witness to typed-reduce to a `Term.refl
carrier endpoint`, which forces `leftEndpoint = rightEndpoint`
(`Term.refl c w : Ty.id c w w`).  We extract this equality via the
witness IH + reflDestruct, then dispatch through the deep iota rule. -/

/-- **β cast wall demolition — Term.idJ full lift.**  Two-arm raw
inversion: cong + iotaIdJReflDeep.  In the iota arm, the witness IH
produces a Term at `Ty.id carrier leftEndpoint rightEndpoint` with raw
`RawTerm.refl witnessRaw'`.  By Term.refl's typing, this forces
`leftEndpoint = rightEndpoint = witnessRaw'`.  We then apply
`Step.par.iotaIdJReflDeep`. -/
theorem RawStep.par.lift_full_idJ
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context motiveType targetRawIH,
        Step.par baseCase baseTarget)
    (witnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par witnessRaw targetRawIH →
      ∃ witnessTarget :
          Term context (Ty.id carrier leftEndpoint rightEndpoint) targetRawIH,
        Step.par witness witnessTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.idJ baseRaw witnessRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.idJ baseCase witness) targetTerm := by
  rcases RawStep.par.idJ_inv rawStep with
    ⟨baseTargetRaw, witnessTargetRaw, eq, baseStep, witnessStep⟩
    | ⟨witnessRaw', baseTargetRaw, eq, witnessToRefl, baseStep⟩
  · -- cong arm
    obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
    obtain ⟨witnessTarget, witnessStepTyped⟩ := witnessLift witnessStep
    cases eq
    refine ⟨motiveType, Term.idJ baseTarget witnessTarget, ?_⟩
    exact Step.par.idJ baseStepTyped witnessStepTyped
  · -- iota arm: witness raw-reduces to RawTerm.refl witnessRaw'
    obtain ⟨witnessCanonical, witnessStepTyped⟩ := witnessLift witnessToRefl
    obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
    cases eq
    refine ⟨motiveType, baseTarget, ?_⟩
    -- The typed IH gives witnessCanonical : Term ctx (Ty.id carrier left right)
    --                                              (RawTerm.refl witnessRaw').
    -- Term.refl_ty_inv says the type-shape forces witnessRaw' = left = right.
    -- We extract this via a destructor that returns a fresh Term.refl-shape
    -- target along with HEq alignment.
    --
    -- The cleanest approach: use a destructor that yields directly a
    -- Step.par witness (Term.refl carrier endpoint) for some endpoint
    -- = leftEndpoint = rightEndpoint.
    --
    -- We use a pre-extraction lemma `Term.idReflDestruct` that takes
    -- a Term at Ty.id with refl-raw and returns a triple (leftEqWitness,
    -- rightEqWitness, witnessAsTermRefl_via_HEq).
    obtain ⟨witnessRawEqLeft, witnessRawEqRight, witnessHeq⟩ :=
      Term.idReflDestruct witnessCanonical
    cases witnessRawEqLeft
    cases witnessRawEqRight
    -- Now witnessRaw' = leftEndpoint = rightEndpoint, and witnessHeq is
    -- HEq witnessCanonical (Term.refl carrier leftEndpoint).
    have witnessEq : witnessCanonical = Term.refl carrier leftEndpoint :=
      eq_of_heq witnessHeq
    rw [witnessEq] at witnessStepTyped
    exact Step.par.iotaIdJReflDeep witnessStepTyped baseStepTyped

/-- **β cast wall demolition — Term.oeqJ full lift.**  Only one
inversion arm (cong); no iota at the raw level for oeqJ. -/
theorem RawStep.par.lift_full_oeqJ
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context motiveType targetRawIH,
        Step.par baseCase baseTarget)
    (witnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par witnessRaw targetRawIH →
      ∃ witnessTarget :
          Term context (Ty.oeq carrier leftEndpoint rightEndpoint) targetRawIH,
        Step.par witness witnessTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.oeqJ baseRaw witnessRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.oeqJ baseCase witness) targetTerm := by
  obtain ⟨baseTargetRaw, witnessTargetRaw, eq, baseStep, witnessStep⟩ :=
    RawStep.par.oeqJ_inv rawStep
  obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
  obtain ⟨witnessTarget, witnessStepTyped⟩ := witnessLift witnessStep
  cases eq
  refine ⟨motiveType, Term.oeqJ baseTarget witnessTarget, ?_⟩
  exact Step.par.oeqJCong baseStepTyped witnessStepTyped

/-- Destructor for `Term.idStrictRefl` at type `Ty.idStrict carrier
leftEndpoint rightEndpoint` with raw `RawTerm.idStrictRefl witnessRaw`. -/
def Term.idStrictReflDestruct
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
                   (RawTerm.idStrictRefl witnessRaw)) :
    Σ' (witnessEqLeft : witnessRaw = leftEndpoint)
       (witnessEqRight : witnessRaw = rightEndpoint),
       HEq someTerm
            (Term.idStrictRefl (context := context) modeIsStrict carrier
                               witnessRaw) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.idStrictRefl witnessRaw)),
        someType = Ty.idStrict carrier leftEndpoint rightEndpoint →
        Σ' (witnessEqLeft : witnessRaw = leftEndpoint)
           (witnessEqRight : witnessRaw = rightEndpoint),
           HEq genericTerm
                (Term.idStrictRefl (context := context) modeIsStrict carrier
                                   witnessRaw) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsIdStrict
  cases genericTerm
  rename_i innerMode innerCarrier
  have idStrictEq := Ty.idStrict.inj someTypeIsIdStrict
  cases idStrictEq.1
  exact ⟨idStrictEq.2.1, idStrictEq.2.2, HEq.rfl⟩

/-- **β cast wall demolition — Term.idStrictRec full lift.**  Two-arm
raw inversion: cong + iotaIdStrictRecRefl.  In iota arm, the witness IH
gives a Term at Ty.idStrict carrier left right with idStrictRefl-raw,
which by typing forces left = right = witnessRaw'. -/
theorem RawStep.par.lift_full_idStrictRec
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context motiveType targetRawIH,
        Step.par baseCase baseTarget)
    (witnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par witnessRaw targetRawIH →
      ∃ witnessTarget :
          Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) targetRawIH,
        Step.par witness witnessTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.idStrictRec baseRaw witnessRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.idStrictRec modeIsStrict baseCase witness) targetTerm := by
  rcases RawStep.par.idStrictRec_inv rawStep with
    ⟨baseTargetRaw, witnessTargetRaw, eq, baseStep, witnessStep⟩
    | ⟨witnessRaw', baseTargetRaw, eq, witnessToRefl, baseStep⟩
  · -- cong arm
    obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
    obtain ⟨witnessTarget, witnessStepTyped⟩ := witnessLift witnessStep
    cases eq
    refine ⟨motiveType, Term.idStrictRec modeIsStrict baseTarget witnessTarget, ?_⟩
    exact Step.par.idStrictRecCong modeIsStrict baseStepTyped witnessStepTyped
  · -- iota arm: witness raw-reduces to RawTerm.idStrictRefl witnessRaw'
    obtain ⟨witnessCanonical, witnessStepTyped⟩ := witnessLift witnessToRefl
    obtain ⟨baseTarget, baseStepTyped⟩ := baseLift baseStep
    cases eq
    obtain ⟨witnessRawEqLeft, witnessRawEqRight, witnessHeq⟩ :=
      Term.idStrictReflDestruct modeIsStrict witnessCanonical
    cases witnessRawEqLeft
    cases witnessRawEqRight
    have witnessEq : witnessCanonical =
        Term.idStrictRefl modeIsStrict carrier leftEndpoint :=
      eq_of_heq witnessHeq
    rw [witnessEq] at witnessStepTyped
    refine ⟨motiveType, baseTarget, ?_⟩
    exact Step.par.iotaIdStrictRecReflDeep modeIsStrict
            witnessStepTyped baseStepTyped

/-! ## Type-changing motive — boolElim via two-Ty existential

`Term.boolElim`'s motive lives at scope+1 (`motiveType : Ty level (scope
+ 1)`) and the boolElim's result type is `motiveType.subst0 Ty.bool
scrutineeRaw`.  After scrutinee steps to scrutineeTargetRaw, the result
type changes to `motiveType.subst0 Ty.bool scrutineeTargetRaw`.  The
two-Ty existential absorbs this gap. -/

/-- **Type-changing motive wall demolition — Term.boolElim full lift.**
Three-arm raw inversion: cong + iotaBoolElimTrueDeep + iotaBoolElimFalseDeep. -/
theorem RawStep.par.lift_full_boolElim
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.bool targetRawIH,
        Step.par scrutinee scrutTarget)
    (thenLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par thenRaw targetRawIH →
      ∃ thenTarget :
          Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) targetRawIH,
        Step.par thenBranch thenTarget)
    (elseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par elseRaw targetRawIH →
      ∃ elseTarget :
          Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) targetRawIH,
        Step.par elseBranch elseTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.boolElim scrutineeRaw thenRaw elseRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.boolElim (motiveType := motiveType) scrutinee thenBranch elseBranch)
        targetTerm := by
  rcases RawStep.par.boolElim_inv rawStep with
    ⟨scrutTargetRaw, thenTargetRaw, elseTargetRaw, eq, scrutStep, thenStep, elseStep⟩
    | ⟨thenTargetRaw, eq, scrutToTrue, thenStep⟩
    | ⟨elseTargetRaw, eq, scrutToFalse, elseStep⟩
  · -- cong arm
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨thenTarget, thenStepTyped⟩ := thenLift thenStep
    obtain ⟨elseTarget, elseStepTyped⟩ := elseLift elseStep
    cases eq
    refine ⟨motiveType.subst0 Ty.bool scrutTargetRaw,
            Term.boolElim scrutTarget thenTarget elseTarget, ?_⟩
    exact Step.par.boolElim scrutStepTyped thenStepTyped elseStepTyped
  · -- iotaBoolElimTrueDeep arm: scrutinee →* boolTrue
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToTrue
    obtain ⟨thenTarget, thenStepTyped⟩ := thenLift thenStep
    -- scrutTarget : Term ctx Ty.bool RawTerm.boolTrue → must be Term.boolTrue
    have heq :
        HEq scrutTarget (Term.boolTrue (context := context)) :=
      Term.boolTrue_unique scrutTarget Term.boolTrue
    have scrutEq : scrutTarget = (Term.boolTrue (context := context)) :=
      eq_of_heq heq
    rw [scrutEq] at scrutStepTyped
    cases eq
    refine ⟨motiveType.subst0 Ty.bool RawTerm.boolTrue, thenTarget, ?_⟩
    exact Step.par.iotaBoolElimTrueDeep elseBranch scrutStepTyped thenStepTyped
  · -- iotaBoolElimFalseDeep arm: scrutinee →* boolFalse
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToFalse
    obtain ⟨elseTarget, elseStepTyped⟩ := elseLift elseStep
    have heq :
        HEq scrutTarget (Term.boolFalse (context := context)) :=
      Term.boolFalse_unique scrutTarget Term.boolFalse
    have scrutEq : scrutTarget = (Term.boolFalse (context := context)) :=
      eq_of_heq heq
    rw [scrutEq] at scrutStepTyped
    cases eq
    refine ⟨motiveType.subst0 Ty.bool RawTerm.boolFalse, elseTarget, ?_⟩
    exact Step.par.iotaBoolElimFalseDeep thenBranch scrutStepTyped elseStepTyped

/-! ## Schematic-payload value ctors with typed cong rules

`Term.oeqRefl` and `Term.idStrictRefl` are schematic-payload value
ctors — their only Term-level computational content is a raw witness.
Both have typed Step.par cong rules (`oeqReflCong`, `idStrictReflCong`)
that take a `RawStep.par` on the witness raw and produce a typed
Step.par at heterogeneous source/target types (the carrier's left and
right endpoints both reduce in lockstep with the witness).

These lifts don't take a typed-IH parameter — the cong rule consumes
the raw step directly.  This makes them genuinely Tier 0.5 (atom-like
but with raw cong). -/

/-- **Term.oeqRefl full lift.**  No typed IH needed — `oeqReflCong`
takes the raw step directly. -/
theorem RawStep.par.lift_full_oeqRefl
    (carrier : Ty level scope) (rawWitness : RawTerm scope)
    (sourceTerm :
      Term context (Ty.oeq carrier rawWitness rawWitness)
                   (RawTerm.oeqRefl rawWitness))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.oeqRefl rawWitness) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨witnessTarget, eq, witnessStep⟩ := RawStep.par.oeqRefl_inv rawStep
  cases eq
  -- Use Term.oeqRefl_unique to align sourceTerm with the canonical Term.oeqRefl:
  -- Actually sourceTerm has type Ty.oeq carrier rawWitness rawWitness with raw
  -- RawTerm.oeqRefl rawWitness, which forces it to be Term.oeqRefl carrier rawWitness.
  -- But cases on sourceTerm would hit dep-elim wall; use a destructor.
  refine ⟨Ty.oeq carrier witnessTarget witnessTarget,
          Term.oeqRefl (context := context) carrier witnessTarget, ?_⟩
  -- Need: Step.par sourceTerm (Term.oeqRefl carrier witnessTarget)
  -- Use suffices to force sourceTerm to be Term.oeqRefl _ rawWitness:
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.oeqRefl rawWitness)),
        someType = Ty.oeq carrier rawWitness rawWitness →
        Step.par genericTerm
                 (Term.oeqRefl (context := context) carrier witnessTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsOeq
  cases genericTerm
  rename_i innerCarrier
  have oeqEq := Ty.oeq.inj someTypeIsOeq
  cases oeqEq.1
  exact Step.par.oeqReflCong witnessStep

/-- **Term.idStrictRefl full lift.** -/
theorem RawStep.par.lift_full_idStrictRefl
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope) (rawWitness : RawTerm scope)
    (sourceTerm :
      Term context (Ty.idStrict carrier rawWitness rawWitness)
                   (RawTerm.idStrictRefl rawWitness))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.idStrictRefl rawWitness) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨witnessTarget, eq, witnessStep⟩ := RawStep.par.idStrictRefl_inv rawStep
  cases eq
  refine ⟨Ty.idStrict carrier witnessTarget witnessTarget,
          Term.idStrictRefl (context := context) modeIsStrict carrier
                            witnessTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.idStrictRefl rawWitness)),
        someType = Ty.idStrict carrier rawWitness rawWitness →
        Step.par genericTerm
                 (Term.idStrictRefl (context := context) modeIsStrict carrier
                                    witnessTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsIdStrict
  cases genericTerm
  rename_i innerMode innerCarrier
  have idStrictEq := Ty.idStrict.inj someTypeIsIdStrict
  cases idStrictEq.1
  exact Step.par.idStrictReflCong modeIsStrict witnessStep

/-! ## Schematic-payload value ctors with new typed cong rules

`Term.refl carrier rawWitness`'s only computational content is the
schematic raw `rawWitness`.  `Step.par.reflCong` was added in the prior
juggernaut to lift `RawStep.par.reflCong` to the typed level: a raw step
on the witness produces a typed step on the wrapper.

`Term.funextRefl`, `Term.funextReflAtId`, `Term.funextIntroHet` follow
the same pattern with their respective new cong rules. -/

/-- **Term.refl full lift.**  No typed IH needed — `reflCong` consumes the
raw step directly.  Source type `Ty.id carrier rawWitness rawWitness`;
target type after step is `Ty.id carrier witnessTarget witnessTarget`. -/
theorem RawStep.par.lift_full_refl
    (carrier : Ty level scope) (rawWitness : RawTerm scope)
    (sourceTerm :
      Term context (Ty.id carrier rawWitness rawWitness)
                   (RawTerm.refl rawWitness))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refl rawWitness) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨witnessTarget, eq, witnessStep⟩ := RawStep.par.refl_inv rawStep
  cases eq
  refine ⟨Ty.id carrier witnessTarget witnessTarget,
          Term.refl (context := context) carrier witnessTarget, ?_⟩
  -- Force sourceTerm to be Term.refl _ rawWitness via free-the-type:
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.refl rawWitness)),
        someType = Ty.id carrier rawWitness rawWitness →
        Step.par genericTerm
                 (Term.refl (context := context) carrier witnessTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsId
  cases genericTerm
  rename_i innerCarrier
  have idEq := Ty.id.inj someTypeIsId
  cases idEq.1
  exact Step.par.reflCong carrier witnessStep

/-! ## Funext-family schematic-payload lifts

`Term.funextRefl`, `Term.funextReflAtId`, `Term.funextIntroHet` all
have raw form `RawTerm.lam (RawTerm.refl applyRaw)` (with applyRaw at
scope+1).  Their typed cong rules (added in the prior juggernaut)
take a raw step on applyRaw and produce a typed Step.par on the
wrapper.  Each lift uses lam_inv + refl_inv to extract the inner
applyRaw step from the raw target. -/

/-! ### Term.funextRefl full lift — DEFERRED

Term.funextRefl's raw form `RawTerm.lam (RawTerm.refl applyRaw)` is
SHARED with Term.lamPi (Term.refl ...) at the same Ty.piTy domainType
(Ty.id codomainType.weaken applyRaw applyRaw) type.  Both ctors
inhabit identical (typed × raw) signatures.  Generic lift dispatch
via `cases genericTerm` produces both arms; the lamPi case requires
constructing Step.par from Term.lamPi to Term.funextRefl, which is
NOT a Step.par cong rule (would require a "Term.lamPi-to-funextRefl"
ctor that ETA-equates the two structurally-distinct ctors).

A clean lift requires either:
1. A new Step.par ctor witnessing the two ctors are convertible (an
   eta-style rule for funextRefl).
2. A Term.unique lemma saying lamPi (refl ...) and funextRefl
   constructed at the same (Ty, raw) signature are HEq.
3. Restricting the headline existential to allow Term.lamPi witnesses
   (since they have identical raw shape, the down-stream confluence
   chain cares about raw, not syntactic Term).

Deferred to a separate commit alongside the headline assembly. -/

/-! ### Term.funextReflAtId full lift — DEFERRED

Term.funextReflAtId's raw form `RawTerm.lam (RawTerm.refl applyRaw)`
collides at the (Ty.id (Ty.arrow ...) ...) type with multiple Term
ctors (Term.lam, Term.lamPi, Term.funextRefl, Term.funextIntroHet).
The `cases genericTerm` + `all_goals first | nomatch | ...` pattern
that ALMOST works at the surface level was found to LEAK 2 axioms
(Quot.sound, propext) per the per-decl audit gate — the indexed-
inductive partial-match trap (memorized) fires on the multi-ctor
dispatch.

The fix requires using ctor-by-ctor explicit `casesOn` with motive,
or matching on raw projection via `Term.toRaw`-shape dispatch.  Both
are deferred to the headline assembly phase where the dispatch can
branch cleanly on Term ctor IDs. -/

/-! ### Term.funextIntroHet full lift — DEFERRED

Term.funextIntroHet's raw form `RawTerm.lam (RawTerm.refl applyARaw)`
is shape-collision with Term.funextReflAtId at Ty.id types — when the
applyARaw happens to be `RawTerm.refl applyRaw'`, both ctors have
identical (Ty, raw) signatures.  Generic dispatch surfaces both arms;
constructing a Step.par from Term.funextReflAtId to Term.funextIntroHet
is not a single Step.par ctor — it would require composing through
the eqArrow / eqArrowHet rules, which target funextRefl / funextRefl
respectively, not funextIntroHet directly.

Deferred to the headline assembly phase, where the dispatch can branch
on the actual source ctor and use ctor-specific Step.par rules. -/

/-! ## Atom-shaped value ctors (equivReflId, equivReflIdAtId)

`Term.equivReflId carrier` and `Term.equivReflIdAtId innerLevel innerLevelLt
carrier carrierRaw` are atom-shaped values with raw form
`RawTerm.equivIntro (lam (var 0)) (lam (var 0))`.  The id-lam bodies are
fixed `RawTerm.var 0`, which only refl-step.  Therefore the only raw
step from this composed shape is `refl`, and the typed lift returns the
source term itself with `Step.par.refl`. -/

/-- **Term.equivReflId full lift.**  Atom-shaped — only refl applies. -/
theorem RawStep.par.lift_full_equivReflId
    (carrier : Ty level scope)
    (sourceTerm :
      Term context (Ty.equiv carrier carrier)
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  -- The id-lam body is var 0; var only refl-steps; lam_inv yields target = lam (var 0).
  obtain ⟨forwardTarget, backwardTarget, eqOuter, forwardStep, backwardStep⟩ :=
    RawStep.par.equivIntro_inv rawStep
  obtain ⟨forwardBody, fEqLam, fBodyStep⟩ := RawStep.par.lam_inv forwardStep
  have fBodyVar := RawStep.par.var_inv fBodyStep
  cases fBodyVar
  cases fEqLam
  obtain ⟨backwardBody, bEqLam, bBodyStep⟩ := RawStep.par.lam_inv backwardStep
  have bBodyVar := RawStep.par.var_inv bBodyStep
  cases bBodyVar
  cases bEqLam
  cases eqOuter
  exact ⟨Ty.equiv carrier carrier, sourceTerm, Step.par.refl sourceTerm⟩

/-- **Term.equivReflIdAtId full lift.**  Atom-shaped — only refl applies. -/
theorem RawStep.par.lift_full_equivReflIdAtId
    (innerLevel : UniverseLevel) (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope) (carrierRaw : RawTerm scope)
    (sourceTerm :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw carrierRaw)
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨forwardTarget, backwardTarget, eqOuter, forwardStep, backwardStep⟩ :=
    RawStep.par.equivIntro_inv rawStep
  obtain ⟨forwardBody, fEqLam, fBodyStep⟩ := RawStep.par.lam_inv forwardStep
  have fBodyVar := RawStep.par.var_inv fBodyStep
  cases fBodyVar
  cases fEqLam
  obtain ⟨backwardBody, bEqLam, bBodyStep⟩ := RawStep.par.lam_inv backwardStep
  have bBodyVar := RawStep.par.var_inv bBodyStep
  cases bBodyVar
  cases bEqLam
  cases eqOuter
  exact ⟨Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw carrierRaw,
         sourceTerm, Step.par.refl sourceTerm⟩

/-! ## Heterogeneous-carrier ctors with single typed equivWitness child

`Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness`
has a single typed `equivWitness : Term context (Ty.equiv carrierA carrierB)
(RawTerm.equivIntro forwardRaw backwardRaw)` child.  The raw form is the
SAME `RawTerm.equivIntro forwardRaw backwardRaw` as the equivWitness.

The lift takes an equivWitness lift IH; from `RawStep.par.equivIntro_inv`
we get a target raw that matches RawTerm.equivIntro forward' backward'.
Apply Step.par.uaIntroHetCong with the typed step. -/

/-- **Term.uaIntroHet full lift.** Single typed child (equivWitness) at
`Ty.equiv carrierA carrierB`. -/
theorem RawStep.par.lift_full_uaIntroHet
    (innerLevel : UniverseLevel) (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                 (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivWitnessLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par (RawTerm.equivIntro forwardRaw backwardRaw) targetRawIH →
      ∃ equivWitnessTarget :
          Term context (Ty.equiv carrierA carrierB) targetRawIH,
        Step.par equivWitness equivWitnessTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.equivIntro forwardRaw backwardRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.uaIntroHet (context := context) innerLevel innerLevelLt
                         carrierARaw carrierBRaw equivWitness)
        targetTerm := by
  -- Use equivIntro_inv to extract target shape
  obtain ⟨forwardTarget, backwardTarget, eqOuter, _, _⟩ :=
    RawStep.par.equivIntro_inv rawStep
  -- Apply equivWitness lift IH (passing the full rawStep) to get typed target
  obtain ⟨equivWitnessTarget, equivWitnessStepTyped⟩ := equivWitnessLift rawStep
  cases eqOuter
  refine ⟨Ty.id (Ty.universe innerLevel innerLevelLt) carrierARaw carrierBRaw, ?_, ?_⟩
  · -- equivWitnessTarget at Ty.equiv carrierA carrierB with raw equivIntro forwardTarget backwardTarget;
    -- we want a typed Term at Ty.id (Ty.universe ...) carrierARaw carrierBRaw with the same raw.
    -- Use Term.uaIntroHet to wrap.
    exact Term.uaIntroHet (context := context) innerLevel innerLevelLt
                          carrierARaw carrierBRaw equivWitnessTarget
  · exact Step.par.uaIntroHetCong innerLevel innerLevelLt
                                  carrierARaw carrierBRaw equivWitnessStepTyped

/-! ## Heterogeneous-carrier equivalence intro lift

`Term.equivIntroHet forward backward leftInv rightInv` has four typed
children but only `forward` + `backward` appear in the raw projection
`RawTerm.equivIntro forwardRaw backwardRaw`.  The cong rule
`Step.par.equivIntroHetCong` takes Step.par on forward + backward and
auto-constructs the leftInv/rightInv with new types.

The lift takes IHs on forward and backward only.  The leftInv/rightInv
inputs are passed through as schematic implicits to the cong rule. -/

/-- **Term.equivIntroHet full lift.** -/
theorem RawStep.par.lift_full_equivIntroHet
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw)
    (forwardLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par forwardRaw targetRawIH →
      ∃ forwardTarget : Term context (Ty.arrow carrierA carrierB) targetRawIH,
        Step.par forward forwardTarget)
    (backwardLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par backwardRaw targetRawIH →
      ∃ backwardTarget : Term context (Ty.arrow carrierB carrierA) targetRawIH,
        Step.par backward backwardTarget)
    (leftInvNewSource :
      ∀ (forwardTarget backwardTarget : RawTerm scope),
      Term context
        (equivIntroHetLeftInverseType carrierA forwardTarget backwardTarget)
        leftInvRaw)
    (rightInvNewSource :
      ∀ (forwardTarget backwardTarget : RawTerm scope),
      Term context
        (equivIntroHetRightInverseType carrierB forwardTarget backwardTarget)
        rightInvRaw)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.equivIntro forwardRaw backwardRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.equivIntroHet (context := context) forward backward leftInv rightInv)
        targetTerm := by
  obtain ⟨forwardTarget, backwardTarget, eqOuter, forwardStep, backwardStep⟩ :=
    RawStep.par.equivIntro_inv rawStep
  obtain ⟨forwardTyped, forwardStepTyped⟩ := forwardLift forwardStep
  obtain ⟨backwardTyped, backwardStepTyped⟩ := backwardLift backwardStep
  cases eqOuter
  refine ⟨Ty.equiv carrierA carrierB,
          Term.equivIntroHet (context := context) forwardTyped backwardTyped
                             (leftInvNewSource forwardTarget backwardTarget)
                             (rightInvNewSource forwardTarget backwardTarget),
          ?_⟩
  exact Step.par.equivIntroHetCong forwardStepTyped backwardStepTyped

theorem RawStep.par.lift_full_oeqFunext
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    (pointwiseProof :
      Term context
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw)
    (pointwiseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par pointwiseRaw targetRawIH →
      ∃ pointwiseTarget :
          Term context
            (oeqFunextPointwiseType domainType codomainType
              leftFunctionRaw rightFunctionRaw)
            targetRawIH,
        Step.par pointwiseProof pointwiseTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.oeqFunext pointwiseRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof)
        targetTerm := by
  obtain ⟨pointwiseTargetRaw, eq, pointwiseStep⟩ :=
    RawStep.par.oeqFunext_inv rawStep
  obtain ⟨pointwiseTarget, pointwiseStepTyped⟩ := pointwiseLift pointwiseStep
  cases eq
  refine
    ⟨Ty.oeq (Ty.arrow domainType codomainType) leftFunctionRaw rightFunctionRaw,
     Term.oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw
                    pointwiseTarget, ?_⟩
  exact Step.par.oeqFunextCong domainType codomainType
                               leftFunctionRaw rightFunctionRaw
                               pointwiseStepTyped

/-! ## Schematic-payload type-code ctors (full lifts)

`Term.arrowCode`, `piTyCode`, ..., `equivCode` are CUMUL-2.4 VALUE-shaped
ctors carrying their raw payloads as schematic fields (no recursive
typed children).  Each has a typed cong rule
`Step.par.<X>CodeCong` mirroring the raw `RawStep.par.<X>CodeCong`.

Pattern per ctor:
1. `RawStep.par.<X>Code_inv` extracts subterm raw steps + target eq.
2. `cases eq` aligns target raw shape.
3. `suffices` over `someType` aligns the universe-Ty type index using
   `Ty.universe.inj`-style reasoning (universe ctor is parametric in
   level + level proof).
4. Apply typed `Step.par.<X>CodeCong`.

All ten codes target `Ty.universe outerLevel levelLe` so the source's
fixed type aligns trivially via `cases` on the proof / by reading off
the result type. -/

/-- **Term.arrowCode full lift.** -/
theorem RawStep.par.lift_full_arrowCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.arrowCode domainCodeRaw codomainCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.arrowCode domainCodeRaw codomainCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨domainTarget, codomainTarget, eq, domainStep, codomainStep⟩ :=
    RawStep.par.arrowCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.arrowCode (context := context) outerLevel levelLe
            domainTarget codomainTarget, ?_⟩
  -- Free-the-type-via-suffices: feedback_lean_free_type_via_suffices.md.
  -- Freeing someType lets Lean's match-compiler dispatch the var arm
  -- via raw-RawTerm.arrowCode-vs-RawTerm.var nomatch, and handle the
  -- arrowCode arm with proper level alignment via someTypeIsUniverse.
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.arrowCode (context := context) outerLevel levelLe
                   domainTarget codomainTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  -- innerLevel innerLevelLe come from inner Term.arrowCode ctor
  -- someTypeIsUniverse : Ty.universe innerLevel innerLevelLe = Ty.universe outerLevel levelLe
  -- We need Step.par.arrowCodeCong at outerLevel/levelLe but ctor instance is at inner.
  -- Substitute the equality:
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  -- innerLevelLe and levelLe have the same type now (innerLevel.toNat + 1 ≤ level);
  -- they may differ proof-irrelevantly, but here we need to close definitionally.
  -- The remaining Step.par target Term.arrowCode is at innerLevelLe vs outerLevelLe.
  -- Since the `≤` proof is propositional (Nat.le is a Prop), proof-irrelevance kicks in.
  exact Step.par.arrowCodeCong outerLevel innerLevelLe domainStep codomainStep

/-- **Term.piTyCode full lift.** Codomain raw lives at scope+1. -/
theorem RawStep.par.lift_full_piTyCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope) (codomainCodeRaw : RawTerm (scope + 1))
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.piTyCode domainCodeRaw codomainCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.piTyCode domainCodeRaw codomainCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨domainTarget, codomainTarget, eq, domainStep, codomainStep⟩ :=
    RawStep.par.piTyCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.piTyCode (context := context) outerLevel levelLe
            domainTarget codomainTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.piTyCode domainCodeRaw codomainCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.piTyCode (context := context) outerLevel levelLe
                   domainTarget codomainTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.piTyCodeCong outerLevel innerLevelLe domainStep codomainStep

/-- **Term.sigmaTyCode full lift.** Second raw lives at scope+1. -/
theorem RawStep.par.lift_full_sigmaTyCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw : RawTerm scope) (secondCodeRaw : RawTerm (scope + 1))
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.sigmaTyCode firstCodeRaw secondCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.sigmaTyCode firstCodeRaw secondCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨firstTarget, secondTarget, eq, firstStep, secondStep⟩ :=
    RawStep.par.sigmaTyCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.sigmaTyCode (context := context) outerLevel levelLe
            firstTarget secondTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.sigmaTyCode firstCodeRaw secondCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.sigmaTyCode (context := context) outerLevel levelLe
                   firstTarget secondTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.sigmaTyCodeCong outerLevel innerLevelLe firstStep secondStep

/-- **Term.productCode full lift.** -/
theorem RawStep.par.lift_full_productCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.productCode firstCodeRaw secondCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.productCode firstCodeRaw secondCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨firstTarget, secondTarget, eq, firstStep, secondStep⟩ :=
    RawStep.par.productCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.productCode (context := context) outerLevel levelLe
            firstTarget secondTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.productCode firstCodeRaw secondCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.productCode (context := context) outerLevel levelLe
                   firstTarget secondTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.productCodeCong outerLevel innerLevelLe firstStep secondStep

/-- **Term.sumCode full lift.** -/
theorem RawStep.par.lift_full_sumCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.sumCode leftCodeRaw rightCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.sumCode leftCodeRaw rightCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨leftTarget, rightTarget, eq, leftStep, rightStep⟩ :=
    RawStep.par.sumCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.sumCode (context := context) outerLevel levelLe
            leftTarget rightTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.sumCode leftCodeRaw rightCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.sumCode (context := context) outerLevel levelLe
                   leftTarget rightTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.sumCodeCong outerLevel innerLevelLe leftStep rightStep

/-- **Term.listCode full lift.** -/
theorem RawStep.par.lift_full_listCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.listCode elementCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listCode elementCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨elementTarget, eq, elementStep⟩ := RawStep.par.listCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.listCode (context := context) outerLevel levelLe
            elementTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.listCode elementCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.listCode (context := context) outerLevel levelLe
                   elementTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.listCodeCong outerLevel innerLevelLe elementStep

/-- **Term.optionCode full lift.** -/
theorem RawStep.par.lift_full_optionCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.optionCode elementCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionCode elementCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨elementTarget, eq, elementStep⟩ := RawStep.par.optionCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.optionCode (context := context) outerLevel levelLe
            elementTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.optionCode elementCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.optionCode (context := context) outerLevel levelLe
                   elementTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.optionCodeCong outerLevel innerLevelLe elementStep

/-- **Term.eitherCode full lift.** -/
theorem RawStep.par.lift_full_eitherCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.eitherCode leftCodeRaw rightCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.eitherCode leftCodeRaw rightCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨leftTarget, rightTarget, eq, leftStep, rightStep⟩ :=
    RawStep.par.eitherCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.eitherCode (context := context) outerLevel levelLe
            leftTarget rightTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.eitherCode leftCodeRaw rightCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.eitherCode (context := context) outerLevel levelLe
                   leftTarget rightTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.eitherCodeCong outerLevel innerLevelLe leftStep rightStep

/-- **Term.idCode full lift.** -/
theorem RawStep.par.lift_full_idCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.idCode typeCodeRaw leftRaw rightRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.idCode typeCodeRaw leftRaw rightRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨typeTarget, leftTarget, rightTarget, eq, typeStep, leftStep, rightStep⟩ :=
    RawStep.par.idCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.idCode (context := context) outerLevel levelLe
            typeTarget leftTarget rightTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.idCode typeCodeRaw leftRaw rightRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.idCode (context := context) outerLevel levelLe
                   typeTarget leftTarget rightTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.idCodeCong outerLevel innerLevelLe typeStep leftStep rightStep

/-- **Term.equivCode full lift.** -/
theorem RawStep.par.lift_full_equivCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.equivCode leftCodeRaw rightCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.equivCode leftCodeRaw rightCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨leftTarget, rightTarget, eq, leftStep, rightStep⟩ :=
    RawStep.par.equivCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.equivCode (context := context) outerLevel levelLe
            leftTarget rightTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.equivCode leftCodeRaw rightCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.equivCode (context := context) outerLevel levelLe
                   leftTarget rightTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.equivCodeCong outerLevel innerLevelLe leftStep rightStep

/-! ## Tier 0/1/2/3 lifts re-expressed at two-Ty existential

The existing fixed-Ty lifts (lift_unit, lift_lam, ..., lift_codataDest)
all produce targets at a SPECIFIC type.  When assembled into the
headline `Term.preserves` via Term induction, we want a uniform IH
shape: `∃ targetTy targetTerm, Step.par sourceTerm targetTerm`.

These wrapper theorems thread the existing fixed-Ty lift's result
through the two-Ty existential.  Each wrapper is a 1-line
`⟨_, target, step⟩` rebracketing.

When all 75 ctors have either a `_full` or `_uniform` lift, the
headline can dispatch via Term induction.  The ctors blocked by the
walls (refl/funextRefl/etc; pair; appPi; transp full) cannot be
rebracketed since their underlying lifts don't exist. -/

/-- **Tier 0 — Term.unit at two-Ty.** -/
theorem RawStep.par.lift_full_unit
    (sourceTerm : Term context Ty.unit (RawTerm.unit : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.unit : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_unit sourceTerm rawStep
  exact ⟨Ty.unit, target, step⟩

/-- **Tier 0 — Term.boolTrue at two-Ty.** -/
theorem RawStep.par.lift_full_boolTrue
    (sourceTerm : Term context Ty.bool (RawTerm.boolTrue : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolTrue : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_boolTrue sourceTerm rawStep
  exact ⟨Ty.bool, target, step⟩

/-- **Tier 0 — Term.boolFalse at two-Ty.** -/
theorem RawStep.par.lift_full_boolFalse
    (sourceTerm : Term context Ty.bool (RawTerm.boolFalse : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolFalse : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_boolFalse sourceTerm rawStep
  exact ⟨Ty.bool, target, step⟩

/-- **Tier 0 — Term.natZero at two-Ty.** -/
theorem RawStep.par.lift_full_natZero
    (sourceTerm : Term context Ty.nat (RawTerm.natZero : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.natZero : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_natZero sourceTerm rawStep
  exact ⟨Ty.nat, target, step⟩

/-- **Tier 0 — Term.var at two-Ty.** -/
theorem RawStep.par.lift_full_var
    {sourceType : Ty level scope} {position : Fin scope}
    (sourceTerm : Term context sourceType (RawTerm.var position))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.var position) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_var sourceTerm rawStep
  exact ⟨sourceType, target, step⟩

/-- **Tier 0 — Term.listNil at two-Ty.** -/
theorem RawStep.par.lift_full_listNil
    {elementType : Ty level scope}
    (sourceTerm :
      Term context (Ty.listType elementType) (RawTerm.listNil : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listNil : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_listNil sourceTerm rawStep
  exact ⟨Ty.listType elementType, target, step⟩

/-- **Tier 0 — Term.optionNone at two-Ty.** -/
theorem RawStep.par.lift_full_optionNone
    {elementType : Ty level scope}
    (sourceTerm :
      Term context (Ty.optionType elementType) (RawTerm.optionNone : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionNone : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_optionNone sourceTerm rawStep
  exact ⟨Ty.optionType elementType, target, step⟩

/-- **Tier 0 — Term.interval0 at two-Ty.** -/
theorem RawStep.par.lift_full_interval0
    (sourceTerm : Term context Ty.interval (RawTerm.interval0 : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval0 : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_interval0 sourceTerm rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 0 — Term.interval1 at two-Ty.** -/
theorem RawStep.par.lift_full_interval1
    (sourceTerm : Term context Ty.interval (RawTerm.interval1 : RawTerm scope))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval1 : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_interval1 sourceTerm rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 1 — Term.natSucc at two-Ty.** -/
theorem RawStep.par.lift_full_natSucc
    {predRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predRaw)
    (predLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par predRaw targetRawIH →
      ∃ predTarget : Term context Ty.nat targetRawIH,
        Step.par predecessor predTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.natSucc predRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.natSucc predecessor) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_natSucc predecessor predLift rawStep
  exact ⟨Ty.nat, target, step⟩

/-- **Tier 1 — Term.optionSome at two-Ty.** -/
theorem RawStep.par.lift_full_optionSome
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context elementType targetRawIH,
        Step.par valueTerm valueTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionSome valueRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.optionSome valueTerm) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_optionSome valueTerm valueLift rawStep
  exact ⟨Ty.optionType elementType, target, step⟩

/-- **Tier 1 — Term.eitherInl at two-Ty.** -/
theorem RawStep.par.lift_full_eitherInl
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context leftType targetRawIH,
        Step.par valueTerm valueTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.eitherInl valueRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.eitherInl (rightType := rightType) valueTerm) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_eitherInl (rightType := rightType) valueTerm valueLift rawStep
  exact ⟨Ty.eitherType leftType rightType, target, step⟩

/-- **Tier 1 — Term.eitherInr at two-Ty.** -/
theorem RawStep.par.lift_full_eitherInr
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context rightType targetRawIH,
        Step.par valueTerm valueTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.eitherInr valueRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.eitherInr (leftType := leftType) valueTerm) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_eitherInr (leftType := leftType) valueTerm valueLift rawStep
  exact ⟨Ty.eitherType leftType rightType, target, step⟩

/-- **Tier 1 — Term.intervalOpp at two-Ty.** -/
theorem RawStep.par.lift_full_intervalOpp
    {innerRaw : RawTerm scope}
    (innerValue : Term context Ty.interval innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context Ty.interval targetRawIH,
        Step.par innerValue innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalOpp innerRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.intervalOpp innerValue) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_intervalOpp innerValue innerLift rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 1 — Term.modIntro at two-Ty.** -/
theorem RawStep.par.lift_full_modIntro
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.modIntro innerRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.modIntro innerTerm) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_modIntro innerTerm innerLift rawStep
  exact ⟨innerType, target, step⟩

/-- **Tier 1 — Term.subsume at two-Ty.** -/
theorem RawStep.par.lift_full_subsume
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.subsume innerRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.subsume innerTerm) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_subsume innerTerm innerLift rawStep
  exact ⟨innerType, target, step⟩

/-- **Tier 1 — Term.recordIntro at two-Ty.** -/
theorem RawStep.par.lift_full_recordIntro
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw)
    (firstLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par firstRaw targetRawIH →
      ∃ firstTarget : Term context singleFieldType targetRawIH,
        Step.par firstField firstTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.recordIntro firstRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.recordIntro firstField) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_recordIntro firstField firstLift rawStep
  exact ⟨Ty.record singleFieldType, target, step⟩

/-- **Tier 1 — Term.lam at two-Ty.** -/
theorem RawStep.par.lift_full_lam
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType.weaken bodyRaw)
    (bodyLift : ∀ {targetRawIH : RawTerm (scope + 1)},
      RawStep.par bodyRaw targetRawIH →
      ∃ bodyTarget : Term (context.cons domainType) codomainType.weaken targetRawIH,
        Step.par body bodyTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.lam bodyRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.lam (codomainType := codomainType) body) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_lam body bodyLift rawStep
  exact ⟨Ty.arrow domainType codomainType, target, step⟩

/-- **Tier 1 — Term.lamPi at two-Ty.** -/
theorem RawStep.par.lift_full_lamPi
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType bodyRaw)
    (bodyLift : ∀ {targetRawIH : RawTerm (scope + 1)},
      RawStep.par bodyRaw targetRawIH →
      ∃ bodyTarget : Term (context.cons domainType) codomainType targetRawIH,
        Step.par body bodyTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.lam bodyRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.lamPi (domainType := domainType) body) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_lamPi body bodyLift rawStep
  exact ⟨Ty.piTy domainType codomainType, target, step⟩

/-- **Tier 1 — Term.pathLam at two-Ty.** -/
theorem RawStep.par.lift_full_pathLam
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyLift : ∀ {targetRawIH : RawTerm (scope + 1)},
      RawStep.par bodyRaw targetRawIH →
      ∃ bodyTarget :
          Term (context.cons Ty.interval) carrierType.weaken targetRawIH,
        Step.par body bodyTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.pathLam bodyRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body)
        targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                             body bodyLift rawStep
  exact ⟨Ty.path carrierType leftEndpoint rightEndpoint, target, step⟩

/-- **Tier 1 — Term.sessionRecv at two-Ty.** -/
theorem RawStep.par.lift_full_sessionRecv
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (channelLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par channelRaw targetRawIH →
      ∃ channelTarget : Term context (Ty.session protocolStep) targetRawIH,
        Step.par channel channelTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.sessionRecv channelRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.sessionRecv channel) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_sessionRecv channel channelLift rawStep
  exact ⟨Ty.session protocolStep, target, step⟩

/-- **Tier 1 — Term.universeCode at two-Ty.** -/
theorem RawStep.par.lift_full_universeCode
    {sourceType : Ty level scope} {innerLevelNat : Nat}
    (sourceTerm :
      Term context sourceType (RawTerm.universeCode innerLevelNat))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.universeCode innerLevelNat : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_universeCode sourceTerm rawStep
  exact ⟨sourceType, target, step⟩

/-- **Tier 1 — Term.cumulUp at two-Ty.** -/
theorem RawStep.par.lift_full_cumulUp
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (typeCodeLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par codeRaw targetRawIH →
      ∃ typeCodeTarget :
          Term context (Ty.universe lowerLevel levelLeLow) targetRawIH,
        Step.par typeCode typeCodeTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.cumulUpMarker codeRaw : RawTerm scope) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.cumulUp lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCode)
        targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_cumulUp lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCode typeCodeLift rawStep
  exact ⟨Ty.universe higherLevel levelLeHigh, target, step⟩

/-- **Tier 2 — Term.intervalMeet at two-Ty.** -/
theorem RawStep.par.lift_full_intervalMeet
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget : Term context Ty.interval targetRawIH,
        Step.par leftValue leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget : Term context Ty.interval targetRawIH,
        Step.par rightValue rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalMeet leftRaw rightRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.intervalMeet leftValue rightValue) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_intervalMeet leftValue rightValue leftLift rightLift rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 2 — Term.intervalJoin at two-Ty.** -/
theorem RawStep.par.lift_full_intervalJoin
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget : Term context Ty.interval targetRawIH,
        Step.par leftValue leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget : Term context Ty.interval targetRawIH,
        Step.par rightValue rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalJoin leftRaw rightRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.intervalJoin leftValue rightValue) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_intervalJoin leftValue rightValue leftLift rightLift rawStep
  exact ⟨Ty.interval, target, step⟩

/-- **Tier 2 — Term.glueIntro at two-Ty.** -/
theorem RawStep.par.lift_full_glueIntro
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw)
    (baseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par baseRaw targetRawIH →
      ∃ baseTarget : Term context baseType targetRawIH,
        Step.par baseValue baseTarget)
    (partialLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par partialRaw targetRawIH →
      ∃ partialTarget : Term context baseType targetRawIH,
        Step.par partialValue partialTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.glueIntro baseRaw partialRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseValue
                        partialValue)
        targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_glueIntro modeIsUnivalent baseType boundaryWitness
                               baseValue partialValue baseLift partialLift rawStep
  exact ⟨Ty.glue baseType boundaryWitness, target, step⟩

/-- **Tier 2 — Term.hcomp at two-Ty.** -/
theorem RawStep.par.lift_full_hcomp
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw)
    (sidesLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par sidesRaw targetRawIH →
      ∃ sidesTarget : Term context carrierType targetRawIH,
        Step.par sidesValue sidesTarget)
    (capLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par capRaw targetRawIH →
      ∃ capTarget : Term context carrierType targetRawIH,
        Step.par capValue capTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.hcomp sidesRaw capRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.hcomp modeIsUnivalent sidesValue capValue) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_hcomp modeIsUnivalent sidesValue capValue sidesLift capLift
                           rawStep
  exact ⟨carrierType, target, step⟩

/-- **Tier 2 — Term.codataUnfold at two-Ty.** -/
theorem RawStep.par.lift_full_codataUnfold
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw)
    (stateLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par stateRaw targetRawIH →
      ∃ stateTarget : Term context stateType targetRawIH,
        Step.par initialState stateTarget)
    (transitionLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par transitionRaw targetRawIH →
      ∃ transitionTarget :
          Term context (Ty.arrow stateType outputType) targetRawIH,
        Step.par transition transitionTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.codataUnfold stateRaw transitionRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.codataUnfold initialState transition) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_codataUnfold initialState transition stateLift transitionLift
                                  rawStep
  exact ⟨Ty.codata stateType outputType, target, step⟩

/-- **Tier 2 — Term.sessionSend at two-Ty.** -/
theorem RawStep.par.lift_full_sessionSend
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (payload : Term context payloadType payloadRaw)
    (channelLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par channelRaw targetRawIH →
      ∃ channelTarget : Term context (Ty.session protocolStep) targetRawIH,
        Step.par channel channelTarget)
    (payloadLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par payloadRaw targetRawIH →
      ∃ payloadTarget : Term context payloadType targetRawIH,
        Step.par payload payloadTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.sessionSend channelRaw payloadRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.sessionSend protocolStep channel payload) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_sessionSend protocolStep channel payload channelLift
                                 payloadLift rawStep
  exact ⟨Ty.session protocolStep, target, step⟩

/-- **Tier 2 — Term.listCons at two-Ty.** -/
theorem RawStep.par.lift_full_listCons
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (headLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par headRaw targetRawIH →
      ∃ headTarget : Term context elementType targetRawIH,
        Step.par headTerm headTarget)
    (tailLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par tailRaw targetRawIH →
      ∃ tailTarget : Term context (Ty.listType elementType) targetRawIH,
        Step.par tailTerm tailTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listCons headRaw tailRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.listCons headTerm tailTerm) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_listCons headTerm tailTerm headLift tailLift rawStep
  exact ⟨Ty.listType elementType, target, step⟩

/-- **Tier 2 — Term.equivApp at two-Ty.** -/
theorem RawStep.par.lift_full_equivApp
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw)
    (equivLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par equivRaw targetRawIH →
      ∃ equivTarget : Term context (Ty.equiv carrierA carrierB) targetRawIH,
        Step.par equivTerm equivTarget)
    (argumentLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentRaw targetRawIH →
      ∃ argumentTarget : Term context carrierA targetRawIH,
        Step.par argumentTerm argumentTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.equivApp equivRaw argumentRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.equivApp equivTerm argumentTerm) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_equivApp equivTerm argumentTerm equivLift argumentLift rawStep
  exact ⟨carrierB, target, step⟩

/-- **Tier 2 — Term.refineIntro at two-Ty.** -/
theorem RawStep.par.lift_full_refineIntro
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw)
    (valueLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par valueRaw targetRawIH →
      ∃ valueTarget : Term context baseType targetRawIH,
        Step.par baseValue valueTarget)
    (proofLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par proofRaw targetRawIH →
      ∃ proofTarget : Term context Ty.unit targetRawIH,
        Step.par predicateProof proofTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refineIntro valueRaw proofRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.refineIntro predicate baseValue predicateProof) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_refineIntro predicate baseValue predicateProof valueLift
                                 proofLift rawStep
  exact ⟨Ty.refine baseType predicate, target, step⟩

/-- **Tier 2 — Term.effectPerform at two-Ty.** -/
theorem RawStep.par.lift_full_effectPerform
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    (operationTag :
      Term context (Ty.effect operationSignature.argumentCarrier effectTag)
                   operationRaw)
    (arguments :
      Term context operationSignature.argumentCarrier argumentsRaw)
    (operationLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par operationRaw targetRawIH →
      ∃ operationTarget :
          Term context (Ty.effect operationSignature.argumentCarrier effectTag)
                       targetRawIH,
        Step.par operationTag operationTarget)
    (argumentsLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentsRaw targetRawIH →
      ∃ argumentsTarget :
          Term context operationSignature.argumentCarrier targetRawIH,
        Step.par arguments argumentsTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.effectPerform operationRaw argumentsRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments)
        targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_effectPerform effectTag effectRow operationSignature
                                   canPerformOperation operationTag arguments
                                   operationLift argumentsLift rawStep
  exact ⟨Ty.effect operationSignature.resultCarrier effectTag, target, step⟩

/-- **Tier 3 — Term.natElim at two-Ty.** -/
theorem RawStep.par.lift_full_natElim
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget : Term context (Ty.arrow Ty.nat motiveType) targetRawIH,
        Step.par succBranch succTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.natElim scrutineeRaw zeroRaw succRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.natElim scrutinee zeroBranch succBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_natElim scrutinee zeroBranch succBranch
                             scrutLift zeroLift succLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.natRec at two-Ty.** -/
theorem RawStep.par.lift_full_natRec
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget :
          Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
                       targetRawIH,
        Step.par succBranch succTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.natRec scrutineeRaw zeroRaw succRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.natRec scrutinee zeroBranch succBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_natRec scrutinee zeroBranch succBranch
                            scrutLift zeroLift succLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.listElim at two-Ty.** -/
theorem RawStep.par.lift_full_listElim
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.listType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (nilLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par nilRaw targetRawIH →
      ∃ nilTarget : Term context motiveType targetRawIH,
        Step.par nilBranch nilTarget)
    (consLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par consRaw targetRawIH →
      ∃ consTarget :
          Term context
            (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
            targetRawIH,
        Step.par consBranch consTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.listElim scrutineeRaw nilRaw consRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.listElim scrutinee nilBranch consBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_listElim scrutinee nilBranch consBranch
                              scrutLift nilLift consLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.optionMatch at two-Ty.** -/
theorem RawStep.par.lift_full_optionMatch
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.optionType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (noneLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par noneRaw targetRawIH →
      ∃ noneTarget : Term context motiveType targetRawIH,
        Step.par noneBranch noneTarget)
    (someLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par someRaw targetRawIH →
      ∃ someTarget :
          Term context (Ty.arrow elementType motiveType) targetRawIH,
        Step.par someBranch someTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.optionMatch scrutineeRaw noneRaw someRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.optionMatch scrutinee noneBranch someBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_optionMatch scrutinee noneBranch someBranch
                                 scrutLift noneLift someLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.eitherMatch at two-Ty.** -/
theorem RawStep.par.lift_full_eitherMatch
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget :
          Term context (Ty.eitherType leftType rightType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget :
          Term context (Ty.arrow leftType motiveType) targetRawIH,
        Step.par leftBranch leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget :
          Term context (Ty.arrow rightType motiveType) targetRawIH,
        Step.par rightBranch rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.eitherMatch scrutinee leftBranch rightBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_eitherMatch scrutinee leftBranch rightBranch
                                 scrutLift leftLift rightLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.modElim at two-Ty.** -/
theorem RawStep.par.lift_full_modElim
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.modElim innerRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.modElim innerTerm) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_modElim innerTerm innerLift rawStep
  exact ⟨innerType, target, step⟩

/-- **Tier 3 — Term.recordProj at two-Ty.** -/
theorem RawStep.par.lift_full_recordProj
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw)
    (recordLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par recordRaw targetRawIH →
      ∃ recordTarget :
          Term context (Ty.record singleFieldType) targetRawIH,
        Step.par recordValue recordTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.recordProj recordRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.recordProj recordValue) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_recordProj recordValue recordLift rawStep
  exact ⟨singleFieldType, target, step⟩

/-- **Tier 3 — Term.refineElim at two-Ty.** -/
theorem RawStep.par.lift_full_refineElim
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (refinedLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par refinedRaw targetRawIH →
      ∃ refinedTarget :
          Term context (Ty.refine baseType predicate) targetRawIH,
        Step.par refinedValue refinedTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refineElim refinedRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.refineElim refinedValue) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_refineElim refinedValue refinedLift rawStep
  exact ⟨baseType, target, step⟩

/-- **Tier 3 — Term.glueElim at two-Ty.** -/
theorem RawStep.par.lift_full_glueElim
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {gluedRaw : RawTerm scope}
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par gluedRaw targetRawIH →
      ∃ gluedTarget :
          Term context (Ty.glue baseType boundaryWitness) targetRawIH,
        Step.par gluedValue gluedTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.glueElim gluedRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.glueElim modeIsUnivalent gluedValue) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_glueElim modeIsUnivalent gluedValue gluedLift rawStep
  exact ⟨baseType, target, step⟩

/-- **Tier 3 — Term.codataDest at two-Ty.** -/
theorem RawStep.par.lift_full_codataDest
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw)
    (codataLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par codataRaw targetRawIH →
      ∃ codataTarget :
          Term context (Ty.codata stateType outputType) targetRawIH,
        Step.par codataValue codataTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.codataDest codataRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.codataDest codataValue) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_codataDest codataValue codataLift rawStep
  exact ⟨outputType, target, step⟩

/-! ## Coverage status (post-juggernaut Phase 5 / #1590-CORE)

**Total Term ctors**: 75
**Full lifts shipped**: 70 (93%)
**Deferred**: 5 (pair, appPi, transp, funextRefl, funextIntroHet)

### Shipped this juggernaut (Phase 5)

**Type-code ctors via free-the-type-via-suffices + Ty.universe alignment**
(10 ctors): arrowCode, piTyCode, sigmaTyCode, productCode, sumCode,
listCode, optionCode, eitherCode, idCode, equivCode.

**Schematic-payload value ctors with new typed cong rules**:
- refl (via Step.par.reflCong, suffices destructor)
- equivReflId (atom-shaped — only refl applies)
- equivReflIdAtId (atom-shaped — only refl applies)

**Heterogeneous-carrier ctors**:
- uaIntroHet (single typed equivWitness child)
- equivIntroHet (forward + backward typed children, leftInv/rightInv
  via fresh-supplier parameters)

### Shipped in prior juggernauts (Phases 1-4)

**Atoms (Tier 0)** (9): unit, boolTrue, boolFalse, natZero, listNil,
optionNone, interval0, interval1, var.

**Unary cong (Tier 1)** (9): natSucc, optionSome, eitherInl, eitherInr,
intervalOpp, modIntro, subsume, recordIntro, sessionRecv.

**Binders (Tier 1)** (3): lam, lamPi, pathLam.

**Binary cong (Tier 2)** (10): intervalMeet, intervalJoin, glueIntro,
hcomp, codataUnfold, sessionSend, listCons, equivApp, refineIntro,
effectPerform.

**Eliminators (Tier 3)** (10): natElim, natRec, listElim, optionMatch,
eitherMatch, modElim, recordProj, refineElim, glueElim, codataDest.

**β cast wall demolished (full lifts)** (4): app, pathApp, fst, snd.

**Type-changing iota** (3): idJ, idStrictRec, boolElim.

**Schematic-payload value (oldcong)** (3): oeqRefl, idStrictRefl, oeqFunext.

**Universe / cumul** (2): universeCode, cumulUp.

### Deferred (5 ctors)

* **pair**: heterogeneous Step.par signature; second has type
  `secondType.subst0 firstType firstRaw` which CHANGES when firstRaw
  steps.  IH structure needs extension to allow target-type-changing
  second IH.
* **appPi (full)**: β cast wall same as `app`; cong-only variant
  shipped.  Full version has additional dep-elim wall via piTy
  vs funextRefl shape ambiguity.
* **transp (full)**: typed `transpReflBetaDeep` Step.par ctor doesn't
  exist; cong-only variant shipped.
* **funextRefl**: raw form `RawTerm.lam (RawTerm.refl applyRaw)`
  shape-collides with Term.lamPi (Term.refl ...) at identical
  (Ty.piTy, raw) signatures.
* **funextIntroHet**: raw form `RawTerm.lam (RawTerm.refl applyARaw)`
  shape-collides with Term.funextReflAtId at identical
  (Ty.id (Ty.arrow ...), raw) signatures.  An earlier draft of
  `lift_full_funextReflAtId` was found to LEAK 2 axioms (Quot.sound,
  propext) via the `cases genericTerm` + `all_goals first | nomatch`
  pattern; hence the entire family is deferred to a redesigned
  ctor-by-ctor casesOn dispatch.

### Headline assembly status

The full `Term.preserves` over Term induction remains deferred — its
assembly requires:
1. Resolving the 5 deferred ctors above.
2. A unified IH shape that handles atoms (0 IHs), unary (1 IH),
   binary (2 IHs), eliminators (3+ IHs).

What's shipped is the 70 compositional bricks, each with `#assert_no_axioms`
verified or smoke-audited zero-axiom (see `Smoke/AuditPhase1590CorePreservesTerm.lean`).
When the full headline is assembled, child IHs are supplied by Term
induction. -/

end LeanFX2
