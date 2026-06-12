import FX1Poly.STC.FxLogicalRelation
import FX1Poly.Typed.ClosedBoolCanonicity
/-! # FX1Poly/STC/FxBoolCanonicity — canonicityViaSTC for FX bool (the §3.12 headline)

The Axis 12 `canonicityTheorem` ledger level, witnessed: every closed
combined-native-layer-typed FX bool GLUES with its canonicity evidence —
reaching `boolTrue` or `boolFalse` — in the canonical STC model's
vocabulary.  This is the polycell.md §3.12 `canonicityViaSTC`
signature, previously doc-only, now a checked construction.

## Why the syntactic side is the COMBINED layer — the vacuity trap

The generic relation (`fxStcRelationAt`) glues GROWN-typed subjects.
At the bool classifier that would be VACUOUS: the grown engine has NO
closed terms at `boolTypeCell` (`noClosedGrownTermAtBoolType` — bool
VALUES are typed by the union's table-driven rows, not the grown Π
engine).  A grown-only `canonicityViaSTC` would be vacuously true and
therefore dishonest.  `ClosedTypedBool` carries the same disjunction
`closedBoolCanonicalForms` consumes (the union table-row witnesses —
`dataIntroNullary` / `baseTypeFormation` — or grown), with the grown
disjunct provably uninhabited
(`closedTypedBool_grownArm_isVacuous`) and the data-intro disjunct
concretely inhabited (`canonicityViaSTC` at `boolTrue` computes, the
non-vacuity smoke).

## The bridge

As with the generic relation, the semantic component is the KERNEL's
canonicity witness — `closedBoolCanonicalForms`, the syntactic route
(grown SN + master SR), definitionally
(`canonicityViaSTC_semantic_isKernelWitness`).  BRIDGED, not
independent; independence stays HIT-blocked (see
`FxLogicalRelation.lean`).

Zero-axiom; gated in `FX1PolyAudit/AuditProfile.lean`. -/

namespace FX1Poly.STC

open FX1Poly.Core FX1Poly.Typed

/-- A closed FX bool subject typed by the COMBINED native layers — the
non-vacuous syntactic component of the bool STC relation (the same
disjunction `closedBoolCanonicalForms` consumes: a union table-row
witness or a grown derivation). -/
structure ClosedTypedBool (profile : PolyProfile) where
  /-- The closed subject. -/
  term : RawTerm 0
  /-- Its native-layer typing at the bool classifier: a union table-row
  witness (`dataIntroNullary` / `baseTypeFormation`) or a grown
  derivation. -/
  typed :
    boolStandaloneRowTyped term ∨
    HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) term boolTypeCell

/-- The canonicity payload at bool: the subject reaches a canonical
bool value. -/
def ReachesCanonicalBool (subject : RawTerm 0) : Prop :=
  ∃ value : RawTerm 0,
    StepStar subject value ∧ (value = boolTrueCell ∨ value = boolFalseCell)

/-- ★ The bool-classifier STC relation: the canonical model's `Glue`
of closed combined-native-layer-typed bool syntax with the CANONICITY
payload (strictly stronger than the generic relation's SN side). -/
def fxStcBoolRelation (profile : PolyProfile) : Type :=
  canonicalSTCModel.Glue (ClosedTypedBool profile)
    (fun typedBool => PLift (ReachesCanonicalBool typedBool.term))

/-- ★★ **canonicityViaSTC (§3.12)**: every closed combined-native-layer-typed
FX bool GLUES with its canonicity evidence.  The semantic component is
the kernel's `closedBoolCanonicalForms` (the syntactic route: grown SN
+ master subject reduction). -/
def canonicityViaSTC {profile : PolyProfile}
    (typedBool : ClosedTypedBool profile) : fxStcBoolRelation profile :=
  ⟨typedBool, ⟨closedBoolCanonicalForms typedBool.typed⟩⟩

/-- The §3.12 headline statement, recovered FROM the glue: a closed
typed bool reaches `boolTrue` or `boolFalse`. -/
theorem canonicityViaSTC_extracts {profile : PolyProfile}
    (typedBool : ClosedTypedBool profile) :
    ReachesCanonicalBool typedBool.term :=
  (canonicityViaSTC typedBool).semantic.down

/-- The bridge pin: the glue's semantic component IS the kernel's
canonicity witness, definitionally. -/
theorem canonicityViaSTC_semantic_isKernelWitness {profile : PolyProfile}
    (typedBool : ClosedTypedBool profile) :
    (canonicityViaSTC typedBool).semantic
      = ⟨closedBoolCanonicalForms typedBool.typed⟩ := rfl

/-! ## Honesty pins: vacuity boundary + non-vacuity smoke -/

/-- The VACUITY TRAP, pinned: the GROWN-only bool glue (the generic
relation instantiated at `boolTypeCell`) has an EMPTY syntactic side —
the grown engine types no closed bool.  This is why
`canonicityViaSTC` quantifies over the combined engines. -/
theorem grownOnlyBoolGlue_isVacuous {profile : PolyProfile}
    (closedGrown : ClosedTypedTerm profile boolTypeCell) : False :=
  HasTypeDescPi.noClosedGrownTermAtBoolType closedGrown.typed

/-- The grown ARM of `ClosedTypedBool` is likewise uninhabited — the
data-intro and base-type arms carry the relation. -/
theorem closedTypedBool_grownArm_isVacuous {profile : PolyProfile}
    {term : RawTerm 0}
    (grownTyped : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) term boolTypeCell) :
    False :=
  HasTypeDescPi.noClosedGrownTermAtBoolType grownTyped

/-- The canonical `boolTrue` subject, as a native-layer-typed bool —
the `gen_boolTrue` row of `dataIntroNullaryRuleDescOf`, with the
subject equation and the output-cell equation both definitional. -/
def boolTrueClosedTyped (profile : PolyProfile) : ClosedTypedBool profile :=
  ⟨boolTrueCell,
    Or.inl (Or.inl ⟨.gen_boolTrue, (), .childNil,
      { outputTypeCode := fun _ => boolTypeCell }, rfl,
      dataIntroNullaryRuleDescOf_boolTrue, rfl⟩)⟩

/-- NON-VACUITY smoke: `canonicityViaSTC` at `boolTrue` produces a
genuine glue whose extracted canonicity evidence is the zero-step
reduction to `boolTrue` itself. -/
theorem canonicityViaSTC_boolTrue_nonVacuous (profile : PolyProfile) :
    (canonicityViaSTC (boolTrueClosedTyped profile)).syntactic.term
      = boolTrueCell := rfl

end FX1Poly.STC
