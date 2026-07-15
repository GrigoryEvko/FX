/-! # mode-2 — the multiplier structure-class certificate (DIM-CLASS for modes)

`mode-2` is the mode-axis analogue of the resource-grade DIM-CLASS taxonomy
(`Mode/GradeAlgebra/EffectLatticeClassification.lean`: `DimensionGradeAlgebra` / `GradedDimensionName` /
`gradeAlgebraOf`).  Where DIM-CLASS classifies a §6 GRADE dimension by its algebraic structure
(ordered-semiring vs bounded-semilattice), `mode-2` classifies a MODE / MULTIPLIER by its STRUCTURE CLASS — the
Nuyts–Devriese transpension "multiplier" classification (Fig 7 / 9 of "Transpension: The Right Adjoint to the
Pi-type").

A MULTIPLIER is the endofunctor (a fresh-dimension / interval shape) a modal dimension is built on; its
structural strength determines which modal operators (connections, the diagonal, the reversal, ultimately
Gel / Glue / transpension) are available.  The classification ladder is the cube-category zoo (verified in the
`context-22` audit): the AFFINE interval (fresh dimension + endpoints, no diagonal) ⊏ the CARTESIAN cube (adds
the diagonal) ⊏ the DEDEKIND cube (adds the monotone connections ∧/∨) ⊏ the DE MORGAN / CCHM cube (adds the
non-monotone reversal ¬).

## What is built here, and what is deferred

  * **`MultiplierStructureClass`** — the four structure classes (`affine` / `cartesian` / `dedekind` /
    `deMorgan`), with `structuralStrength` and the structural-consequence predicates (`supportsDiagonal` /
    `supportsConnections` / `supportsReversal` — Fig 9: which operators each class unlocks).
  * **`refines`** — the linear refinement order on classes (by structural strength), reflexive + transitive.
  * **`MultiplierCertificate`** — the certificate: a structure class plus the three structural flags, with a
    PROOF that the flags match the class.  `MultiplierStructureClass.certificate` builds the canonical valid
    certificate for each class.
  * **`IntervalMultiplierName` / `structureClassOf` / `certificate`** — the named interval multipliers and
    their classification (mirroring `GradedDimensionName.gradeAlgebraOf`), with the per-name `rfl` ledger.
  * the refinement CHAIN (`affine ⊑ cartesian ⊑ dedekind ⊑ deMorgan`) + non-degeneracy (distinct classes,
    strict refinement, the reversal only at `deMorgan`).

  * ★ **the full Nuyts property table** (Fig 7/9) — `MultiplierProperty` (the eight properties), the per-class
    `hasProperty` table, its MONOTONICITY up the ladder (`hasProperty_mono`), and its CONSISTENCY with the cube
    flags — beyond the three-flag cube ladder.

DEFERRED (recorded by `= false` markers):
  * the SEMANTIC multiplier endofunctor + the unpointability / dimensional-splitness criteria ARE shipped at
    `mode-12`; only the genuine PRESHEAF-category model with the full Nuyts axioms remains deferred
    (`hasMultiplierEndofunctorRealization = false`, scoped to the presheaf model);
  * the MODAL CONSEQUENCES — the Gel / Glue / Weld / transpension CONSTRUCTIONS each class unlocks (Fig 9's
    right-hand side) — `hasMultiplierModalConsequences = false` (`mode-11` ships the adjunction + zoo targets);
  * the SEMANTIC justification of the property-table values (that the cube presheaf categories realize them) —
    `hasFullMultiplierPropertyTable = false` (the structural table itself is now shipped, see above).

This `mode-2` discharges `mode-1`'s `fxMode_hasModeTheoryStructureClass` deferral (the structure-class layer).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Axis

/-! ## The structure classes -/

/-- The **multiplier structure classes** — the cube-category ladder a modal dimension's multiplier can carry:
the affine interval, the cartesian cube (with diagonal), the Dedekind cube (with monotone connections), and the
De Morgan / CCHM cube (with the non-monotone reversal). -/
inductive MultiplierStructureClass where
  /-- The affine interval: a fresh dimension with endpoints, no diagonal — the minimal transpension multiplier. -/
  | affine
  /-- The cartesian cube: adds the diagonal (the contraction). -/
  | cartesian
  /-- The Dedekind cube: adds the monotone connections (∧ / ∨), no reversal. -/
  | dedekind
  /-- The De Morgan / CCHM cube: adds the non-monotone reversal (¬). -/
  | deMorgan
  deriving DecidableEq

/-- The structural strength of a class (its position on the refinement ladder). -/
def MultiplierStructureClass.structuralStrength : MultiplierStructureClass → Nat
  | .affine => 0
  | .cartesian => 1
  | .dedekind => 2
  | .deMorgan => 3

/-- Whether the class has the diagonal (cartesian and above) — the strength threshold `1 ≤ …`, derived from
`structuralStrength` (one source of truth for the ladder) rather than a parallel table. -/
def MultiplierStructureClass.supportsDiagonal (structureClass : MultiplierStructureClass) : Bool :=
  decide (1 ≤ structureClass.structuralStrength)

/-- Whether the class has the monotone connections (Dedekind and above) — the threshold `2 ≤ …`. -/
def MultiplierStructureClass.supportsConnections (structureClass : MultiplierStructureClass) : Bool :=
  decide (2 ≤ structureClass.structuralStrength)

/-- Whether the class has the non-monotone reversal (De Morgan only) — the threshold `3 ≤ …`. -/
def MultiplierStructureClass.supportsReversal (structureClass : MultiplierStructureClass) : Bool :=
  decide (3 ≤ structureClass.structuralStrength)

/-- One class **refines** another when it has at most the structural strength — the linear ladder order.
Reducible so the `Nat`-`≤` `Decidable` instance is found through it. -/
@[reducible] def MultiplierStructureClass.refines (lower upper : MultiplierStructureClass) : Prop :=
  lower.structuralStrength ≤ upper.structuralStrength

/-- Refinement is reflexive. -/
theorem MultiplierStructureClass.refines_refl (structureClass : MultiplierStructureClass) :
    structureClass.refines structureClass :=
  Nat.le_refl _

/-- Refinement is transitive. -/
theorem MultiplierStructureClass.refines_trans {lower middle upper : MultiplierStructureClass}
    (lowerToMiddle : lower.refines middle) (middleToUpper : middle.refines upper) :
    lower.refines upper :=
  Nat.le_trans lowerToMiddle middleToUpper

/-! ## The certificate -/

/-- A **multiplier certificate** — the structure class together with its three structural flags and a proof
that the flags are exactly the class's structural consequences.  This is the certified evidence of a
multiplier's structure (the mode-axis analogue of a DIM-CLASS classification). -/
structure MultiplierCertificate where
  /-- The structure class being certified. -/
  structureClass : MultiplierStructureClass
  /-- Whether the diagonal is available. -/
  hasDiagonal : Bool
  /-- Whether the monotone connections are available. -/
  hasConnections : Bool
  /-- Whether the non-monotone reversal is available. -/
  hasReversal : Bool
  /-- The diagonal flag matches the class. -/
  diagonalMatches : hasDiagonal = structureClass.supportsDiagonal
  /-- The connections flag matches the class. -/
  connectionsMatch : hasConnections = structureClass.supportsConnections
  /-- The reversal flag matches the class. -/
  reversalMatches : hasReversal = structureClass.supportsReversal

/-- The canonical (valid) certificate for a structure class: the flags ARE its structural consequences, so each
match obligation is `rfl`. -/
def MultiplierStructureClass.certificate (structureClass : MultiplierStructureClass) : MultiplierCertificate where
  structureClass := structureClass
  hasDiagonal := structureClass.supportsDiagonal
  hasConnections := structureClass.supportsConnections
  hasReversal := structureClass.supportsReversal
  diagonalMatches := rfl
  connectionsMatch := rfl
  reversalMatches := rfl

/-! ## The named interval multipliers + the classification -/

/-- The named interval multipliers carrying a structure class (the mode-axis analogue of `GradedDimensionName`). -/
inductive IntervalMultiplierName where
  /-- The affine / BCH interval. -/
  | affineInterval
  /-- The cartesian-cube interval. -/
  | cartesianInterval
  /-- The Dedekind-cube interval. -/
  | dedekindInterval
  /-- The De Morgan / CCHM interval. -/
  | deMorganInterval

/-- **The classification** — each named interval's structure class (mirrors `gradeAlgebraOf`). -/
def IntervalMultiplierName.structureClassOf : IntervalMultiplierName → MultiplierStructureClass
  | .affineInterval => .affine
  | .cartesianInterval => .cartesian
  | .dedekindInterval => .dedekind
  | .deMorganInterval => .deMorgan

/-- The certified classification of a named interval. -/
def IntervalMultiplierName.certificate (name : IntervalMultiplierName) : MultiplierCertificate :=
  name.structureClassOf.certificate

/-! ## Ledger -/

/-- Ledger: the affine interval is the affine class. -/
theorem affineInterval_isAffine :
    IntervalMultiplierName.affineInterval.structureClassOf = .affine := rfl

/-- Ledger: the cartesian interval is the cartesian class. -/
theorem cartesianInterval_isCartesian :
    IntervalMultiplierName.cartesianInterval.structureClassOf = .cartesian := rfl

/-- Ledger: the Dedekind interval is the Dedekind class. -/
theorem dedekindInterval_isDedekind :
    IntervalMultiplierName.dedekindInterval.structureClassOf = .dedekind := rfl

/-- Ledger (the strongest): the De Morgan interval is the De Morgan class. -/
theorem deMorganInterval_isDeMorgan :
    IntervalMultiplierName.deMorganInterval.structureClassOf = .deMorgan := rfl

/-! ## The refinement chain + non-degeneracy -/

/-- The refinement ladder: affine ⊑ cartesian ⊑ dedekind ⊑ deMorgan. -/
theorem multiplierLadder :
    MultiplierStructureClass.affine.refines .cartesian
      ∧ MultiplierStructureClass.cartesian.refines .dedekind
      ∧ MultiplierStructureClass.dedekind.refines .deMorgan := by
  decide

/-- Non-degeneracy: the affine and De Morgan classes are genuinely distinct. -/
theorem affine_ne_deMorgan : MultiplierStructureClass.affine ≠ .deMorgan :=
  fun classesEqual => MultiplierStructureClass.noConfusion classesEqual

/-- Non-degeneracy: refinement is strict — the De Morgan class does NOT refine the affine class. -/
theorem deMorgan_not_refines_affine : ¬ MultiplierStructureClass.deMorgan.refines .affine := by
  decide

/-- The structural distinction is contentful: only the De Morgan class has the reversal. -/
theorem deMorgan_supportsReversal : MultiplierStructureClass.deMorgan.supportsReversal = true := rfl

/-- The affine class does NOT have the reversal (the bottom of the ladder is genuinely weaker). -/
theorem affine_not_supportsReversal : MultiplierStructureClass.affine.supportsReversal = false := rfl

/-! ## The structure-class lattice — how modal structure-classes combine

The mode-axis analogue of the resource DIM-CLASS composition (`BoundedJoinSemilattice.product`): combining two
modal dimensions needs the JOIN of their structure classes (the weakest class supporting both), and the common
substructure is the MEET.  On the linear ladder these are the strength-max and strength-min, forming a (bounded)
lattice. -/

/-- The **join** of two structure classes — the weakest class refining both (strength-max on the ladder). -/
def MultiplierStructureClass.join (lower upper : MultiplierStructureClass) : MultiplierStructureClass :=
  if lower.structuralStrength ≤ upper.structuralStrength then upper else lower

/-- The **meet** of two structure classes — the strongest class both refine (strength-min on the ladder). -/
def MultiplierStructureClass.meet (lower upper : MultiplierStructureClass) : MultiplierStructureClass :=
  if lower.structuralStrength ≤ upper.structuralStrength then lower else upper

/-- Join is idempotent. -/
theorem MultiplierStructureClass.join_idem (structureClass : MultiplierStructureClass) :
    structureClass.join structureClass = structureClass := by cases structureClass <;> rfl

/-- Join is commutative. -/
theorem MultiplierStructureClass.join_comm (lower upper : MultiplierStructureClass) :
    lower.join upper = upper.join lower := by cases lower <;> cases upper <;> rfl

/-- Join is associative. -/
theorem MultiplierStructureClass.join_assoc (lower middle upper : MultiplierStructureClass) :
    (lower.join middle).join upper = lower.join (middle.join upper) := by
  cases lower <;> cases middle <;> cases upper <;> rfl

/-- Meet is idempotent. -/
theorem MultiplierStructureClass.meet_idem (structureClass : MultiplierStructureClass) :
    structureClass.meet structureClass = structureClass := by cases structureClass <;> rfl

/-- Meet is commutative. -/
theorem MultiplierStructureClass.meet_comm (lower upper : MultiplierStructureClass) :
    lower.meet upper = upper.meet lower := by cases lower <;> cases upper <;> rfl

/-- Meet is associative. -/
theorem MultiplierStructureClass.meet_assoc (lower middle upper : MultiplierStructureClass) :
    (lower.meet middle).meet upper = lower.meet (middle.meet upper) := by
  cases lower <;> cases middle <;> cases upper <;> rfl

/-- Absorption: `join a (meet a b) = a`. -/
theorem MultiplierStructureClass.join_meet_absorb (lower upper : MultiplierStructureClass) :
    lower.join (lower.meet upper) = lower := by cases lower <;> cases upper <;> rfl

/-- Absorption: `meet a (join a b) = a`. -/
theorem MultiplierStructureClass.meet_join_absorb (lower upper : MultiplierStructureClass) :
    lower.meet (lower.join upper) = lower := by cases lower <;> cases upper <;> rfl

/-- The join is an upper bound: the left operand refines it. -/
theorem MultiplierStructureClass.refines_join_left (lower upper : MultiplierStructureClass) :
    lower.refines (lower.join upper) := by cases lower <;> cases upper <;> decide

/-- The join is an upper bound: the right operand refines it. -/
theorem MultiplierStructureClass.refines_join_right (lower upper : MultiplierStructureClass) :
    upper.refines (lower.join upper) := by cases lower <;> cases upper <;> decide

/-- The join is the LEAST upper bound: anything refined by both operands is refined by the join. -/
theorem MultiplierStructureClass.join_isLeastUpperBound {lower upper bound : MultiplierStructureClass}
    (lowerRefines : lower.refines bound) (upperRefines : upper.refines bound) :
    (lower.join upper).refines bound := by
  cases lower <;> cases upper <;> first | exact lowerRefines | exact upperRefines

/-! ## The full Nuyts property table (Fig 7/9) — beyond the cube ladder

The cube ladder (`affine ⊏ cartesian ⊏ dedekind ⊏ deMorgan`) tracks the diagonal / connections / reversal axis.
Nuyts–Devriese Fig 7/9 records a FULLER property set: alongside `cartesian` / `connections` / `reversal` the
multiplier may be `cancellative` (T-slice faithful), `affine` (T-slice full — the endpoint structure),
`semicartesian` (= COPOINTED in Nuyts' later terminology — equipped with the projection `pi1 : multiplier -> Id`,
i.e. weakening: a dimension may be DISCARDED), `objectwisePointable` (a designated global point `1 -> interval`,
DISTINCT from copointedness), and `quantifiable` (T-slice right adjoint — Pi over the dimension exists, the
universal modality's left adjoint).  This section ships the per-class table over all eight properties, its
MONOTONICITY up the ladder, and its CONSISTENCY with the cube-ladder flags.

The affine multiplier's DEFINING geometry (Nuyts tech report Ex 3.3.3) is: copointed (`semicartesian` = true —
it HAS the projection / weakening) but NOT a comonad (`cartesian` = false — it LACKS the diagonal, the
duplication / contraction).  Objectwise-pointability is a SEPARATE, arity-dependent property (Ex 3.3.3:
pointable iff the cube arity is nonzero); it is NOT what characterises affine, and must not be conflated with
copointedness nor with the absence of the diagonal (see `affineClass_isCopointed_lacksDiagonal`).

The property VALUES are the Fig-7 cube-category facts; what is PROVEN here is the table's internal coherence
(monotone along the refinement ladder, consistent with `supportsDiagonal` / `supportsConnections` /
`supportsReversal`).  The genuine SEMANTIC justification — that the cube presheaf categories realize each
property — is the deferred presheaf model (`hasPresheafMultiplierModel`, `mode-12`). -/

/-- The Nuyts Fig-7/9 multiplier properties — the cube-ladder three plus the orthogonal sub-properties. -/
inductive MultiplierProperty where
  /-- The dimension action is cancellative. -/
  | cancellative
  /-- Has the endpoint projections (the affine structure). -/
  | affine
  /-- COPOINTED (Nuyts' later name for semicartesian): equipped with the projection `pi1 : multiplier -> Id` —
  the weakening that lets a dimension be DISCARDED.  TRUE for affine (the affine cube IS copointed). -/
  | semicartesian
  /-- Objectwise pointable: a designated global point `1 -> interval` (an endpoint).  DISTINCT from
  copointedness (`semicartesian`) and from the diagonal (`cartesian`); arity-dependent (Nuyts Ex 3.3.3:
  pointable iff the cube arity is nonzero), so NOT a defining invariant of the affine class. -/
  | objectwisePointable
  /-- Π over the dimension exists (the universal modality's left adjoint). -/
  | quantifiable
  /-- Has the diagonal — the comonad comultiplication (duplication / contraction).  FALSE for affine: its
  DEFINING lack (Nuyts Ex 3.3.3, the affine cube is "not a comonad"); the discriminator the affine lock
  enforces (the diagonal `pair i i` is untypeable). -/
  | cartesian
  /-- Has the monotone connections ∧ / ∨. -/
  | connections
  /-- Has the non-monotone reversal ¬. -/
  | reversal
  deriving DecidableEq

/-- ★ The **full property table** — for each structure class, which of the eight Nuyts properties holds.  The
shared base (`cancellative` / `affine` / `semicartesian` / `objectwisePointable` / `quantifiable`) holds across
the whole cube ladder (objectwise-pointability for the ladder as realized over the pointed binary interval —
the nullary / nominal case is the unpointable exception, mode-12 `voidMultiplier`); the discriminating columns
(`cartesian` / `connections` / `reversal`) route through the existing strength flags (single source of truth). -/
def MultiplierStructureClass.hasProperty (structureClass : MultiplierStructureClass) :
    MultiplierProperty → Bool
  | .cancellative => true
  | .affine => true
  | .semicartesian => true
  | .objectwisePointable => true
  | .quantifiable => true
  | .cartesian => structureClass.supportsDiagonal
  | .connections => structureClass.supportsConnections
  | .reversal => structureClass.supportsReversal

/-- The `cartesian` column of the table IS the diagonal flag (single source of truth). -/
theorem hasProperty_cartesian (structureClass : MultiplierStructureClass) :
    structureClass.hasProperty .cartesian = structureClass.supportsDiagonal := rfl

/-- The `connections` column of the table IS the connections flag. -/
theorem hasProperty_connections (structureClass : MultiplierStructureClass) :
    structureClass.hasProperty .connections = structureClass.supportsConnections := rfl

/-- The `reversal` column of the table IS the reversal flag. -/
theorem hasProperty_reversal (structureClass : MultiplierStructureClass) :
    structureClass.hasProperty .reversal = structureClass.supportsReversal := rfl

/-- Ledger: the whole cube ladder is `quantifiable` — even the affine bottom (Π over the dimension exists). -/
theorem affine_quantifiable : MultiplierStructureClass.affine.hasProperty .quantifiable = true := rfl

/-- Ledger: the whole cube ladder is `objectwisePointable` — even the affine bottom — when realized over the
pointed binary interval (the global endpoint `0`).  This records OBJECTWISE-pointability (a global point), NOT
affine's defining geometry: affine is characterised by copointedness + the ABSENCE of the diagonal
(`affineClass_isCopointed_lacksDiagonal`), and the nullary / nominal affine cube is in fact unpointable
(mode-12 `voidMultiplier`).  Theorem name kept (`affine_pointed`) as the established cross-axis ledger handle. -/
theorem affine_pointed : MultiplierStructureClass.affine.hasProperty .objectwisePointable = true := rfl

/-- ★ Ledger (the affine multiplier's DEFINING geometry, Nuyts tech report Ex 3.3.3).  The affine class is
COPOINTED — it HAS the projection / weakening (`semicartesian` = true: a dimension may be discarded) — but is
NOT a comonad: it LACKS the diagonal (`supportsDiagonal` = false: no duplication / contraction).  This — NOT
(un)pointedness — is what the affine interval lock enforces: the diagonal use `pair (var 0) (var 0)`
(duplicating the locked dimension variable) is untypeable.  Cf.
`BridgeIntervalAffineMultiplier.bridgeLacksDiagonal`. -/
theorem affineClass_isCopointed_lacksDiagonal :
    MultiplierStructureClass.affine.hasProperty .semicartesian = true
      ∧ MultiplierStructureClass.affine.supportsDiagonal = false :=
  ⟨rfl, rfl⟩

/-- ★ The property table is MONOTONE up the refinement ladder: a stronger class has every property a weaker one
has.  The discriminating structural coherence (proved by exhausting the finite ladder × property grid). -/
theorem hasProperty_mono {lower upper : MultiplierStructureClass} (refinesProof : lower.refines upper)
    (property : MultiplierProperty) (propertyHolds : lower.hasProperty property = true) :
    upper.hasProperty property = true := by
  cases lower <;> cases upper <;> cases property <;>
    first
      | rfl
      | exact absurd propertyHolds (by decide)
      | exact absurd refinesProof (by decide)

/-- Non-degeneracy: the `reversal` property is GAINED strictly at the top — affine lacks it, deMorgan has it. -/
theorem reversal_gained :
    MultiplierStructureClass.affine.hasProperty .reversal = false
      ∧ MultiplierStructureClass.deMorgan.hasProperty .reversal = true := by
  decide

/-! ## Honesty markers -/

/-- **Honesty marker.**  The SEMANTIC multiplier endofunctor + the unpointability / dimensional-splitness
criteria ARE shipped at `mode-12` (`Multiplier`, `IsUnpointable`, `IsDimensionallySplit`, the per-class
realization).  What remains deferred is the genuine PRESHEAF-category model with the full Nuyts axioms
(`mode-12` `hasPresheafMultiplierModel`).  `= false`. -/
def fxMode_hasMultiplierEndofunctorRealization : Bool := false

/-- **Honesty marker.**  The MODAL CONSEQUENCES — the Gel / Glue / Weld / transpension CONSTRUCTIONS each class
unlocks (Fig 9's right-hand side) — remain deferred; `mode-11` ships the transpension adjunction + the named
target zoo, not the per-operator recoveries.  `= false`. -/
def fxMode_hasMultiplierModalConsequences : Bool := false

/-- **Honesty marker.**  The per-class property TABLE over the eight Nuyts Fig-7/9 properties (cancellative /
affine / semicartesian / objectwisePointable / quantifiable + the cube-ladder three) IS now shipped (`hasProperty` +
monotonicity + flag-consistency).  What remains deferred is the SEMANTIC justification of the property values
(that the cube presheaf categories realize them) — the presheaf model, `mode-12`.  `= false`. -/
def fxMode_hasFullMultiplierPropertyTable : Bool := false

end FX1Poly.Axis
