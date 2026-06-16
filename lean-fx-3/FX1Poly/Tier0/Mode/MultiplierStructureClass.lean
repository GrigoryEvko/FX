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

DEFERRED (recorded by `= false` markers):
  * the SEMANTIC multiplier — the actual endofunctor on a base category realizing each class, with the
    unpointability / dimensional-splitness criteria — `hasMultiplierEndofunctorRealization = false`
    (`mode-12`);
  * the MODAL CONSEQUENCES — the Gel / Glue / Weld / transpension / amazing-right-adjoint CONSTRUCTIONS each
    class unlocks (Fig 9's right-hand side) — `hasMultiplierModalConsequences = false` (`mode-11`);
  * the full per-cell Nuyts Fig-7/9 correspondence beyond the cube ladder (cancellative / semicartesian /
    pointed sub-properties) — `hasFullMultiplierPropertyTable = false`.

This `mode-2` discharges `mode-1`'s `fxMode_hasModeTheoryStructureClass` deferral (the structure-class layer).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

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

/-- Whether the class has the diagonal (cartesian and above). -/
def MultiplierStructureClass.supportsDiagonal : MultiplierStructureClass → Bool
  | .affine => false
  | .cartesian => true
  | .dedekind => true
  | .deMorgan => true

/-- Whether the class has the monotone connections (Dedekind and above). -/
def MultiplierStructureClass.supportsConnections : MultiplierStructureClass → Bool
  | .affine => false
  | .cartesian => false
  | .dedekind => true
  | .deMorgan => true

/-- Whether the class has the non-monotone reversal (De Morgan only). -/
def MultiplierStructureClass.supportsReversal : MultiplierStructureClass → Bool
  | .affine => false
  | .cartesian => false
  | .dedekind => false
  | .deMorgan => true

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
  refine ⟨?_, ?_, ?_⟩ <;> decide

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

/-! ## Honesty markers -/

/-- **Honesty marker.**  The SEMANTIC multiplier — the actual endofunctor on a base category realizing each
class, with the unpointability / dimensional-splitness criteria — is `mode-12`, deferred.  `= false`. -/
def fxMode_hasMultiplierEndofunctorRealization : Bool := false

/-- **Honesty marker.**  The MODAL CONSEQUENCES — the Gel / Glue / Weld / transpension / amazing-right-adjoint
CONSTRUCTIONS each class unlocks (Fig 9's right-hand side) — are `mode-11`, deferred.  `= false`. -/
def fxMode_hasMultiplierModalConsequences : Bool := false

/-- **Honesty marker.**  The full per-cell Nuyts Fig-7/9 property table beyond the cube ladder (cancellative /
semicartesian / pointed sub-properties) is deferred.  `= false`. -/
def fxMode_hasFullMultiplierPropertyTable : Bool := false

end FX1Poly.Tier0
