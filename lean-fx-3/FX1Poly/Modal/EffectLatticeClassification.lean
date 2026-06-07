import FX1Poly.Modal.ResourceGraded

/-! # FX1Poly/Modal/EffectLatticeClassification
    — which of the 21 dimensions the generic `HasGradeOver` semiring engine covers, and a FORMAL proof of
      the limit: the EFFECT family is a bounded join-semilattice, NOT an ordered grade semiring (§6.3 / §9.3)

The generic `HasGradeOver R` engine (DIM5) is built over an `OrderedGradeSemiring` — a structure with a
distinct annihilating multiplication (§6.1: `0 * r = 0`).  The RESOURCE / co-effect dimensions fit it: usage
`{0,1,ω}` (DIM2), security `{unclassified < classified}` (DIM5), and the complexity / space / precision
`Nat`-semiring (DIM3).  This file proves the BOUNDARY: the EFFECT family does NOT fit, and characterizes what
it is instead.

The DIM5-era memory noted informally that "effect/trust don't fit `OrderedGradeSemiring`, they fail
annihilation."  This file upgrades that hand-wave to a machine-checked, zero-axiom theorem.

## Why effect is not a semiring

A grade semiring needs `add` (parallel combine) AND a distinct `mul` (sequential scale) with annihilation
`mul a zero = zero`.  Security fits because its `mul` is the MEET (`classified * unclassified = unclassified`
— §6.3 ghost-on-secret-leaks-nothing), which annihilates at `zero = unclassified`.  Effect has NO such dual:
§9.3 makes effects MONOTONIC — sequential composition ACCUMULATES, never removes, so the only sound `mul` is
the JOIN itself.  With `mul = add = join`, annihilation fails: `mul impure pure = join impure pure = impure ≠
pure`.  `effectIsNotLawfulOrderedGradeSemiring` proves exactly this.  (Trust is the order-DUAL: add = mul =
`min`, the weakest-link minimum — same single-idempotent-op structure, same non-fit; classified as a
semilattice here, proof analogous.)

## What effect IS

A bounded join-semilattice `(EffectGrade, join, pureEffect)` — commutative, associative, idempotent join with
a bottom.  `effectIsLawfulBoundedJoinSemilattice` proves the full law set.  So the effect-family dimensions
need a separate LATTICE-graded engine, NOT the semiring `HasGradeOver`.

## The classification

`GradedDimensionName.gradeAlgebraOf` records which §6 dimension carries which algebra: the resource dims are
`orderedSemiring`, the effect/trust dims are `boundedSemilattice`.  The `…_isOrderedSemiring` /
`…_isBoundedSemilattice` rfl-facts pin it.

## Zero-axiom verification

`EffectGrade` is a 2-element inductive; the lattice laws close by `cases <;> rfl`; the negative result reads
off `lawful.mul_zero impure` (defeq `impure = pure`) and refutes it by `decide`; the catalog is a
full-enumeration match.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-! ## The effect grade and its join -/

/-- A minimal effect grade: `pureEffect` (Tot, the bottom) and `impureEffect` (any effect performed).  Enough
to exhibit the semilattice-vs-semiring boundary; the full §9.4 effect lattice is the powerset extension. -/
inductive EffectGrade where
  | pureEffect
  | impureEffect
  deriving DecidableEq

/-- Effect join — effects ACCUMULATE (§9.3 monotonicity: once impure, always impure).  Full 2x2 enumeration,
propext-free. -/
def EffectGrade.join : EffectGrade → EffectGrade → EffectGrade
  | .pureEffect, .pureEffect => .pureEffect
  | .pureEffect, .impureEffect => .impureEffect
  | .impureEffect, .pureEffect => .impureEffect
  | .impureEffect, .impureEffect => .impureEffect

/-- Effect order: `pureEffect ≤ impureEffect` (Tot is the bottom). -/
def EffectGrade.le : EffectGrade → EffectGrade → Bool
  | .pureEffect, .pureEffect => true
  | .pureEffect, .impureEffect => true
  | .impureEffect, .pureEffect => false
  | .impureEffect, .impureEffect => true

/-! ## The negative result — effect is NOT an ordered grade semiring -/

/-- The candidate ordered-semiring structure over `EffectGrade`: `add` (parallel) AND `mul` (sequential) are
BOTH the join, because §9.3 effects accumulate in both directions with no removing/annihilating operation. -/
def effectSemiringCandidate : OrderedGradeSemiring where
  Carrier := EffectGrade
  zero := .pureEffect
  one := .impureEffect
  add := EffectGrade.join
  mul := EffectGrade.join
  le := EffectGrade.le
  carrierDecEq := instDecidableEqEffectGrade

/-- Concrete witness: the join does not annihilate — `join impure pure = impure ≠ pure`.  (Contrast security,
whose `mul` is the MEET: `classified * unclassified = unclassified = zero`.) -/
theorem effectJoinAnnihilation_concretelyFails :
    EffectGrade.join EffectGrade.impureEffect EffectGrade.pureEffect ≠ EffectGrade.pureEffect := by
  decide

/-- **Effect is NOT a lawful ordered grade semiring** (the §6.3 / §9.3 boundary of the `HasGradeOver` engine).
If it were lawful, `mul_zero impure` would force `join impure pure = pure`, but the join accumulates
(`= impure`).  Sequential effect composition is the join, which has no annihilator — so the effect family
cannot ride the semiring `HasGradeOver` engine; it needs a lattice-graded one. -/
theorem effectIsNotLawfulOrderedGradeSemiring :
    ¬ IsLawfulOrderedGradeSemiring effectSemiringCandidate := by
  intro lawful
  have annihilationFails : EffectGrade.impureEffect = EffectGrade.pureEffect :=
    lawful.mul_zero EffectGrade.impureEffect
  exact absurd annihilationFails (by decide)

/-- The CONTRAST: security DOES annihilate (`mul = meet`, so `mul a zero = zero`) — re-exported from the
shipped `fxSecuritySemiring_isLawful`, the reason security fits the semiring engine where effect cannot. -/
theorem securityHasAnnihilation :
    ∀ someGrade : SecurityGrade,
      fxSecuritySemiring.mul someGrade fxSecuritySemiring.zero = fxSecuritySemiring.zero :=
  fxSecuritySemiring_isLawful.mul_zero

/-! ## The positive structure — effect IS a bounded join-semilattice -/

/-- A bounded join-semilattice: a carrier with a bottom and an idempotent commutative-associative join.  The
algebra the effect-family dimensions live in (the §9.3 effect lattice), distinct from the `OrderedGradeSemiring`
the resource dimensions use. -/
structure BoundedJoinSemilattice where
  Carrier : Type
  bottom : Carrier
  join : Carrier → Carrier → Carrier
  carrierDecEq : DecidableEq Carrier

/-- The bounded-join-semilattice laws: join is a commutative idempotent monoid with `bottom` as identity. -/
structure IsLawfulBoundedJoinSemilattice (lattice : BoundedJoinSemilattice) : Prop where
  join_comm : ∀ firstGrade secondGrade : lattice.Carrier,
    lattice.join firstGrade secondGrade = lattice.join secondGrade firstGrade
  join_assoc : ∀ firstGrade secondGrade thirdGrade : lattice.Carrier,
    lattice.join (lattice.join firstGrade secondGrade) thirdGrade =
      lattice.join firstGrade (lattice.join secondGrade thirdGrade)
  join_idempotent : ∀ someGrade : lattice.Carrier, lattice.join someGrade someGrade = someGrade
  bottom_join : ∀ someGrade : lattice.Carrier, lattice.join lattice.bottom someGrade = someGrade
  join_bottom : ∀ someGrade : lattice.Carrier, lattice.join someGrade lattice.bottom = someGrade

/-- The effect bounded join-semilattice. -/
def effectLattice : BoundedJoinSemilattice where
  Carrier := EffectGrade
  bottom := .pureEffect
  join := EffectGrade.join
  carrierDecEq := instDecidableEqEffectGrade

/-- **Effect IS a verified bounded join-semilattice.**  Commutative, associative, idempotent join with the
pure bottom — the algebra the effect family genuinely inhabits, in place of the (failed) ordered semiring. -/
theorem effectIsLawfulBoundedJoinSemilattice : IsLawfulBoundedJoinSemilattice effectLattice where
  join_comm := fun firstGrade secondGrade => by cases firstGrade <;> cases secondGrade <;> rfl
  join_assoc := fun firstGrade secondGrade thirdGrade => by
    cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl
  join_idempotent := fun someGrade => by cases someGrade <;> rfl
  bottom_join := fun someGrade => by cases someGrade <;> rfl
  join_bottom := fun someGrade => by cases someGrade <;> rfl

/-! ## The dimension classification -/

/-- The two graded-algebra classes a §6 dimension can carry. -/
inductive DimensionGradeAlgebra where
  | orderedSemiring
  | boundedSemilattice

/-- The §6 dimensions that carry a grade algebra (the ones the generic-engine question is about). -/
inductive GradedDimensionName where
  | usage
  | security
  | complexity
  | space
  | precision
  | effect
  | trust

/-- **The classification.**  Resource / co-effect dimensions (distinct annihilating `mul`) are ordered
semirings — covered by `HasGradeOver`; the effect / trust dimensions (single idempotent op, no annihilator)
are bounded semilattices — NOT covered.  Full enumeration, no wildcard. -/
def GradedDimensionName.gradeAlgebraOf : GradedDimensionName → DimensionGradeAlgebra
  | .usage => .orderedSemiring
  | .security => .orderedSemiring
  | .complexity => .orderedSemiring
  | .space => .orderedSemiring
  | .precision => .orderedSemiring
  | .effect => .boundedSemilattice
  | .trust => .boundedSemilattice

/-- Ledger: usage is an ordered semiring (shipped `fxUsageSemiring_isLawful`). -/
theorem usage_isOrderedSemiring :
    GradedDimensionName.usage.gradeAlgebraOf = .orderedSemiring := rfl

/-- Ledger: security is an ordered semiring (shipped `fxSecuritySemiring_isLawful`). -/
theorem security_isOrderedSemiring :
    GradedDimensionName.security.gradeAlgebraOf = .orderedSemiring := rfl

/-- Ledger: complexity / space is an ordered semiring (shipped `fxComplexitySemiring_isLawful`). -/
theorem complexity_isOrderedSemiring :
    GradedDimensionName.complexity.gradeAlgebraOf = .orderedSemiring := rfl

/-- Ledger (the BOUNDARY): effect is a bounded semilattice, NOT a semiring (proved by
`effectIsNotLawfulOrderedGradeSemiring` + `effectIsLawfulBoundedJoinSemilattice`). -/
theorem effect_isBoundedSemilattice :
    GradedDimensionName.effect.gradeAlgebraOf = .boundedSemilattice := rfl

/-- Ledger: trust is a bounded semilattice (the order-dual of effect: add = mul = `min`, the weakest-link
minimum — same single-idempotent-op non-fit; classified by analogy to the proved effect case). -/
theorem trust_isBoundedSemilattice :
    GradedDimensionName.trust.gradeAlgebraOf = .boundedSemilattice := rfl

end FX1Poly.Modal
