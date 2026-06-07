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
`min`, the weakest-link minimum — same single-idempotent-op structure, same non-fit; PROVEN below on par with
effect via `trustIsNotLawfulOrderedGradeSemiring` + `trustIsLawfulBoundedJoinSemilattice`.)

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
cannot ride the semiring `HasGradeOver` engine; it needs a lattice-graded one.  (Trust is the order-DUAL —
add = mul = `min`, the weakest-link minimum — and is PROVEN below on par with effect, via
`trustIsNotLawfulOrderedGradeSemiring` + `trustIsLawfulBoundedJoinSemilattice`, not merely asserted.) -/
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

/-! ## The trust dual — same boundary, order-dual combine (weakest-link minimum)

Trust (§6.3 Dim 9: `Verified > Tested > Sorry > Assumed > External`) propagates as the MINIMUM through the call
graph — the weakest link wins.  This is the order-DUAL of effect: where effect ACCUMULATES upward from a pure
bottom, trust DEGRADES downward from a trusted top, both via a single idempotent commutative op with no
annihilating second operation.  So trust meets the same semiring boundary as effect and inhabits the same
bounded-idempotent-commutative-monoid structure — here PROVEN, not (as the dimension classification previously
recorded) merely asserted by analogy. -/

/-- A minimal trust grade: `trustedGrade` (Verified-like — the TOP of the trust order, the combine identity)
and `untrustedGrade` (External-like — the absorbing element).  Two elements suffice to exhibit the
semilattice-vs-semiring boundary, with the order dualized relative to `EffectGrade`. -/
inductive TrustGrade where
  | trustedGrade
  | untrustedGrade
  deriving DecidableEq

/-- Trust combine — the weakest link wins (§6.3: trust propagates as the minimum).  Any `untrustedGrade` input
makes the whole `untrustedGrade`; `trustedGrade` is the identity.  Full 2x2 enumeration, propext-free. -/
def TrustGrade.weakestLink : TrustGrade → TrustGrade → TrustGrade
  | .trustedGrade, .trustedGrade => .trustedGrade
  | .trustedGrade, .untrustedGrade => .untrustedGrade
  | .untrustedGrade, .trustedGrade => .untrustedGrade
  | .untrustedGrade, .untrustedGrade => .untrustedGrade

/-- Trust order: `untrustedGrade ≤ trustedGrade` (External is the bottom of the trust order — the order-dual of
`EffectGrade.le`). -/
def TrustGrade.le : TrustGrade → TrustGrade → Bool
  | .trustedGrade, .trustedGrade => true
  | .trustedGrade, .untrustedGrade => false
  | .untrustedGrade, .trustedGrade => true
  | .untrustedGrade, .untrustedGrade => true

/-- The candidate ordered-semiring structure over `TrustGrade`: `add` (parallel) AND `mul` (sequential) are
BOTH the weakest-link minimum — the order-dual of the effect join.  Trust likewise has no distinct annihilating
second operation. -/
def trustSemiringCandidate : OrderedGradeSemiring where
  Carrier := TrustGrade
  zero := .trustedGrade
  one := .untrustedGrade
  add := TrustGrade.weakestLink
  mul := TrustGrade.weakestLink
  le := TrustGrade.le
  carrierDecEq := instDecidableEqTrustGrade

/-- Concrete witness: the weakest-link minimum does not annihilate — `weakestLink untrusted trusted = untrusted
≠ trusted`.  (The combine identity is `trustedGrade`; degrading back to it would require discarding the
untrusted input, which trust never does — the dual of the effect non-annihilation.) -/
theorem trustWeakestLinkAnnihilation_concretelyFails :
    TrustGrade.weakestLink TrustGrade.untrustedGrade TrustGrade.trustedGrade ≠ TrustGrade.trustedGrade := by
  decide

/-- **Trust is NOT a lawful ordered grade semiring** — the order-dual of the effect boundary.  If it were
lawful, `mul_zero untrusted` would force `weakestLink untrusted trusted = trusted`, but the weakest link
degrades (`= untrusted`).  Sequential trust composition is the minimum, which has no annihilator — so the trust
family cannot ride the semiring `HasGradeOver` engine either; it needs the lattice-graded one. -/
theorem trustIsNotLawfulOrderedGradeSemiring :
    ¬ IsLawfulOrderedGradeSemiring trustSemiringCandidate := by
  intro lawful
  have annihilationFails : TrustGrade.untrustedGrade = TrustGrade.trustedGrade :=
    lawful.mul_zero TrustGrade.untrustedGrade
  exact absurd annihilationFails (by decide)

/-- The trust bounded join-semilattice: the weakest-link combine presented as the monoid op, with the trusted
top `trustedGrade` as the identity (`bottom`).  The same bounded-idempotent-commutative-monoid structure as
effect, order-dualized. -/
def trustLattice : BoundedJoinSemilattice where
  Carrier := TrustGrade
  bottom := .trustedGrade
  join := TrustGrade.weakestLink
  carrierDecEq := instDecidableEqTrustGrade

/-- **Trust IS a verified bounded join-semilattice** — commutative, associative, idempotent combine with the
trusted identity.  This upgrades the trust dimension from the earlier "classified by analogy" note to a proof on
par with `effectIsLawfulBoundedJoinSemilattice`: BOTH semilattice-family dimensions are now machine-checked. -/
theorem trustIsLawfulBoundedJoinSemilattice : IsLawfulBoundedJoinSemilattice trustLattice where
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

/-- Ledger (the order-dual BOUNDARY): trust is a bounded semilattice, NOT a semiring — now MACHINE-CHECKED on
par with effect (`trustIsNotLawfulOrderedGradeSemiring` + `trustIsLawfulBoundedJoinSemilattice`), no longer
asserted by analogy.  add = mul = `min`, the weakest-link minimum, the single-idempotent-op non-fit. -/
theorem trust_isBoundedSemilattice :
    GradedDimensionName.trust.gradeAlgebraOf = .boundedSemilattice := rfl

/-! ## Lattice-family composition — the lattice dimensions compose POINTWISE

The multi-dimensional thesis (§1.3 / §6.8: "twenty-one dimensions compose in one signature") for the LATTICE
family — the analogue of the resource family's grade VECTOR (the `OrderedGradeSemiring` product behind
`HasGradeOver`).  The §6.8 effect / trust / ... bounded-join-semilattice dimensions combine componentwise: the
product of two bounded join-semilattices is a bounded join-semilattice, and its laws follow from the two
components' WITHOUT re-proof.  So any tuple of lawful lattice dimensions is itself one lawful lattice dimension —
graded composition for the lattice family, mirroring the no-cascade composition the resource family already has. -/

/-- Init-only pair congruence (no `congrArg₂` outside Mathlib): a product equality from its two component
equalities.  The lattice-product laws are all componentwise, so this is the only glue they need. -/
theorem pairEqOfComponents {firstType secondType : Type}
    {firstLeft firstRight : firstType} {secondLeft secondRight : secondType}
    (firstComponentEq : firstLeft = firstRight) (secondComponentEq : secondLeft = secondRight) :
    (firstLeft, secondLeft) = (firstRight, secondRight) := by
  rw [firstComponentEq, secondComponentEq]

/-- **The pointwise product of two bounded join-semilattices.**  Carrier is the product, bottom is the pair of
bottoms, join is componentwise.  The composite of two lattice dimensions into one — the lattice-family analogue
of the resource grade vector. -/
def BoundedJoinSemilattice.product (firstLattice secondLattice : BoundedJoinSemilattice) :
    BoundedJoinSemilattice where
  Carrier := firstLattice.Carrier × secondLattice.Carrier
  bottom := (firstLattice.bottom, secondLattice.bottom)
  join := fun firstPair secondPair =>
    (firstLattice.join firstPair.1 secondPair.1, secondLattice.join firstPair.2 secondPair.2)
  carrierDecEq := by
    haveI := firstLattice.carrierDecEq
    haveI := secondLattice.carrierDecEq
    exact inferInstance

/-- **Lattice composition is law-preserving (no re-proof).**  The pointwise product of two LAWFUL bounded
join-semilattices is itself lawful — every law (comm / assoc / idempotent / bottom-identity) holds componentwise,
so it follows from the two components' laws with only the pair-congruence glue.  This is the formal "the lattice
dimensions compose" theorem: a grade vector over any tuple of effect-family dimensions is a single lawful lattice
dimension, exactly as the resource grade vector composes the semiring dimensions. -/
theorem BoundedJoinSemilattice.productIsLawful
    {firstLattice secondLattice : BoundedJoinSemilattice}
    (firstLawful : IsLawfulBoundedJoinSemilattice firstLattice)
    (secondLawful : IsLawfulBoundedJoinSemilattice secondLattice) :
    IsLawfulBoundedJoinSemilattice (firstLattice.product secondLattice) where
  join_comm := fun firstPair secondPair =>
    pairEqOfComponents (firstLawful.join_comm firstPair.1 secondPair.1)
      (secondLawful.join_comm firstPair.2 secondPair.2)
  join_assoc := fun firstPair secondPair thirdPair =>
    pairEqOfComponents (firstLawful.join_assoc firstPair.1 secondPair.1 thirdPair.1)
      (secondLawful.join_assoc firstPair.2 secondPair.2 thirdPair.2)
  join_idempotent := fun pair =>
    pairEqOfComponents (firstLawful.join_idempotent pair.1) (secondLawful.join_idempotent pair.2)
  bottom_join := fun pair =>
    pairEqOfComponents (firstLawful.bottom_join pair.1) (secondLawful.bottom_join pair.2)
  join_bottom := fun pair =>
    pairEqOfComponents (firstLawful.join_bottom pair.1) (secondLawful.join_bottom pair.2)

/-- The concrete `effect × trust` composite lattice — two genuine §6.8 lattice dimensions composed. -/
def effectTrustProductLattice : BoundedJoinSemilattice :=
  effectLattice.product trustLattice

/-- **Effect × trust IS a lawful bounded join-semilattice** — the first concrete witness that two real §6.8
lattice dimensions compose into one lawful lattice dimension, via `productIsLawful` with no per-product proof. -/
theorem effectTrustProductIsLawful :
    IsLawfulBoundedJoinSemilattice effectTrustProductLattice :=
  BoundedJoinSemilattice.productIsLawful effectIsLawfulBoundedJoinSemilattice
    trustIsLawfulBoundedJoinSemilattice

end FX1Poly.Modal
