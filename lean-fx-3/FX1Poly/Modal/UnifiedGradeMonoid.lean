import FX1Poly.Modal.EffectLatticeClassification

/-! # FX1Poly/Modal/UnifiedGradeMonoid
    — the unified grade VECTOR across BOTH dimension families: the honest "twenty-one dimensions compose"
      (§1.3 / §6.1 / §6.8), with the §6.1-vs-DIM-CLASS tension resolved

§6.1 presents the grade vector as "the PRODUCT of all [dimension semirings]".  But DIM-CLASS proved that the
effect / trust dimensions are NOT semirings — they are bounded join-semilattices (no annihilating sequential
`mul`).  So the grade vector is NOT a pure semiring product.  This file resolves the tension honestly: the layer
the WHOLE vector shares — the §6.1 PARALLEL-use combine (`+`) — is a COMMUTATIVE MONOID, and BOTH families
project onto it (`OrderedGradeSemiring`'s additive part, `BoundedJoinSemilattice`'s join).  The grade vector is
the PRODUCT of those commutative monoids, mixing resource and co-effect dimensions freely.  (The SEQUENTIAL
`mul` — §6.2's App-rule scaling — is the family-specific layer: a genuine annihilating `mul` for the resource
semirings, the idempotent join-as-`mul` for the lattices.  The combine layer is uniform; the scale layer is not.)

## What this file ships (all zero-axiom)

  * `CommutativeGradeMonoid` + `IsLawfulCommutativeGradeMonoid` — the unified combine layer (carrier + identity
    + commutative-associative-unital combine), the structure BOTH dimension families inhabit.
  * `OrderedGradeSemiring.toCommutativeGradeMonoid` (+ `_isLawful`) — every resource dimension projects, its
    monoid laws read off its `add_comm` / `add_assoc` / `zero_add` / `add_zero`.
  * `BoundedJoinSemilattice.toCommutativeGradeMonoid` (+ `_isLawful`) — every effect-family dimension projects,
    its monoid laws read off its `join_comm` / `join_assoc` / `bottom_join` / `join_bottom`.
  * `CommutativeGradeMonoid.product` (+ `productIsLawful`) — the grade VECTOR: the pointwise product of two
    lawful grade monoids is a lawful grade monoid, every law componentwise.
  * `securityEffectGradeMonoid` (+ `IsLawful`) — the FIRST concrete CROSS-FAMILY witness: a resource dimension
    (security, a semiring) and a co-effect dimension (effect, a lattice) compose into ONE lawful grade monoid.
    The honest "a semiring dimension and a lattice dimension live in the same grade vector".

## Zero-axiom verification

Two `Type`/`Prop` structures, two projections (record literals), two law-transport theorems (field-by-field
re-export of the source laws), the product (record literal + `inferInstance` for the pair `DecidableEq`) and its
lawfulness (componentwise via the shipped `pairEqOfComponents` glue), and the concrete witness.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **The unified combine layer.**  A carrier with a distinguished `identity` and a binary `combine` — the §6.1
PARALLEL-use operation (`+`) that EVERY dimension (resource semiring or effect-family lattice) shares.  Strictly
weaker than `OrderedGradeSemiring` (no `mul`) and than `BoundedJoinSemilattice` (no idempotence): exactly the
common structure the whole grade vector inhabits. -/
structure CommutativeGradeMonoid where
  Carrier : Type
  identity : Carrier
  combine : Carrier → Carrier → Carrier
  carrierDecEq : DecidableEq Carrier

/-- The commutative-grade-monoid laws: `combine` is a commutative monoid with `identity` as its unit. -/
structure IsLawfulCommutativeGradeMonoid (monoid : CommutativeGradeMonoid) : Prop where
  combine_comm : ∀ firstGrade secondGrade : monoid.Carrier,
    monoid.combine firstGrade secondGrade = monoid.combine secondGrade firstGrade
  combine_assoc : ∀ firstGrade secondGrade thirdGrade : monoid.Carrier,
    monoid.combine (monoid.combine firstGrade secondGrade) thirdGrade =
      monoid.combine firstGrade (monoid.combine secondGrade thirdGrade)
  identity_combine : ∀ someGrade : monoid.Carrier, monoid.combine monoid.identity someGrade = someGrade
  combine_identity : ∀ someGrade : monoid.Carrier, monoid.combine someGrade monoid.identity = someGrade

/-- **Every resource dimension projects to the unified combine layer** — keep `add` and `zero`, forget `mul`. -/
def OrderedGradeSemiring.toCommutativeGradeMonoid (semiring : OrderedGradeSemiring) :
    CommutativeGradeMonoid where
  Carrier := semiring.Carrier
  identity := semiring.zero
  combine := semiring.add
  carrierDecEq := semiring.carrierDecEq

/-- A lawful resource semiring projects to a lawful grade monoid — the monoid laws ARE the semiring's additive
commutative-monoid laws. -/
theorem OrderedGradeSemiring.toCommutativeGradeMonoid_isLawful {semiring : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring semiring) :
    IsLawfulCommutativeGradeMonoid semiring.toCommutativeGradeMonoid where
  combine_comm := lawful.add_comm
  combine_assoc := lawful.add_assoc
  identity_combine := lawful.zero_add
  combine_identity := lawful.add_zero

/-- **Every effect-family dimension projects to the unified combine layer** — `join` is the combine, `bottom`
the identity (the lattice's idempotence is extra structure the monoid layer drops). -/
def BoundedJoinSemilattice.toCommutativeGradeMonoid (lattice : BoundedJoinSemilattice) :
    CommutativeGradeMonoid where
  Carrier := lattice.Carrier
  identity := lattice.bottom
  combine := lattice.join
  carrierDecEq := lattice.carrierDecEq

/-- A lawful bounded join-semilattice projects to a lawful grade monoid — the monoid laws ARE the lattice's
join commutative-monoid laws. -/
theorem BoundedJoinSemilattice.toCommutativeGradeMonoid_isLawful {lattice : BoundedJoinSemilattice}
    (lawful : IsLawfulBoundedJoinSemilattice lattice) :
    IsLawfulCommutativeGradeMonoid lattice.toCommutativeGradeMonoid where
  combine_comm := lawful.join_comm
  combine_assoc := lawful.join_assoc
  identity_combine := lawful.bottom_join
  combine_identity := lawful.join_bottom

/-- **The grade VECTOR — the pointwise product of two grade monoids.**  Carrier is the product, identity is the
pair of identities, combine is componentwise.  Mixes dimensions from EITHER family (each already projected to a
grade monoid). -/
def CommutativeGradeMonoid.product (firstMonoid secondMonoid : CommutativeGradeMonoid) :
    CommutativeGradeMonoid where
  Carrier := firstMonoid.Carrier × secondMonoid.Carrier
  identity := (firstMonoid.identity, secondMonoid.identity)
  combine := fun firstPair secondPair =>
    (firstMonoid.combine firstPair.1 secondPair.1, secondMonoid.combine firstPair.2 secondPair.2)
  carrierDecEq := by
    haveI := firstMonoid.carrierDecEq
    haveI := secondMonoid.carrierDecEq
    exact inferInstance

/-- **The grade vector is law-preserving (no re-proof).**  The pointwise product of two LAWFUL grade monoids is
lawful — every commutative-monoid law holds componentwise.  So a grade vector over ANY tuple of dimensions, drawn
from EITHER family, is itself one lawful grade monoid: the formal "the twenty-one dimensions compose at the
combine layer". -/
theorem CommutativeGradeMonoid.productIsLawful
    {firstMonoid secondMonoid : CommutativeGradeMonoid}
    (firstLawful : IsLawfulCommutativeGradeMonoid firstMonoid)
    (secondLawful : IsLawfulCommutativeGradeMonoid secondMonoid) :
    IsLawfulCommutativeGradeMonoid (firstMonoid.product secondMonoid) where
  combine_comm := fun firstPair secondPair =>
    pairEqOfComponents (firstLawful.combine_comm firstPair.1 secondPair.1)
      (secondLawful.combine_comm firstPair.2 secondPair.2)
  combine_assoc := fun firstPair secondPair thirdPair =>
    pairEqOfComponents (firstLawful.combine_assoc firstPair.1 secondPair.1 thirdPair.1)
      (secondLawful.combine_assoc firstPair.2 secondPair.2 thirdPair.2)
  identity_combine := fun pair =>
    pairEqOfComponents (firstLawful.identity_combine pair.1) (secondLawful.identity_combine pair.2)
  combine_identity := fun pair =>
    pairEqOfComponents (firstLawful.combine_identity pair.1) (secondLawful.combine_identity pair.2)

/-- The cross-family grade vector `security × effect` — a RESOURCE dimension (security, a semiring) and a
CO-EFFECT dimension (effect, a lattice) in one grade monoid. -/
def securityEffectGradeMonoid : CommutativeGradeMonoid :=
  fxSecuritySemiring.toCommutativeGradeMonoid.product effectLattice.toCommutativeGradeMonoid

/-- **A semiring dimension and a lattice dimension live in the SAME grade vector** — `security × effect` is a
lawful grade monoid, the first concrete cross-family composition, via `productIsLawful` with no per-product
proof.  The honest realization of §6.1's "the dimensions compose in one signature" across the §6.8 family split. -/
theorem securityEffectGradeMonoidIsLawful :
    IsLawfulCommutativeGradeMonoid securityEffectGradeMonoid :=
  CommutativeGradeMonoid.productIsLawful
    (fxSecuritySemiring.toCommutativeGradeMonoid_isLawful fxSecuritySemiring_isLawful)
    (effectLattice.toCommutativeGradeMonoid_isLawful effectIsLawfulBoundedJoinSemilattice)

end FX1Poly.Modal
