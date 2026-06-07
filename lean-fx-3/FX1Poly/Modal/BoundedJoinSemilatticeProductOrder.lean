import FX1Poly.Modal.BoundedJoinSemilatticeUniversal

/-! # FX1Poly/Modal/BoundedJoinSemilatticeProductOrder
    — join monotonicity + the product order is COMPONENTWISE: the order-theoretic completion of lattice-family
      grade-vector composition

The DIM-CLASS lattice engine now has the algebra (`IsLawfulBoundedJoinSemilattice`), the induced order
(`le` + the partial-order laws, DIM-CLASS-order #912), the universal property (`join_isLeastUpperBound`,
DIM-CLASS-lub #916), and the pointwise product lattice (`product` + `productIsLawful`, DIM-CLASS-product #911).
This file closes the composition story on the ORDER side: it proves that the GRADE-VECTOR order — the order of
the product lattice that combines several lattice dimensions — is exactly the CONJUNCTION of the per-dimension
orders, and that `join` is MONOTONE.

## Why this matters (§6.2 subsumption for the lattice family, at the vector level)

§6.2's subsumption rule lets a value at grade `r` be used where grade `s` is expected when `r ≤ s`.  For a single
lattice dimension that is the induced `le`.  For the full GRADE VECTOR (a tuple of lattice dimensions), what is
the subsumption order?  `productLe_iff` answers it: `firstVector ≤ secondVector` in the product lattice IFF
`firstVector ≤ secondVector` in EVERY component dimension.  So multi-dimensional grade subsumption decomposes —
a value's grade vector is subsumed exactly when it is subsumed dimension-by-dimension.  This is the
order-theoretic foundation of "the twenty-one dimensions compose in one signature" (§1.3) for the lattice
family: the combined order IS the per-dimension orders, with no cross-dimension coupling.

## What lands here (all zero-axiom)

  * `join_mono` — `join` is MONOTONE in both arguments (`a ≤ a'` and `b ≤ b'` give `join a b ≤ join a' b'`),
    generic over every lattice dimension.  Derived from `le_trans` + `le_join_left`/`le_join_right` + `join_le`.
    This is what makes grade COMBINATION well-behaved: combining stronger grades yields a stronger result.
  * `productLe_iff` — **the product order is componentwise**: `(lattice1.product lattice2).le firstPair
    secondPair ↔ lattice1.le firstPair.1 secondPair.1 ∧ lattice2.le firstPair.2 secondPair.2`.  Forward by
    `congrArg Prod.fst`/`Prod.snd` (the product `le` is a pair equality); backward by the shipped
    `pairEqOfComponents`.  Generic over any two lattice dimensions.
  * `effectTrustProductLe_iff` / `overflowEffectProductLe_iff` — the concrete grade-vector orders decompose
    componentwise, including `overflowEffectProductLe_iff` which has the NON-CHAIN overflow diamond as a factor
    (the decomposition is shape-agnostic: it does not care whether a component is a chain or an antichain-bearing
    diamond).
  * `effectTrustVectorSubsumes` — a concrete subsumption witness: `(pure, trusted) ≤ (impure, untrusted)` in the
    effect×trust vector, because it holds in BOTH components (`effectLe_pure_impure` + `trustLe_trusted_untrusted`).

## Zero-axiom verification

`join_mono` composes the shipped order/lub lemmas; `productLe_iff` is `congrArg Prod.fst`/`Prod.snd` (forward,
the product `le` unfolds to a pair equality) and `pairEqOfComponents` (backward, the Init-only pair congruence);
the concrete results specialize.  No `Prod.mk.injEq` (which is propext-backed) — the iff is proved by explicit
forward/backward functions.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **`join` is monotone.**  `a ≤ a'` and `b ≤ b'` give `join a b ≤ join a' b'` — combining stronger grades
yields a stronger combined grade.  Generic over every lattice dimension; derived from `le_trans` +
`le_join_left`/`le_join_right` + `join_le`. -/
theorem BoundedJoinSemilattice.join_mono {lattice : BoundedJoinSemilattice}
    (lawful : IsLawfulBoundedJoinSemilattice lattice)
    {firstLower firstUpper secondLower secondUpper : lattice.Carrier}
    (firstLe : lattice.le firstLower firstUpper) (secondLe : lattice.le secondLower secondUpper) :
    lattice.le (lattice.join firstLower secondLower) (lattice.join firstUpper secondUpper) :=
  BoundedJoinSemilattice.join_le lawful
    (BoundedJoinSemilattice.le_trans lawful firstLe
      (BoundedJoinSemilattice.le_join_left lawful firstUpper secondUpper))
    (BoundedJoinSemilattice.le_trans lawful secondLe
      (BoundedJoinSemilattice.le_join_right lawful firstUpper secondUpper))

/-- **The product order is componentwise.**  A grade vector in the product lattice is below another IFF it is
below in EVERY component dimension.  The order-theoretic foundation of multi-dimensional grade subsumption: the
combined order is exactly the conjunction of the per-dimension orders, no cross-dimension coupling.  Forward by
`congrArg Prod.fst`/`Prod.snd` (the product `le` is a pair equality); backward by `pairEqOfComponents`. -/
theorem BoundedJoinSemilattice.productLe_iff (firstLattice secondLattice : BoundedJoinSemilattice)
    (firstPair secondPair : (firstLattice.product secondLattice).Carrier) :
    (firstLattice.product secondLattice).le firstPair secondPair ↔
      (firstLattice.le firstPair.1 secondPair.1 ∧ secondLattice.le firstPair.2 secondPair.2) :=
  ⟨fun productLe => ⟨congrArg Prod.fst productLe, congrArg Prod.snd productLe⟩,
   fun ⟨firstLe, secondLe⟩ => pairEqOfComponents firstLe secondLe⟩

/-- Concrete: the effect×trust grade-vector order decomposes componentwise. -/
theorem effectTrustProductLe_iff
    (firstPair secondPair : effectTrustProductLattice.Carrier) :
    effectTrustProductLattice.le firstPair secondPair ↔
      (effectLattice.le firstPair.1 secondPair.1 ∧ trustLattice.le firstPair.2 secondPair.2) :=
  BoundedJoinSemilattice.productLe_iff effectLattice trustLattice firstPair secondPair

/-- Concrete: the overflow×effect grade-vector order decomposes componentwise — with the NON-CHAIN overflow
diamond as a factor, demonstrating the decomposition is shape-agnostic (chain or antichain-bearing alike). -/
theorem overflowEffectProductLe_iff
    (firstPair secondPair : overflowEffectProductLattice.Carrier) :
    overflowEffectProductLattice.le firstPair secondPair ↔
      (overflowLattice.le firstPair.1 secondPair.1 ∧ effectLattice.le firstPair.2 secondPair.2) :=
  BoundedJoinSemilattice.productLe_iff overflowLattice effectLattice firstPair secondPair

/-- Concrete subsumption witness: `(pure, trusted) ≤ (impure, untrusted)` in the effect×trust grade vector,
because the subsumption holds in BOTH components. -/
theorem effectTrustVectorSubsumes :
    effectTrustProductLattice.le (EffectGrade.pureEffect, TrustGrade.trustedGrade)
      (EffectGrade.impureEffect, TrustGrade.untrustedGrade) :=
  (effectTrustProductLe_iff _ _).mpr ⟨effectLe_pure_impure, trustLe_trusted_untrusted⟩

end FX1Poly.Modal
