import FX1Poly.Modal.MutationChainLatticeDimension
import FX1Poly.Modal.OverflowLatticeDimension

/-! # FX1Poly/Modal/LatticeDistributivityClassification
    — the chain-vs-diamond DISTRIBUTIVITY dichotomy: FX's lattice dimensions are distributive iff they
      are chains; the diamond M3 is the lone non-distributive one

Firings building the lattice family established its shapes: trivial 2-chains (effect / trust / security), a
proper total-order 4-chain (mutation, `MutationChainLatticeDimension.lean`), a finite antichain (the overflow
diamond M3, `OverflowLatticeDimension.lean`), and an infinite antichain (clock).  The overflow file then
completed M3 to a FULL bounded lattice (meet + absorption) and proved it NON-DISTRIBUTIVE and MODULAR.  This
file is the structural CAPSTONE: it classifies the lattice dimensions by distributivity, the deepest
lattice-theoretic invariant, and pins down exactly which dimension is the non-distributive one.

## The dichotomy

A lattice is DISTRIBUTIVE when `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)`.  In lattice theory the distributive lattices
are exactly those with NO M3 (diamond) and NO N5 (pentagon) sublattice; in particular every CHAIN (total order,
with `∧ = min`, `∨ = max`) is distributive, and the diamond M3 is the smallest NON-distributive lattice.  FX's
lattice dimensions split cleanly along this line:

  * **The chains are distributive.**  `mutationIsDistributive` proves the mutation 4-chain
    `immutable < appendOnly < monotonic < readWrite` satisfies the distributive law — a genuinely non-trivial
    chain (not a two-element triviality).  The trivial 2-chains (effect / trust / security) are distributive a
    fortiori; security's distributivity is in fact already shipped as `SecurityGrade.left_distrib` (security's
    `mul` is the meet, `add` the join, so that semiring law IS the lattice distributive law of the security
    chain).
  * **The diamond M3 is NOT distributive.**  `overflowIsNonDistributive` (overflow file) exhibits the canonical
    failure on the three incomparable modes `wrap / trap / saturate`.

`mutationChainDistributesButOverflowDiamondDoesNot` bundles the two into the headline classification: combining
mutation grants distributes over the chain, but combining overflow modes does NOT distribute over the diamond —
the §6.3 fact that overflow's three fixed-width modes are pairwise INCOMPARABLE is exactly what makes its
lattice non-distributive, while mutation's total order is exactly what makes its lattice distributive.  So the
21-dimension grade vector is heterogeneous at the deepest lattice-theoretic level too (§6.8): even among the
dimensions that ARE bounded lattices, they are not all the same KIND of lattice.

## What lands here (all zero-axiom)

  * `MutationGrade.meet` (the chain MIN, dual to the shipped chain-max join) + its meet-semilattice laws
    (`mutationMeet_comm` / `_assoc` / `_idempotent`) + the two absorption laws (`mutationJoinMeetAbsorb` /
    `mutationMeetJoinAbsorb`) — establishing the mutation chain is a genuine bounded LATTICE (the meet-side
    mirror of the shipped join-semilattice).
  * `mutationIsDistributive` — the 4-chain satisfies `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)` (64-leaf `cases <;>
    rfl`).
  * `mutationChainDistributesButOverflowDiamondDoesNot` — the dichotomy: mutation distributive ∧ overflow
    non-distributive (citing the shipped `overflowIsNonDistributive`).

## Zero-axiom verification

`MutationGrade.meet` is the chain min on the 4-element enum; every law closes by `cases <;> rfl` (the
distributive law is a 64-leaf full enumeration), and the dichotomy is the pair of `mutationIsDistributive` with
the shipped `overflowIsNonDistributive`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Mutation MEET — the chain MIN (the LESS-permissive of two mutation grants), the dual of the shipped
chain-max `MutationGrade.join`.  Full 16-case enumeration of the total order
`immutable < appendOnly < monotonic < readWrite`. -/
def MutationGrade.meet : MutationGrade → MutationGrade → MutationGrade
  | .immutable,  _           => .immutable
  | .appendOnly, .immutable  => .immutable
  | .appendOnly, .appendOnly => .appendOnly
  | .appendOnly, .monotonic  => .appendOnly
  | .appendOnly, .readWrite  => .appendOnly
  | .monotonic,  .immutable  => .immutable
  | .monotonic,  .appendOnly => .appendOnly
  | .monotonic,  .monotonic  => .monotonic
  | .monotonic,  .readWrite  => .monotonic
  | .readWrite,  .immutable  => .immutable
  | .readWrite,  .appendOnly => .appendOnly
  | .readWrite,  .monotonic  => .monotonic
  | .readWrite,  .readWrite  => .readWrite

/-- Mutation meet is commutative (the meet-semilattice mirror of the shipped `join_comm`). -/
theorem mutationMeet_comm (firstGrade secondGrade : MutationGrade) :
    MutationGrade.meet firstGrade secondGrade = MutationGrade.meet secondGrade firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- Mutation meet is associative (64-leaf full enumeration). -/
theorem mutationMeet_assoc (firstGrade secondGrade thirdGrade : MutationGrade) :
    MutationGrade.meet (MutationGrade.meet firstGrade secondGrade) thirdGrade =
      MutationGrade.meet firstGrade (MutationGrade.meet secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- Mutation meet is idempotent. -/
theorem mutationMeet_idempotent (grade : MutationGrade) : MutationGrade.meet grade grade = grade := by
  cases grade <;> rfl

/-- **Absorption (join over meet): `a ∨ (a ∧ b) = a`.**  With the meet-semilattice laws and the shipped
join-semilattice, this makes the mutation chain a genuine bounded LATTICE. -/
theorem mutationJoinMeetAbsorb (firstGrade secondGrade : MutationGrade) :
    MutationGrade.join firstGrade (MutationGrade.meet firstGrade secondGrade) = firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- **Absorption (meet over join): `a ∧ (a ∨ b) = a`.**  The second lattice-absorption law. -/
theorem mutationMeetJoinAbsorb (firstGrade secondGrade : MutationGrade) :
    MutationGrade.meet firstGrade (MutationGrade.join firstGrade secondGrade) = firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- ★ **The mutation 4-chain is a DISTRIBUTIVE lattice** — `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)`.  Every chain
(total order) is distributive: `min` distributes over `max`.  A genuinely non-trivial demonstration on a
four-element chain, not a two-element triviality. -/
theorem mutationIsDistributive (firstGrade secondGrade thirdGrade : MutationGrade) :
    MutationGrade.meet firstGrade (MutationGrade.join secondGrade thirdGrade) =
      MutationGrade.join (MutationGrade.meet firstGrade secondGrade)
        (MutationGrade.meet firstGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- ★ **The chain-vs-diamond distributivity dichotomy.**  The mutation total-order chain DISTRIBUTES
(`mutationIsDistributive`) but the overflow diamond M3 does NOT (`overflowIsNonDistributive`, overflow file).
Among FX's bounded-lattice dimensions, distributivity tracks the order shape exactly: chains are distributive,
the antichain-bearing diamond is not.  So the §6.8 heterogeneity reaches the deepest lattice-theoretic
invariant — even the lattice dimensions are not all the same kind of lattice. -/
theorem mutationChainDistributesButOverflowDiamondDoesNot :
    (∀ firstGrade secondGrade thirdGrade : MutationGrade,
      MutationGrade.meet firstGrade (MutationGrade.join secondGrade thirdGrade) =
        MutationGrade.join (MutationGrade.meet firstGrade secondGrade)
          (MutationGrade.meet firstGrade thirdGrade)) ∧
    (∃ firstGrade secondGrade thirdGrade : OverflowGrade,
      OverflowGrade.meet firstGrade (OverflowGrade.join secondGrade thirdGrade) ≠
        OverflowGrade.join (OverflowGrade.meet firstGrade secondGrade)
          (OverflowGrade.meet firstGrade thirdGrade)) :=
  ⟨mutationIsDistributive, overflowIsNonDistributive⟩

end FX1Poly.Modal
