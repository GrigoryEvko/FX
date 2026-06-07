import FX1Poly.Modal.EffectLatticeClassification
import FX1Poly.Modal.ClockDomainLatticeDimension

/-! # FX1Poly/Modal/MutationChainLatticeDimension
    — the MUTATION dimension (§6.3 Dim 18) as the first proper TOTAL-ORDER chain, completing the
      lattice-shape spanning set

The lattice-graded engine (`EffectLatticeClassification.lean`) has so far carried three shapes:
TWO-ELEMENT chains (effect / trust / security — total orders, but trivially so), a FINITE ANTICHAIN
(overflow's diamond M3 — three pairwise-incomparable modes), and an INFINITE ANTICHAIN (clock's `sync`
elements).  The one shape still missing is a PROPER total order — a chain of more than two elements where
every pair is comparable.  This file supplies it: the MUTATION dimension (§6.3 Dim 18), whose distinct
content is exactly that it is the FIRST dimension with NO antichain.

## The mutation chain (§6.3 Dim 18)

§6.3 Dim 18 / §1.1: mutability is a four-level lattice `immutable < append_only < monotonic < read_write`,
default `immutable` (the deny-by-default bottom, §1.2):

  * `immutable` — the BOTTOM (the default: no mutation).
  * `appendOnly` — adds to the tail only.
  * `monotonic` — changes forward in a declared partial order.
  * `readWrite` — the TOP: any mutation.

These form a genuine CHAIN: `immutable <= appendOnly <= monotonic <= readWrite`, totally ordered.  The join
is the chain MAX (the more-permissive of two mutation grants).  Unlike overflow and clock, the induced order
has NO incomparable pair — `mutationIsTotalOrder` is the property that distinguishes a chain from an
antichain-bearing lattice.

## What lands here (all zero-axiom)

  * `MutationGrade` (4-ctor enum) + `MutationGrade.join` (the chain max, full 16-case enumeration).
  * `mutationLattice` + `mutationIsLawfulBoundedJoinSemilattice` — the chain is a verified bounded
    join-semilattice (laws by `cases <;> rfl`, like overflow — finite enum, no parameterization).
  * **`mutationIsTotalOrder`** — the genuinely NEW content: EVERY pair of mutation grades is comparable
    (`le a b ∨ le b a`).  This is the property NO antichain-bearing dimension (overflow's three-element
    antichain, clock's infinite one) has; mutation is the first dimension whose induced order is a proper
    (more-than-two-element) total order.
  * `mutationImmutableBelowAppendOnly` / `mutationAppendOnlyBelowMonotonic` /
    `mutationMonotonicBelowReadWrite` — the covering chain (each link of the order).
  * `mutationChainHasFourDistinct` — the four modes are pairwise distinct (a proper four-element chain, not
    a collapsed order).
  * `mutationImmutableIsLeast` / `mutationReadWriteIsGreatest` — `immutable` is the bottom (via the generic
    `bottom_le`) and `readWrite` the top of the induced order.
  * `mutationClockProductLattice` + `mutationClockProductIsLawful` — the proper CHAIN composes with the
    INFINITE ANTICHAIN (clock) via the shipped `productIsLawful`: the two structurally OPPOSITE lattice
    shapes (a total order and an infinite antichain) combine into one lawful lattice dimension with no
    per-product re-proof.

With this the lattice family spans all four shapes: trivial 2-chains, a proper total-order chain (mutation),
a finite antichain (overflow), and an infinite antichain (clock).

## Honest scope boundary

This adds the mutation lattice as the total-order member of the bounded-join-semilattice family and proves it
lawful + genuinely a proper total order + composable.  Like overflow / clock, it does NOT fold `mutation`
into the closed `GradedDimensionName` classification enum (a deferred, purely-additive cross-file edit); the
lawfulness + total-order theorems here ARE the classification evidence.  The full §6.3 mutation dimension also
carries the runtime mutation semantics (`ref mut` / `ref append`); only its COMBINE algebra — the chain — is
modeled here.  The §6.8 `monotonic × concurrent` soundness collision is NOT modeled (it needs a concurrency
dimension, not yet present).

## Zero-axiom verification

`MutationGrade` is a 4-element enum with derived `DecidableEq`; the lattice laws close by `cases <;> rfl`
(the associativity is a 64-leaf full enumeration); the covering-chain facts are `rfl`; the total order is
`cases <;> cases <;> first | exact Or.inl rfl | exact Or.inr rfl` (each pair's join is one endpoint, so one
disjunct is `rfl`); distinctness is `MutationGrade.noConfusion`; composition reuses the shipped
`productIsLawful`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The mutation grade (§6.3 Dim 18): a four-level chain `immutable` (the bottom — the default, no mutation),
`appendOnly` (tail append), `monotonic` (forward change in a declared order), `readWrite` (the top — any
mutation). -/
inductive MutationGrade where
  | immutable
  | appendOnly
  | monotonic
  | readWrite
  deriving DecidableEq

/-- Mutation join — the chain MAX (the more-permissive of two mutation grants).  Full 16-case enumeration of
the total order `immutable < appendOnly < monotonic < readWrite`. -/
def MutationGrade.join : MutationGrade → MutationGrade → MutationGrade
  | .immutable,  .immutable  => .immutable
  | .immutable,  .appendOnly => .appendOnly
  | .immutable,  .monotonic  => .monotonic
  | .immutable,  .readWrite  => .readWrite
  | .appendOnly, .immutable  => .appendOnly
  | .appendOnly, .appendOnly => .appendOnly
  | .appendOnly, .monotonic  => .monotonic
  | .appendOnly, .readWrite  => .readWrite
  | .monotonic,  .immutable  => .monotonic
  | .monotonic,  .appendOnly => .monotonic
  | .monotonic,  .monotonic  => .monotonic
  | .monotonic,  .readWrite  => .readWrite
  | .readWrite,  .immutable  => .readWrite
  | .readWrite,  .appendOnly => .readWrite
  | .readWrite,  .monotonic  => .readWrite
  | .readWrite,  .readWrite  => .readWrite

/-- The mutation bounded join-semilattice (a four-element chain): carrier `MutationGrade`, bottom
`immutable`, the chain-max join. -/
def mutationLattice : BoundedJoinSemilattice where
  Carrier := MutationGrade
  bottom := .immutable
  join := MutationGrade.join
  carrierDecEq := instDecidableEqMutationGrade

/-- **Mutation IS a verified bounded join-semilattice** — commutative, associative, idempotent chain-max
join with the `immutable` bottom.  The laws close by the same `cases <;> rfl` as the finite-enum overflow
(the 64-leaf associativity is a full enumeration). -/
theorem mutationIsLawfulBoundedJoinSemilattice : IsLawfulBoundedJoinSemilattice mutationLattice where
  join_comm := fun firstGrade secondGrade => by cases firstGrade <;> cases secondGrade <;> rfl
  join_assoc := fun firstGrade secondGrade thirdGrade => by
    cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl
  join_idempotent := fun someGrade => by cases someGrade <;> rfl
  bottom_join := fun someGrade => by cases someGrade <;> rfl
  join_bottom := fun someGrade => by cases someGrade <;> rfl

/-! ## The total order — the genuinely new content

Mutation is the first dimension whose induced order is a PROPER total order: every pair of grades is
comparable.  This is exactly the property an antichain-bearing dimension (overflow / clock) cannot have. -/

/-- **The mutation order is TOTAL.**  Every pair of mutation grades is comparable — there is NO incomparable
pair, the structural opposite of overflow's and clock's antichains.  For each pair the join is one of the two
endpoints, so one of the two `le` disjuncts is `rfl`. -/
theorem mutationIsTotalOrder (firstGrade secondGrade : MutationGrade) :
    mutationLattice.le firstGrade secondGrade ∨ mutationLattice.le secondGrade firstGrade := by
  cases firstGrade <;> cases secondGrade <;> first | exact Or.inl rfl | exact Or.inr rfl

/-! ## The covering chain -/

/-- `immutable <= appendOnly` (the first link of the chain). -/
theorem mutationImmutableBelowAppendOnly :
    mutationLattice.le MutationGrade.immutable MutationGrade.appendOnly := rfl

/-- `appendOnly <= monotonic` (the second link). -/
theorem mutationAppendOnlyBelowMonotonic :
    mutationLattice.le MutationGrade.appendOnly MutationGrade.monotonic := rfl

/-- `monotonic <= readWrite` (the third link). -/
theorem mutationMonotonicBelowReadWrite :
    mutationLattice.le MutationGrade.monotonic MutationGrade.readWrite := rfl

/-- The four modes are pairwise distinct — a proper four-element chain, not a collapsed order. -/
theorem mutationChainHasFourDistinct :
    MutationGrade.immutable ≠ MutationGrade.appendOnly ∧
    MutationGrade.appendOnly ≠ MutationGrade.monotonic ∧
    MutationGrade.monotonic ≠ MutationGrade.readWrite :=
  ⟨fun mutationEq => MutationGrade.noConfusion mutationEq,
   fun mutationEq => MutationGrade.noConfusion mutationEq,
   fun mutationEq => MutationGrade.noConfusion mutationEq⟩

/-! ## Bounds — immutable is the bottom, readWrite the top -/

/-- `immutable` is the least element (via the generic `bottom_le`) — the deny-by-default §1.2 bottom. -/
theorem mutationImmutableIsLeast (grade : MutationGrade) :
    mutationLattice.le MutationGrade.immutable grade :=
  BoundedJoinSemilattice.bottom_le mutationIsLawfulBoundedJoinSemilattice grade

/-- `readWrite` is the greatest element: every grade is below it. -/
theorem mutationReadWriteIsGreatest (grade : MutationGrade) :
    mutationLattice.le grade MutationGrade.readWrite := by cases grade <;> rfl

/-! ## Cross-family composition — the proper chain composes with the infinite antichain -/

/-- The `mutation × clock` composite lattice — a proper total-order CHAIN composed with an INFINITE
ANTICHAIN, the two structurally opposite lattice shapes. -/
def mutationClockProductLattice : BoundedJoinSemilattice :=
  mutationLattice.product clockLattice

/-- **Mutation × clock IS a lawful bounded join-semilattice** — the proper total-order chain and the
infinite-antichain clock dimension compose into one lawful lattice dimension via the shipped `productIsLawful`,
with NO per-product re-proof.  The strongest evidence yet that the §6.8 lattice-family composition is
shape-agnostic: it combines the two OPPOSITE order shapes — a total order and an infinite antichain — without
caring which is which. -/
theorem mutationClockProductIsLawful :
    IsLawfulBoundedJoinSemilattice mutationClockProductLattice :=
  BoundedJoinSemilattice.productIsLawful mutationIsLawfulBoundedJoinSemilattice
    clockIsLawfulBoundedJoinSemilattice

end FX1Poly.Modal
