import FX1Poly.Modal.OverflowLatticeDimension

/-! # FX1Poly/Modal/BoundedJoinSemilatticeUniversal
    — the join-semilattice UNIVERSAL PROPERTY (least-upper-bound) + decidable order, generic over every
      lattice-family dimension

`EffectLatticeClassification.lean` shipped the DIM-CLASS lattice engine: `BoundedJoinSemilattice` +
`IsLawfulBoundedJoinSemilattice` (the comm / assoc / idempotent / bottom-identity monoid laws) + the induced
order `le` (`lower ≤ upper ⟺ join lower upper = upper`) with its partial-order laws (`le_refl` / `le_trans` /
`le_antisymm` / `bottom_le`).  But those laws make the structure only a COMMUTATIVE IDEMPOTENT MONOID WITH A
COMPATIBLE ORDER — they do not yet record what makes `join` a genuine LATTICE operation: that `join a b` is the
LEAST UPPER BOUND of `a` and `b`.  This file proves that universal property, generically.

## The least-upper-bound characterization (the genuine lattice content)

  * `le_join_left` / `le_join_right` — `join a b` is an UPPER BOUND: `a ≤ join a b` and `b ≤ join a b` (by
    assoc + idempotence).
  * `join_le` — `join a b` is the LEAST upper bound: any common upper bound `c` (`a ≤ c`, `b ≤ c`) dominates it
    (`join a b ≤ c`, by assoc).
  * `join_isLeastUpperBound` — the three bundled into the single universal property (`join a b` is the lub of
    `{a, b}`).  This is the defining lattice-theoretic fact, holding for EVERY lattice-family dimension (effect /
    trust / security / overflow / any future one) with no per-dimension proof.

## Decidable order

  * `decidableLe` — the induced order is DECIDABLE, straight from the carrier's `DecidableEq` (`le lower upper`
    is by definition the equality `join lower upper = upper`).  So every lattice dimension's order is decidable;
    grade-checking against a lattice bound is a decision procedure, not an oracle.

## The concrete diamond payoff — "mixing overflow modes is a type error", precisely

  * `overflowConflictIsLeastUpperBoundOfWrapTrap` — in the overflow diamond, `conflictGrade` is the LEAST upper
    bound of `wrap` and `trap` (their `join`, via `join_le`).
  * `overflowOnlyConflictBoundsWrapTrap` — THE diamond consequence: the ONLY common upper bound of two distinct
    overflow modes is the conflict TOP (`le_antisymm` of "conflict is greatest" and "conflict is least upper
    bound").  This is the exact formalization of §6.3's "the other three are incomparable — mixing is a type
    error": any grade context that bounds two distinct fixed-width modes IS the rejected conflict state.  It
    complements firing-21's antichain (`wrap`/`trap`/`saturate` pairwise incomparable) with the dual fact that
    their joins escape immediately to the top.

## Zero-axiom verification

The universal-property lemmas are `calc` chains over the shipped join laws (`join_assoc` / `join_idempotent` /
`join_comm`); `decidableLe` is the carrier `DecidableEq` at the defeq-unfolded `le`; the concrete overflow
results compose `join_le` (with the `overflowJoin_wrap_trap` rewrite via `▸`) and the shipped `le_antisymm` /
`overflowConflictIsGreatest`.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **`join a b` is an upper bound of the left operand** — `a ≤ join a b`.  By associativity then idempotence:
`join a (join a b) = join (join a a) b = join a b`. -/
theorem BoundedJoinSemilattice.le_join_left {lattice : BoundedJoinSemilattice}
    (lawful : IsLawfulBoundedJoinSemilattice lattice) (firstGrade secondGrade : lattice.Carrier) :
    lattice.le firstGrade (lattice.join firstGrade secondGrade) :=
  calc lattice.join firstGrade (lattice.join firstGrade secondGrade)
      = lattice.join (lattice.join firstGrade firstGrade) secondGrade :=
        (lawful.join_assoc firstGrade firstGrade secondGrade).symm
    _ = lattice.join firstGrade secondGrade := by rw [lawful.join_idempotent]

/-- **`join a b` is an upper bound of the right operand** — `b ≤ join a b`.  By commutativity, associativity, and
idempotence. -/
theorem BoundedJoinSemilattice.le_join_right {lattice : BoundedJoinSemilattice}
    (lawful : IsLawfulBoundedJoinSemilattice lattice) (firstGrade secondGrade : lattice.Carrier) :
    lattice.le secondGrade (lattice.join firstGrade secondGrade) :=
  calc lattice.join secondGrade (lattice.join firstGrade secondGrade)
      = lattice.join secondGrade (lattice.join secondGrade firstGrade) := by
        rw [lawful.join_comm firstGrade secondGrade]
    _ = lattice.join (lattice.join secondGrade secondGrade) firstGrade :=
        (lawful.join_assoc secondGrade secondGrade firstGrade).symm
    _ = lattice.join secondGrade firstGrade := by rw [lawful.join_idempotent]
    _ = lattice.join firstGrade secondGrade := lawful.join_comm secondGrade firstGrade

/-- **`join a b` is the LEAST upper bound** — any common upper bound `c` (`a ≤ c` and `b ≤ c`) dominates `join a
b`.  By associativity: `join (join a b) c = join a (join b c) = join a c = c`. -/
theorem BoundedJoinSemilattice.join_le {lattice : BoundedJoinSemilattice}
    (lawful : IsLawfulBoundedJoinSemilattice lattice)
    {firstGrade secondGrade upperBound : lattice.Carrier}
    (firstLeUpper : lattice.le firstGrade upperBound) (secondLeUpper : lattice.le secondGrade upperBound) :
    lattice.le (lattice.join firstGrade secondGrade) upperBound :=
  calc lattice.join (lattice.join firstGrade secondGrade) upperBound
      = lattice.join firstGrade (lattice.join secondGrade upperBound) :=
        lawful.join_assoc firstGrade secondGrade upperBound
    _ = lattice.join firstGrade upperBound := by rw [secondLeUpper]
    _ = upperBound := firstLeUpper

/-- **The join-semilattice universal property.**  `join a b` is the LEAST UPPER BOUND of `{a, b}`: it is an upper
bound of both, and it is dominated by every common upper bound.  This is the defining lattice-theoretic content
(beyond the idempotent-commutative-monoid laws), holding for every lattice-family dimension with no per-dimension
proof. -/
theorem BoundedJoinSemilattice.join_isLeastUpperBound {lattice : BoundedJoinSemilattice}
    (lawful : IsLawfulBoundedJoinSemilattice lattice) (firstGrade secondGrade : lattice.Carrier) :
    lattice.le firstGrade (lattice.join firstGrade secondGrade) ∧
    lattice.le secondGrade (lattice.join firstGrade secondGrade) ∧
    ∀ upperBound : lattice.Carrier,
      lattice.le firstGrade upperBound → lattice.le secondGrade upperBound →
        lattice.le (lattice.join firstGrade secondGrade) upperBound :=
  ⟨BoundedJoinSemilattice.le_join_left lawful firstGrade secondGrade,
   BoundedJoinSemilattice.le_join_right lawful firstGrade secondGrade,
   fun _upperBound firstLeUpper secondLeUpper =>
     BoundedJoinSemilattice.join_le lawful firstLeUpper secondLeUpper⟩

/-- **The induced order is decidable.**  `le lower upper` is by definition the equality `join lower upper =
upper`, decided by the carrier's `DecidableEq`.  So grade-checking against any lattice-dimension bound is a
decision procedure. -/
def BoundedJoinSemilattice.decidableLe (lattice : BoundedJoinSemilattice)
    (lower upper : lattice.Carrier) : Decidable (lattice.le lower upper) :=
  lattice.carrierDecEq (lattice.join lower upper) upper

/-- **Concrete: `conflictGrade` is the LEAST upper bound of `wrap` and `trap`** in the overflow diamond — their
`join` (via `join_le` + the `overflowJoin_wrap_trap` rewrite). -/
theorem overflowConflictIsLeastUpperBoundOfWrapTrap (upperBound : OverflowGrade)
    (wrapLe : overflowLattice.le OverflowGrade.wrapGrade upperBound)
    (trapLe : overflowLattice.le OverflowGrade.trapGrade upperBound) :
    overflowLattice.le OverflowGrade.conflictGrade upperBound :=
  overflowJoin_wrap_trap ▸ BoundedJoinSemilattice.join_le overflowIsLawfulBoundedJoinSemilattice wrapLe trapLe

/-- **THE diamond consequence — the ONLY common upper bound of two distinct overflow modes is the conflict top.**
Any grade `upperBound` that bounds both `wrap` and `trap` IS `conflictGrade` (`le_antisymm` of "conflict is
greatest" and "conflict is the least upper bound").  This is the precise formalization of §6.3's "mixing overflow
modes is a type error": a context bounding two distinct fixed-width modes is the rejected conflict state. -/
theorem overflowOnlyConflictBoundsWrapTrap (upperBound : OverflowGrade)
    (wrapLe : overflowLattice.le OverflowGrade.wrapGrade upperBound)
    (trapLe : overflowLattice.le OverflowGrade.trapGrade upperBound) :
    upperBound = OverflowGrade.conflictGrade :=
  BoundedJoinSemilattice.le_antisymm overflowIsLawfulBoundedJoinSemilattice
    (overflowConflictIsGreatest upperBound)
    (overflowConflictIsLeastUpperBoundOfWrapTrap upperBound wrapLe trapLe)

end FX1Poly.Modal
