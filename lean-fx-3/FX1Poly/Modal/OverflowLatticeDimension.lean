import FX1Poly.Modal.EffectLatticeClassification

/-! # FX1Poly/Modal/OverflowLatticeDimension
    — the OVERFLOW dimension (§6.3 Dim 16) as the FIRST NON-CHAIN bounded join-semilattice (diamond M3)

`EffectLatticeClassification.lean` shipped the lattice-graded engine for the §6.8 effect-family dimensions —
`BoundedJoinSemilattice` + `IsLawfulBoundedJoinSemilattice` + the pointwise product (`productIsLawful`) + the
induced partial order (`le` / `le_refl` / `le_trans` / `le_antisymm` / `bottom_le`).  But every instance it
carries — effect `{pure < impure}`, trust `{trusted < untrusted}` (and security) — is a TWO-ELEMENT CHAIN, where
every pair is comparable.  This file exercises the engine on a genuinely NEW lattice shape: the OVERFLOW
dimension (§6.3 Dim 16: `{exact, wrap, trap, saturate}`), the first NON-CHAIN instance.

## The diamond M3 lattice

§3.1 / §6.3: arithmetic overflow is `exact` (arbitrary-precision, the default — the BOTTOM) by default; the
three FIXED-width modes `wrap` / `trap` / `saturate` are INCOMPARABLE ("Other three incomparable — mixing is a
type error unless coerced", §6.3 Dim 16).  We model this as the diamond M3 bounded join-semilattice:

  * `exactGrade` — the bottom (arbitrary precision absorbs into any mode).
  * `wrapGrade` / `trapGrade` / `saturateGrade` — a three-element ANTICHAIN (pairwise incomparable).
  * `conflictGrade` — the TOP, the join of any two distinct modes: it is the algebraic realization of the spec's
    "mixing overflow modes is a type error".  A grade of `conflictGrade` is the rejected state; the type system
    refuses it (just as the §6.4 permission PCM lifts an over-allocation to an explicit `CONFLICT` top).

`join` is the lattice supremum: `exact` is the identity, two equal modes join to themselves, two DISTINCT modes
join to `conflict`, and `conflict` absorbs.  This is M3, the canonical non-distributive lattice — and crucially a
genuine NON-CHAIN, so it is the first instance whose induced order has incomparable elements.

## What lands here (all zero-axiom)

  * `OverflowGrade` (5-ctor enum) + `OverflowGrade.join` (full 25-case enumeration, propext-free).
  * `overflowLattice` + `overflowIsLawfulBoundedJoinSemilattice` — the diamond is a verified bounded
    join-semilattice (the laws close by `cases <;> rfl`, including the 125-leaf associativity).
  * `overflowJoin_wrap_trap` / `_wrap_saturate` / `_trap_saturate` — the conflict-mixing semantics: any two
    distinct modes join to `conflictGrade` (the §6.3 "mixing is a type error", as a `rfl`).
  * **`overflowWrapTrapIncomparable` / `_wrapSaturate_` / `_trapSaturate_`** — the genuinely NEW content: the
    three modes are PAIRWISE INCOMPARABLE in the induced order (`¬ le a b ∧ ¬ le b a`).  No chain lattice
    (effect / trust / security) has an incomparable pair; this is the first instance that exercises the engine's
    antisymmetric order on a real antichain.
  * `overflowConflictIsGreatest` / `overflowExactIsLeast` — `conflict` is the top and `exact` the bottom of the
    induced order (the latter via the generic `bottom_le`).
  * `overflowEffectProductLattice` + `overflowEffectProductIsLawful` — the non-chain overflow dimension composes
    with the chain effect dimension via the shipped `productIsLawful`, with NO per-product re-proof: a non-chain
    and a chain lattice dimension combine into one lawful lattice dimension, exactly as the §6.8 thesis predicts.

## Honest scope boundary

This adds the overflow lattice as a structurally-new (non-chain) member of the bounded-join-semilattice family
and proves it lawful + genuinely non-chain (the antichain) + composable.  It does NOT fold `overflow` into the
closed `GradedDimensionName` classification enum in `EffectLatticeClassification.lean` — that is a deferred,
purely-additive cross-file edit (new ctor + new `gradeAlgebraOf` arm + ledger theorem); the lawfulness +
incomparability theorems here ARE the classification evidence (overflow ∈ the bounded-semilattice family, and
it is that family's first non-chain member).  The full §6.3 overflow grade also carries the runtime-mode
semantics (wrap-around arithmetic, trap-on-overflow); only its COMBINE algebra — the lattice — is modeled here.

## Zero-axiom verification

`OverflowGrade` is a 5-element enum with derived `DecidableEq`; the lattice laws close by `cases <;> rfl`; the
conflict-mixing facts are `rfl`; the antichain incomparability is the defeq route `fun overflowEq =>
OverflowGrade.noConfusion overflowEq` (the induced `le` reduces to a `conflictGrade = _` equality the
`noConfusion` refutes); composition reuses the shipped `productIsLawful`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The overflow grade (§6.3 Dim 16): `exactGrade` (arbitrary precision, the bottom), the three incomparable
fixed-width modes `wrapGrade` / `trapGrade` / `saturateGrade`, and `conflictGrade` (the top — the rejected
"mixing is a type error" state). -/
inductive OverflowGrade where
  | exactGrade
  | wrapGrade
  | trapGrade
  | saturateGrade
  | conflictGrade
  deriving DecidableEq

/-- Overflow join — the diamond M3 supremum.  `exact` is the identity; two equal modes join to themselves; any
two DISTINCT fixed-width modes join to `conflictGrade` (the §6.3 "mixing overflow modes is a type error");
`conflict` absorbs.  Full 25-case enumeration, propext-free. -/
def OverflowGrade.join : OverflowGrade → OverflowGrade → OverflowGrade
  | .exactGrade, .exactGrade => .exactGrade
  | .exactGrade, .wrapGrade => .wrapGrade
  | .exactGrade, .trapGrade => .trapGrade
  | .exactGrade, .saturateGrade => .saturateGrade
  | .exactGrade, .conflictGrade => .conflictGrade
  | .wrapGrade, .exactGrade => .wrapGrade
  | .wrapGrade, .wrapGrade => .wrapGrade
  | .wrapGrade, .trapGrade => .conflictGrade
  | .wrapGrade, .saturateGrade => .conflictGrade
  | .wrapGrade, .conflictGrade => .conflictGrade
  | .trapGrade, .exactGrade => .trapGrade
  | .trapGrade, .wrapGrade => .conflictGrade
  | .trapGrade, .trapGrade => .trapGrade
  | .trapGrade, .saturateGrade => .conflictGrade
  | .trapGrade, .conflictGrade => .conflictGrade
  | .saturateGrade, .exactGrade => .saturateGrade
  | .saturateGrade, .wrapGrade => .conflictGrade
  | .saturateGrade, .trapGrade => .conflictGrade
  | .saturateGrade, .saturateGrade => .saturateGrade
  | .saturateGrade, .conflictGrade => .conflictGrade
  | .conflictGrade, .exactGrade => .conflictGrade
  | .conflictGrade, .wrapGrade => .conflictGrade
  | .conflictGrade, .trapGrade => .conflictGrade
  | .conflictGrade, .saturateGrade => .conflictGrade
  | .conflictGrade, .conflictGrade => .conflictGrade

/-- The overflow bounded join-semilattice (diamond M3): carrier `OverflowGrade`, bottom `exactGrade`, the diamond
join. -/
def overflowLattice : BoundedJoinSemilattice where
  Carrier := OverflowGrade
  bottom := .exactGrade
  join := OverflowGrade.join
  carrierDecEq := instDecidableEqOverflowGrade

/-- **Overflow IS a verified bounded join-semilattice** — commutative, associative, idempotent diamond join with
the `exact` bottom.  Unlike effect / trust / security, this is a NON-CHAIN lattice; the laws nonetheless close by
the same `cases <;> rfl` (the associativity is a 125-leaf full enumeration). -/
theorem overflowIsLawfulBoundedJoinSemilattice : IsLawfulBoundedJoinSemilattice overflowLattice where
  join_comm := fun firstGrade secondGrade => by cases firstGrade <;> cases secondGrade <;> rfl
  join_assoc := fun firstGrade secondGrade thirdGrade => by
    cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl
  join_idempotent := fun someGrade => by cases someGrade <;> rfl
  bottom_join := fun someGrade => by cases someGrade <;> rfl
  join_bottom := fun someGrade => by cases someGrade <;> rfl

/-! ## Conflict-mixing semantics — any two distinct modes join to the conflict top

The §6.3 "the other three are incomparable — mixing is a type error" rendered algebraically: the join of any two
distinct fixed-width modes is `conflictGrade`, the rejected state. -/

/-- Mixing `wrap` and `trap` yields the conflict top (§6.3 type-error semantics). -/
theorem overflowJoin_wrap_trap :
    overflowLattice.join OverflowGrade.wrapGrade OverflowGrade.trapGrade = OverflowGrade.conflictGrade := rfl

/-- Mixing `wrap` and `saturate` yields the conflict top. -/
theorem overflowJoin_wrap_saturate :
    overflowLattice.join OverflowGrade.wrapGrade OverflowGrade.saturateGrade = OverflowGrade.conflictGrade := rfl

/-- Mixing `trap` and `saturate` yields the conflict top. -/
theorem overflowJoin_trap_saturate :
    overflowLattice.join OverflowGrade.trapGrade OverflowGrade.saturateGrade = OverflowGrade.conflictGrade := rfl

/-! ## The antichain — the genuinely non-chain content

The three fixed-width modes are PAIRWISE INCOMPARABLE in the induced order.  This is the property NO chain lattice
(effect / trust / security) can have: it is the first time the engine's antisymmetric `le` is exercised on a real
antichain.  Each `¬ le a b` reduces (by the diamond join + `le := join a b = b`) to refuting `conflictGrade = b`. -/

/-- `wrap` and `trap` are incomparable. -/
theorem overflowWrapTrapIncomparable :
    ¬ overflowLattice.le OverflowGrade.wrapGrade OverflowGrade.trapGrade ∧
    ¬ overflowLattice.le OverflowGrade.trapGrade OverflowGrade.wrapGrade :=
  ⟨fun overflowEq => OverflowGrade.noConfusion overflowEq,
   fun overflowEq => OverflowGrade.noConfusion overflowEq⟩

/-- `wrap` and `saturate` are incomparable. -/
theorem overflowWrapSaturateIncomparable :
    ¬ overflowLattice.le OverflowGrade.wrapGrade OverflowGrade.saturateGrade ∧
    ¬ overflowLattice.le OverflowGrade.saturateGrade OverflowGrade.wrapGrade :=
  ⟨fun overflowEq => OverflowGrade.noConfusion overflowEq,
   fun overflowEq => OverflowGrade.noConfusion overflowEq⟩

/-- `trap` and `saturate` are incomparable. -/
theorem overflowTrapSaturateIncomparable :
    ¬ overflowLattice.le OverflowGrade.trapGrade OverflowGrade.saturateGrade ∧
    ¬ overflowLattice.le OverflowGrade.saturateGrade OverflowGrade.trapGrade :=
  ⟨fun overflowEq => OverflowGrade.noConfusion overflowEq,
   fun overflowEq => OverflowGrade.noConfusion overflowEq⟩

/-! ## Bounds — conflict is the top, exact is the bottom -/

/-- `conflictGrade` is the greatest element: every grade is below it. -/
theorem overflowConflictIsGreatest (grade : OverflowGrade) :
    overflowLattice.le grade OverflowGrade.conflictGrade := by
  cases grade <;> rfl

/-- `exactGrade` is the least element: it is below every grade (via the generic `bottom_le`). -/
theorem overflowExactIsLeast (grade : OverflowGrade) :
    overflowLattice.le OverflowGrade.exactGrade grade :=
  BoundedJoinSemilattice.bottom_le overflowIsLawfulBoundedJoinSemilattice grade

/-! ## Cross-family composition — the non-chain dimension composes with a chain dimension -/

/-- The `overflow × effect` composite lattice — a NON-CHAIN dimension composed with a CHAIN dimension. -/
def overflowEffectProductLattice : BoundedJoinSemilattice :=
  overflowLattice.product effectLattice

/-- **Overflow × effect IS a lawful bounded join-semilattice** — the non-chain overflow dimension and the chain
effect dimension compose into one lawful lattice dimension via the shipped `productIsLawful`, with NO per-product
re-proof.  Concrete evidence that the §6.8 lattice-family composition is shape-agnostic: it does not care whether
a factor is a chain or a genuine antichain-bearing diamond. -/
theorem overflowEffectProductIsLawful :
    IsLawfulBoundedJoinSemilattice overflowEffectProductLattice :=
  BoundedJoinSemilattice.productIsLawful overflowIsLawfulBoundedJoinSemilattice
    effectIsLawfulBoundedJoinSemilattice

end FX1Poly.Modal
