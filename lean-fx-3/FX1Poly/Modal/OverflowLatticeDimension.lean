import FX1Poly.Modal.EffectLatticeClassification

/-! # FX1Poly/Modal/OverflowLatticeDimension
    — the OVERFLOW dimension (§6.3 Dim 16) as the FIRST NON-CHAIN bounded join-semilattice, and (bottom of
      file) the kernel's FIRST FULL bounded LATTICE: the diamond M3, modular but non-distributive

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

/-! ## The MEET — completing the diamond to the kernel's FIRST FULL bounded lattice (M3: modular, non-distributive)

Everything above makes overflow a bounded JOIN-semilattice (the join half only).  But the diamond M3 is a full
LATTICE: it also has MEETS (infima).  This section adds `OverflowGrade.meet` — the diamond infimum, dual to
`join` under the bottom↔top swap: `conflictGrade` (the top) is the meet IDENTITY, two equal modes meet to
themselves, two DISTINCT fixed-width modes meet DOWN to the `exactGrade` bottom, and `exactGrade` ABSORBS — and
the two **absorption laws** `a ∨ (a ∧ b) = a` / `a ∧ (a ∨ b) = a`.  Absorption is exactly what upgrades "two
unrelated semilattices" into a genuine bounded LATTICE; this is the kernel's FIRST full lattice (every prior
lattice dimension — effect/trust/security/overflow-join/clock/mutation — built only the join half).

Because M3 is the textbook diamond, it is also the kernel's FIRST non-distributive AND first modular lattice:

  * `overflowIsNonDistributive` — the canonical M3 distribution failure: `wrap ∧ (trap ∨ saturate) = wrap ∧
    conflict = wrap`, but `(wrap ∧ trap) ∨ (wrap ∧ saturate) = exact ∨ exact = exact`, and `wrap ≠ exact`.
    Distribution FAILS — overflow is genuinely richer than the distributive CHAINS (effect/trust/security/
    mutation are chains, hence automatically distributive).  This is the algebraic face of §6.3's "the three
    modes are incomparable": three pairwise-incomparable atoms with a common top and bottom is precisely M3,
    and M3 is the smallest non-distributive lattice.
  * `overflowIsModular` — yet M3 satisfies the MODULAR law `a ≤ c → a ∨ (b ∧ c) = (a ∨ b) ∧ c`.  This pins
    overflow down precisely as M3 (the diamond), NOT N5 (the pentagon, the canonical NON-modular lattice):
    the diamond is modular-but-not-distributive, the pentagon is neither.  The `a ≤ c` guard is essential —
    drop it and the equation fails (e.g. `a = trap`, `c = wrap`, `b = saturate`), which is exactly why
    modularity is strictly weaker than distributivity.

`meet` mirrors `join` dualized, so the meet-semilattice laws close by the same `cases <;> rfl` (the
associativity is the 125-leaf full enumeration); absorption is a 25-case `cases <;> rfl`; non-distributivity is
a concrete `decide` witness (`wrap ≠ exact` after both sides compute); modularity is `cases … <;> first | rfl |
exact OverflowGrade.noConfusion hac` — the impossible `le a c` cases are refuted by `noConfusion` (the induced
`le` reduces to a false `conflictGrade = _`-style equality), the genuine `a ≤ c` cases close by `rfl`.  All
zero-axiom; per-declaration gated in `FX1PolyAudit/AuditModal.lean`. -/

/-- Overflow MEET — the diamond M3 infimum, dual to `OverflowGrade.join` under the bottom↔top swap.
`conflictGrade` (top) is the identity; two equal modes meet to themselves; any two DISTINCT fixed-width modes
meet to `exactGrade` (the bottom — losing all mode information); `exactGrade` absorbs.  Full 25-case
enumeration, propext-free. -/
def OverflowGrade.meet : OverflowGrade → OverflowGrade → OverflowGrade
  | .exactGrade, _ => .exactGrade
  | .wrapGrade, .exactGrade => .exactGrade
  | .wrapGrade, .wrapGrade => .wrapGrade
  | .wrapGrade, .trapGrade => .exactGrade
  | .wrapGrade, .saturateGrade => .exactGrade
  | .wrapGrade, .conflictGrade => .wrapGrade
  | .trapGrade, .exactGrade => .exactGrade
  | .trapGrade, .wrapGrade => .exactGrade
  | .trapGrade, .trapGrade => .trapGrade
  | .trapGrade, .saturateGrade => .exactGrade
  | .trapGrade, .conflictGrade => .trapGrade
  | .saturateGrade, .exactGrade => .exactGrade
  | .saturateGrade, .wrapGrade => .exactGrade
  | .saturateGrade, .trapGrade => .exactGrade
  | .saturateGrade, .saturateGrade => .saturateGrade
  | .saturateGrade, .conflictGrade => .saturateGrade
  | .conflictGrade, .exactGrade => .exactGrade
  | .conflictGrade, .wrapGrade => .wrapGrade
  | .conflictGrade, .trapGrade => .trapGrade
  | .conflictGrade, .saturateGrade => .saturateGrade
  | .conflictGrade, .conflictGrade => .conflictGrade

/-- Meet is commutative (the meet-semilattice mirror of `join_comm`). -/
theorem overflowMeet_comm (firstGrade secondGrade : OverflowGrade) :
    OverflowGrade.meet firstGrade secondGrade = OverflowGrade.meet secondGrade firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- Meet is associative (125-leaf full enumeration, the mirror of `join_assoc`). -/
theorem overflowMeet_assoc (firstGrade secondGrade thirdGrade : OverflowGrade) :
    OverflowGrade.meet (OverflowGrade.meet firstGrade secondGrade) thirdGrade =
      OverflowGrade.meet firstGrade (OverflowGrade.meet secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- Meet is idempotent. -/
theorem overflowMeet_idempotent (grade : OverflowGrade) : OverflowGrade.meet grade grade = grade := by
  cases grade <;> rfl

/-- `conflictGrade` (the top) is the meet IDENTITY on the left — the dual of `exact` being the join identity. -/
theorem overflowTopMeet (grade : OverflowGrade) :
    OverflowGrade.meet OverflowGrade.conflictGrade grade = grade := by cases grade <;> rfl

/-- `conflictGrade` is the meet identity on the right. -/
theorem overflowMeetTop (grade : OverflowGrade) :
    OverflowGrade.meet grade OverflowGrade.conflictGrade = grade := by cases grade <;> rfl

/-- `exactGrade` (the bottom) ABSORBS under meet — the dual of `conflict` absorbing under join. -/
theorem overflowExactMeet (grade : OverflowGrade) :
    OverflowGrade.meet OverflowGrade.exactGrade grade = OverflowGrade.exactGrade := by cases grade <;> rfl

/-- **Absorption (join over meet): `a ∨ (a ∧ b) = a`.**  One of the two laws that make join + meet a genuine
bounded LATTICE rather than two unrelated semilattices. -/
theorem overflowJoinMeetAbsorb (firstGrade secondGrade : OverflowGrade) :
    OverflowGrade.join firstGrade (OverflowGrade.meet firstGrade secondGrade) = firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- **Absorption (meet over join): `a ∧ (a ∨ b) = a`.**  The second lattice-absorption law. -/
theorem overflowMeetJoinAbsorb (firstGrade secondGrade : OverflowGrade) :
    OverflowGrade.meet firstGrade (OverflowGrade.join firstGrade secondGrade) = firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-! ### Dual conflict-mixing — distinct modes MEET to the exact bottom (dual of join-to-conflict) -/

/-- `wrap ∧ trap = exact`: meeting distinct modes loses all mode information (dual of `overflowJoin_wrap_trap`). -/
theorem overflowMeet_wrap_trap :
    OverflowGrade.meet OverflowGrade.wrapGrade OverflowGrade.trapGrade = OverflowGrade.exactGrade := rfl

/-- `wrap ∧ saturate = exact`. -/
theorem overflowMeet_wrap_saturate :
    OverflowGrade.meet OverflowGrade.wrapGrade OverflowGrade.saturateGrade = OverflowGrade.exactGrade := rfl

/-- `trap ∧ saturate = exact`. -/
theorem overflowMeet_trap_saturate :
    OverflowGrade.meet OverflowGrade.trapGrade OverflowGrade.saturateGrade = OverflowGrade.exactGrade := rfl

/-- ★ **M3 is NON-DISTRIBUTIVE** — the canonical diamond witness `wrap / trap / saturate`:
`wrap ∧ (trap ∨ saturate) = wrap ∧ conflict = wrap` but `(wrap ∧ trap) ∨ (wrap ∧ saturate) = exact ∨ exact =
exact`, and `wrap ≠ exact`.  The overflow dimension is genuinely richer than the distributive chains. -/
theorem overflowIsNonDistributive :
    ∃ firstGrade secondGrade thirdGrade : OverflowGrade,
      OverflowGrade.meet firstGrade (OverflowGrade.join secondGrade thirdGrade) ≠
        OverflowGrade.join (OverflowGrade.meet firstGrade secondGrade)
          (OverflowGrade.meet firstGrade thirdGrade) :=
  ⟨OverflowGrade.wrapGrade, OverflowGrade.trapGrade, OverflowGrade.saturateGrade,
    fun equalityHyp => OverflowGrade.noConfusion equalityHyp⟩

/-- ★ **M3 IS MODULAR** — the modular law `a ≤ c → a ∨ (b ∧ c) = (a ∨ b) ∧ c` holds.  This pins overflow down
as M3 (the diamond, modular but not distributive), NOT N5 (the pentagon, the canonical non-modular lattice).
The `a ≤ c` guard is essential: its impossible cases are refuted by `noConfusion`, the genuine cases close by
`rfl`. -/
theorem overflowIsModular (firstGrade secondGrade thirdGrade : OverflowGrade)
    (firstBelowThird : overflowLattice.le firstGrade thirdGrade) :
    OverflowGrade.join firstGrade (OverflowGrade.meet secondGrade thirdGrade) =
      OverflowGrade.meet (OverflowGrade.join firstGrade secondGrade) thirdGrade := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;>
    first | rfl | exact OverflowGrade.noConfusion firstBelowThird

/-! ## The MEET universal property — `meet a b` is the GREATEST LOWER BOUND (the glb dual of the shipped lub)

`BoundedJoinSemilatticeUniversal.lean` proved the JOIN's universal property — `join a b` is the LEAST UPPER
BOUND — generically, and specialized it to the overflow diamond (`overflowConflictIsLeastUpperBoundOfWrapTrap`
/ `overflowOnlyConflictBoundsWrapTrap`: the unique common UPPER bound of two distinct modes is the conflict top).
This section proves the DUAL for the meet built above: `meet a b` is the GREATEST LOWER BOUND of `a` and `b`.
Together with the shipped lub, this completes M3's lattice characterization — it has BOTH universal properties,
and the antichain is bounded from both sides (conflict above, exact below).

The lub was proved generically (over the abstract join laws) because `BoundedJoinSemilattice` carries `join`;
the meet here is concrete to overflow, so the glb is proved by concrete enumeration (`cases <;> rfl` / the
`le`-guard `noConfusion` discharge) — lighter than the generic `calc`, since `OverflowGrade.le lowerBound x`
is defeq to the computable equality `join lowerBound x = x`.  All zero-axiom; gated in `AuditModal.lean`. -/

/-- **`meet a b` is a LOWER bound of the left operand** — `meet a b ≤ a` (the dual of `le_join_left`). -/
theorem overflowMeetLeLeft (firstGrade secondGrade : OverflowGrade) :
    overflowLattice.le (OverflowGrade.meet firstGrade secondGrade) firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- **`meet a b` is a LOWER bound of the right operand** — `meet a b ≤ b` (the dual of `le_join_right`). -/
theorem overflowMeetLeRight (firstGrade secondGrade : OverflowGrade) :
    overflowLattice.le (OverflowGrade.meet firstGrade secondGrade) secondGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- **`meet a b` is the GREATEST lower bound** — any common lower bound `c` (`c ≤ a` and `c ≤ b`) is dominated
by `meet a b` (`c ≤ meet a b`).  The dual of `join_le`; the impossible `le`-guard cases are refuted by
`noConfusion`, the genuine ones close by `rfl`. -/
theorem overflowLeMeet {firstGrade secondGrade lowerBound : OverflowGrade}
    (firstLower : overflowLattice.le lowerBound firstGrade)
    (secondLower : overflowLattice.le lowerBound secondGrade) :
    overflowLattice.le lowerBound (OverflowGrade.meet firstGrade secondGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases lowerBound <;>
    first | rfl | exact OverflowGrade.noConfusion firstLower | exact OverflowGrade.noConfusion secondLower

/-- **The meet universal property.**  `meet a b` is the GREATEST LOWER BOUND of `{a, b}`: a lower bound of both,
dominating every common lower bound.  The dual of `BoundedJoinSemilattice.join_isLeastUpperBound`; with that
shipped lub, the overflow diamond now carries BOTH lattice universal properties. -/
theorem overflowMeetIsGreatestLowerBound (firstGrade secondGrade : OverflowGrade) :
    overflowLattice.le (OverflowGrade.meet firstGrade secondGrade) firstGrade ∧
    overflowLattice.le (OverflowGrade.meet firstGrade secondGrade) secondGrade ∧
    ∀ lowerBound : OverflowGrade,
      overflowLattice.le lowerBound firstGrade → overflowLattice.le lowerBound secondGrade →
        overflowLattice.le lowerBound (OverflowGrade.meet firstGrade secondGrade) :=
  ⟨overflowMeetLeLeft firstGrade secondGrade, overflowMeetLeRight firstGrade secondGrade,
   fun _lowerBound firstLower secondLower => overflowLeMeet firstLower secondLower⟩

/-- **Concrete: `exactGrade` is the GREATEST lower bound of `wrap` and `trap`** — their `meet` (via `overflowLe
Meet` + the `overflowMeet_wrap_trap` rewrite).  The dual of `overflowConflictIsLeastUpperBoundOfWrapTrap`. -/
theorem overflowExactIsGreatestLowerBoundOfWrapTrap (lowerBound : OverflowGrade)
    (wrapGe : overflowLattice.le lowerBound OverflowGrade.wrapGrade)
    (trapGe : overflowLattice.le lowerBound OverflowGrade.trapGrade) :
    overflowLattice.le lowerBound OverflowGrade.exactGrade :=
  overflowMeet_wrap_trap ▸ overflowLeMeet wrapGe trapGe

/-- **THE dual diamond consequence — the ONLY common lower bound of two distinct overflow modes is the exact
bottom.**  Any grade below both `wrap` and `trap` IS `exactGrade` (`le_antisymm` of "exact is least" and "exact
is the greatest lower bound").  The mirror of `overflowOnlyConflictBoundsWrapTrap`: the antichain `{wrap, trap,
saturate}` is pinched to the exact bottom from below exactly as it escapes to the conflict top from above — the
complete glb/lub picture of the diamond. -/
theorem overflowOnlyExactBoundsWrapTrap (lowerBound : OverflowGrade)
    (wrapGe : overflowLattice.le lowerBound OverflowGrade.wrapGrade)
    (trapGe : overflowLattice.le lowerBound OverflowGrade.trapGrade) :
    lowerBound = OverflowGrade.exactGrade :=
  BoundedJoinSemilattice.le_antisymm overflowIsLawfulBoundedJoinSemilattice
    (overflowExactIsGreatestLowerBoundOfWrapTrap lowerBound wrapGe trapGe)
    (overflowExactIsLeast lowerBound)

end FX1Poly.Modal
