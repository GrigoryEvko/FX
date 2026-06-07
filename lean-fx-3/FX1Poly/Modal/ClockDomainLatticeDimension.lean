import FX1Poly.Modal.EffectLatticeClassification
import FX1Poly.Modal.OverflowLatticeDimension

/-! # FX1Poly/Modal/ClockDomainLatticeDimension
    — the CLOCK-DOMAIN dimension (§6.3 Dim 12 / §18.7) as the FIRST PARAMETERIZED (infinite-carrier)
      bounded join-semilattice

`EffectLatticeClassification.lean` shipped the lattice-graded engine (`BoundedJoinSemilattice` +
`IsLawfulBoundedJoinSemilattice` + the pointwise product + the induced order); `OverflowLatticeDimension.lean`
exercised it on the first NON-CHAIN instance (the finite diamond M3 — a three-element antichain).  Every
lattice dimension shipped so far — effect `{pure < impure}`, trust, security, overflow `{exact, wrap, trap,
saturate}` — has a FINITE carrier (a closed enum).  This file exercises the engine on a genuinely new shape:
the CLOCK-DOMAIN dimension, whose carrier is INFINITE (parameterized by a clock identifier), giving the
first lattice dimension with an INFINITE antichain.

## The clock-domain lattice (§6.3 Dim 12 / §18.7)

§6.3 Dim 12 / §18.7: a hardware signal is `combinational` (the default — feeds any domain) or driven by a
specific clock `sync(clk_id)`; combining two signals follows `combinational + x = x`, `sync(a) + sync(a) =
sync(a)`, and `sync(a) + sync(b) = CROSS_DOMAIN_ERROR` when `a != b` (mixing two distinct clock domains
without a synchronizer is a type error).  We model this as a bounded join-semilattice:

  * `combinational` — the BOTTOM (a combinational signal absorbs into any domain: the join identity).
  * `sync clockId` — one element per clock identifier (`clockId : Nat`), an INFINITE ANTICHAIN: distinct
    clocks are pairwise incomparable.
  * `crossDomainError` — the TOP, the join of any two distinct `sync` domains: the algebraic realization of
    "mixing clock domains is a type error" (the same role overflow's `conflict` and the §6.4 permission
    PCM's `CONFLICT` play).

`join` is the lattice supremum: `combinational` is the identity; two equal clocks join to themselves; two
DISTINCT clocks join to `crossDomainError`; `crossDomainError` absorbs.  This is the "flat lattice with a
top" over the set of clock identifiers — and, crucially, the first lattice instance whose carrier is INFINITE
(so the engine's antisymmetric order is exercised on an infinite antichain, not a fixed finite one).

## What lands here (all zero-axiom)

  * `ClockGrade` (3-ctor inductive, one ctor carrying a `Nat`) + `ClockGrade.join` (the spec-faithful
    join, the `sync`-`sync` arm guarded by a `Nat.beq` equality test — propext-free Bool-`bif`).
  * `natBeqReflexive` / `natEqOfBeqTrue` / `natBeqCommutes` — the three propext-clean `Nat.beq` facts the
    parameterized join laws need (hand-rolled by structural recursion — `Nat.beq` decision facts, no
    propext, the contrast with the finite enums whose laws were pure `cases <;> rfl`).
  * `clockLattice` + `clockIsLawfulBoundedJoinSemilattice` — the clock domain is a verified bounded
    join-semilattice; comm/assoc go through the `Nat.beq` case analysis (the genuinely-new proof obligation
    a parameterized carrier introduces over a finite enum).
  * **`clockSyncIncomparableOfDistinct`** — the genuinely NEW content: for EVERY pair of distinct clocks
    `a != b`, `sync a` and `sync b` are incomparable (`¬ le a b ∧ ¬ le b a`).  This is an INFINITE antichain
    — no finite-enum dimension (overflow's three-element antichain included) has one.
  * `clockSyncJoinDistinctIsCrossDomain` — the cross-domain-error semantics: mixing two distinct clocks
    yields the `crossDomainError` top (§18.7's "mixing without a synchronizer is a type error").
  * `clockSync01Incomparable` — a concrete non-vacuity witness (`sync 0` / `sync 1` incomparable).
  * `clockCombinationalIsLeast` / `clockCrossDomainIsGreatest` — `combinational` is the bottom (via the
    generic `bottom_le`) and `crossDomainError` the top of the induced order.
  * `clockOverflowProductLattice` + `clockOverflowProductIsLawful` — the clock dimension composes with the
    OVERFLOW dimension via the shipped `productIsLawful`: TWO antichain-bearing lattices (one infinite, one a
    finite diamond) combine into one lawful lattice dimension with NO per-product re-proof — the §6.8
    lattice-family composition is shape- AND cardinality-agnostic.

## Honest scope boundary

This adds the clock-domain lattice as a structurally-new (infinite-carrier) member of the
bounded-join-semilattice family and proves it lawful + genuinely infinite-antichain + composable.  Like the
overflow file, it does NOT fold `clock` into the closed `GradedDimensionName` classification enum (a
deferred purely-additive cross-file edit); the lawfulness + infinite-antichain theorems here ARE the
classification evidence.  The full §18.7 clock-domain semantics also carries the explicit-synchronizer
construct (`sync_2ff`) that legally crosses domains; only the COMBINE algebra — the lattice — is modeled here.

## Zero-axiom verification

`ClockGrade` is a plain (non-indexed) inductive with derived `DecidableEq` (the `Nat` field routes through
`Nat.decEq`, propext-clean); the parameterized `sync`-`sync` join laws close by `Nat.beq` case analysis using
the three hand-rolled propext-clean `Nat.beq` facts (`Bool.cond_true` / `Bool.cond_false` discharge the guard
residues, exactly as the §6.4 permission proof does); the identity/absorber sub-cases use small
`cases <;> rfl` helper lemmas (a `combinational`/`crossDomainError` join through a stuck `sync`-`sync` guard
does not reduce by `rfl`, so it is rewritten away); incomparability is the defeq route `ClockGrade.noConfusion`
after rewriting the guard `false`; composition reuses the shipped `productIsLawful`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-! ## Propext-clean `Nat.beq` facts

A parameterized carrier (`sync clockId`) makes the join laws depend on the decidable equality of clock
identifiers.  The three facts below — reflexivity, soundness, and commutativity of `Nat.beq` — are
hand-rolled by structural recursion so they are guaranteed propext-free (unlike `Nat.mul_assoc` /
`Nat.add_mul`, several core `Nat` lemmas leak `propext`; these tiny decision facts do not). -/

/-- `Nat.beq n n` is `true` — reflexivity of the boolean equality test, by recursion on `n`. -/
theorem natBeqReflexive : (clockId : Nat) → Nat.beq clockId clockId = true
  | 0 => rfl
  | clockId + 1 => natBeqReflexive clockId

/-- `Nat.beq` is sound: a `true` test forces equality, by recursion on both arguments. -/
theorem natEqOfBeqTrue : (first second : Nat) → Nat.beq first second = true → first = second
  | 0,         0,          _ => rfl
  | 0,         _ + 1,      h => Bool.noConfusion h
  | _ + 1,     0,          h => Bool.noConfusion h
  | first + 1, second + 1, h => congrArg Nat.succ (natEqOfBeqTrue first second h)

/-- `Nat.beq` is commutative, by recursion on both arguments. -/
theorem natBeqCommutes : (first second : Nat) → Nat.beq first second = Nat.beq second first
  | 0,         0         => rfl
  | 0,         _ + 1     => rfl
  | _ + 1,     0         => rfl
  | first + 1, second + 1 => natBeqCommutes first second

/-! ## The clock-domain grade and its join -/

/-- The clock-domain grade (§6.3 Dim 12 / §18.7): `combinational` (feeds any domain — the bottom), a
clock-driven signal `sync clockId` (one element per clock identifier — an infinite antichain), and
`crossDomainError` (the top — mixing two distinct clock domains is a type error). -/
inductive ClockGrade where
  | combinational
  | sync (clockId : Nat)
  | crossDomainError
  deriving DecidableEq

/-- Clock-domain join — the lattice supremum.  `combinational` is the identity (a combinational signal
feeds any domain); two equal clocks join to themselves; two DISTINCT clocks join to `crossDomainError` (the
§18.7 "mixing clock domains is a type error"); `crossDomainError` absorbs.  The `sync`-`sync` arm is guarded
by `Nat.beq` (a Bool-`bif`, propext-free); the rest is a full 3×3 enumeration. -/
def ClockGrade.join : ClockGrade → ClockGrade → ClockGrade
  | .combinational,    .combinational    => .combinational
  | .combinational,    .sync d           => .sync d
  | .combinational,    .crossDomainError => .crossDomainError
  | .sync c,           .combinational    => .sync c
  | .sync c,           .sync d           => bif Nat.beq c d then .sync c else .crossDomainError
  | .sync _,           .crossDomainError => .crossDomainError
  | .crossDomainError, .combinational    => .crossDomainError
  | .crossDomainError, .sync _           => .crossDomainError
  | .crossDomainError, .crossDomainError => .crossDomainError

/-! ## Identity / absorber helpers

A `combinational` or `crossDomainError` join whose OTHER argument is a stuck `sync`-`sync` guard does not
reduce by `rfl` (the join keys on the other argument's head ctor, which a `bif` hides).  These four lemmas —
proved by casing the other argument so its head is known — let the associativity proof rewrite such joins
away instead of relying on a stuck `rfl`. -/

/-- `combinational` is the left identity for the join. -/
theorem clockJoinCombinationalLeft (grade : ClockGrade) :
    ClockGrade.join .combinational grade = grade := by cases grade <;> rfl

/-- `combinational` is the right identity for the join. -/
theorem clockJoinCombinationalRight (grade : ClockGrade) :
    ClockGrade.join grade .combinational = grade := by cases grade <;> rfl

/-- `crossDomainError` absorbs on the left. -/
theorem clockJoinCrossDomainLeft (grade : ClockGrade) :
    ClockGrade.join .crossDomainError grade = .crossDomainError := by cases grade <;> rfl

/-- `crossDomainError` absorbs on the right. -/
theorem clockJoinCrossDomainRight (grade : ClockGrade) :
    ClockGrade.join grade .crossDomainError = .crossDomainError := by cases grade <;> rfl

/-- A clock joined with itself is itself (idempotence at a `sync` element — via `natBeqReflexive`). -/
theorem clockJoinSyncWithSelf (clockId : Nat) :
    ClockGrade.join (.sync clockId) (.sync clockId) = .sync clockId := by
  show (bif Nat.beq clockId clockId then ClockGrade.sync clockId else ClockGrade.crossDomainError)
     = ClockGrade.sync clockId
  rw [natBeqReflexive clockId, Bool.cond_true]

/-! ## The bounded join-semilattice -/

/-- The clock-domain bounded join-semilattice: carrier `ClockGrade`, bottom `combinational`, the
clock-domain join. -/
def clockLattice : BoundedJoinSemilattice where
  Carrier := ClockGrade
  bottom := .combinational
  join := ClockGrade.join
  carrierDecEq := instDecidableEqClockGrade

/-- **Combining clock domains is commutative.**  The `sync`-`sync` arm uses `natBeqCommutes` (the guard is
symmetric) and `natEqOfBeqTrue` (when the guard fires the two clocks are equal, so the kept clock agrees). -/
theorem clockJoinCommutes (first second : ClockGrade) :
    ClockGrade.join first second = ClockGrade.join second first := by
  cases first with
  | combinational => cases second <;> rfl
  | sync c =>
      cases second with
      | combinational => rfl
      | sync d =>
          show (bif Nat.beq c d then ClockGrade.sync c else ClockGrade.crossDomainError)
             = (bif Nat.beq d c then ClockGrade.sync d else ClockGrade.crossDomainError)
          rw [natBeqCommutes c d]
          cases h : Nat.beq d c with
          | false => rfl
          | true => exact congrArg ClockGrade.sync (natEqOfBeqTrue d c h).symm
      | crossDomainError => rfl
  | crossDomainError => cases second <;> rfl

/-- **Combining clock domains is associative.**  Only the `sync`-`sync`-`sync` arm is non-trivial: a nested
`Nat.beq` case analysis showing that any pairwise cross-domain forces the whole to cross-domain, and when all
three clocks agree the kept clock is the same in both association orders.  The mixed `combinational` /
`crossDomainError` arms are discharged by the identity/absorber helpers (a stuck `sync`-`sync` guard blocks a
direct `rfl`). -/
theorem clockJoinAssociates (first second third : ClockGrade) :
    ClockGrade.join (ClockGrade.join first second) third
      = ClockGrade.join first (ClockGrade.join second third) := by
  cases first with
  | combinational =>
      rw [clockJoinCombinationalLeft second, clockJoinCombinationalLeft (ClockGrade.join second third)]
  | crossDomainError =>
      rw [clockJoinCrossDomainLeft second, clockJoinCrossDomainLeft third,
        clockJoinCrossDomainLeft (ClockGrade.join second third)]
  | sync p =>
      cases second with
      | combinational =>
          rw [clockJoinCombinationalRight (ClockGrade.sync p), clockJoinCombinationalLeft third]
      | crossDomainError =>
          rw [clockJoinCrossDomainRight (ClockGrade.sync p)]
          cases third <;> rfl
      | sync q =>
          cases third with
          | combinational =>
              rw [clockJoinCombinationalRight (ClockGrade.join (ClockGrade.sync p) (ClockGrade.sync q)),
                clockJoinCombinationalRight (ClockGrade.sync q)]
          | crossDomainError =>
              rw [clockJoinCrossDomainRight (ClockGrade.join (ClockGrade.sync p) (ClockGrade.sync q)),
                clockJoinCrossDomainRight (ClockGrade.sync q), clockJoinCrossDomainRight (ClockGrade.sync p)]
          | sync r =>
              show ClockGrade.join (bif Nat.beq p q then ClockGrade.sync p else ClockGrade.crossDomainError)
                     (ClockGrade.sync r)
                 = ClockGrade.join (ClockGrade.sync p)
                     (bif Nat.beq q r then ClockGrade.sync q else ClockGrade.crossDomainError)
              cases hpq : Nat.beq p q with
              | false =>
                  cases hqr : Nat.beq q r with
                  | false => rfl
                  | true =>
                      show ClockGrade.crossDomainError
                         = bif Nat.beq p q then ClockGrade.sync p else ClockGrade.crossDomainError
                      rw [hpq, Bool.cond_false]
              | true =>
                  have clocksAgree : p = q := natEqOfBeqTrue p q hpq
                  subst clocksAgree
                  show (bif Nat.beq p r then ClockGrade.sync p else ClockGrade.crossDomainError)
                     = ClockGrade.join (ClockGrade.sync p)
                         (bif Nat.beq p r then ClockGrade.sync p else ClockGrade.crossDomainError)
                  cases hpr : Nat.beq p r with
                  | false => rfl
                  | true =>
                      show ClockGrade.sync p
                         = bif Nat.beq p p then ClockGrade.sync p else ClockGrade.crossDomainError
                      rw [natBeqReflexive p, Bool.cond_true]

/-- **The clock domain IS a verified bounded join-semilattice.**  Unlike effect / trust / security /
overflow, its carrier is INFINITE; the laws nonetheless hold, with comm/assoc routed through the `Nat.beq`
case analysis (the new obligation a parameterized carrier introduces). -/
theorem clockIsLawfulBoundedJoinSemilattice : IsLawfulBoundedJoinSemilattice clockLattice where
  join_comm := clockJoinCommutes
  join_assoc := clockJoinAssociates
  join_idempotent := fun grade => by
    cases grade with
    | combinational => rfl
    | sync clockId => exact clockJoinSyncWithSelf clockId
    | crossDomainError => rfl
  bottom_join := fun grade => by cases grade <;> rfl
  join_bottom := fun grade => by cases grade <;> rfl

/-! ## The infinite antichain — the genuinely new content

For EVERY pair of distinct clocks the two `sync` elements are incomparable.  This is an INFINITE antichain:
no finite-enum lattice dimension (overflow's three-element antichain included) exercises the engine's
antisymmetric order on an unbounded set of pairwise-incomparable elements. -/

/-- **Distinct clocks are incomparable.**  For any two distinct clock identifiers, `sync a` and `sync b` are
pairwise incomparable in the induced order — an INFINITE antichain.  Each `¬ le` reduces (by the join + the
distinctness guard) to refuting `crossDomainError = sync _`. -/
theorem clockSyncIncomparableOfDistinct (firstClock secondClock : Nat)
    (distinct : Nat.beq firstClock secondClock = false) :
    ¬ clockLattice.le (ClockGrade.sync firstClock) (ClockGrade.sync secondClock) ∧
    ¬ clockLattice.le (ClockGrade.sync secondClock) (ClockGrade.sync firstClock) := by
  refine ⟨fun leEq => ?_, fun leEq => ?_⟩
  · change (bif Nat.beq firstClock secondClock then ClockGrade.sync firstClock
              else ClockGrade.crossDomainError)
        = ClockGrade.sync secondClock at leEq
    rw [distinct] at leEq
    exact ClockGrade.noConfusion leEq
  · change (bif Nat.beq secondClock firstClock then ClockGrade.sync secondClock
              else ClockGrade.crossDomainError)
        = ClockGrade.sync firstClock at leEq
    rw [natBeqCommutes secondClock firstClock, distinct] at leEq
    exact ClockGrade.noConfusion leEq

/-- **Cross-domain mixing is the error top.**  Combining two distinct clock domains yields `crossDomainError`
(§18.7: mixing without a synchronizer is a type error). -/
theorem clockSyncJoinDistinctIsCrossDomain (firstClock secondClock : Nat)
    (distinct : Nat.beq firstClock secondClock = false) :
    clockLattice.join (ClockGrade.sync firstClock) (ClockGrade.sync secondClock)
      = ClockGrade.crossDomainError := by
  show (bif Nat.beq firstClock secondClock then ClockGrade.sync firstClock else ClockGrade.crossDomainError)
     = ClockGrade.crossDomainError
  rw [distinct, Bool.cond_false]

/-- Concrete non-vacuity: clocks `0` and `1` are incomparable (the infinite antichain is inhabited). -/
theorem clockSync01Incomparable :
    ¬ clockLattice.le (ClockGrade.sync 0) (ClockGrade.sync 1) ∧
    ¬ clockLattice.le (ClockGrade.sync 1) (ClockGrade.sync 0) :=
  clockSyncIncomparableOfDistinct 0 1 rfl

/-! ## Bounds — combinational is the bottom, crossDomainError the top -/

/-- `combinational` is the least element (via the generic `bottom_le`). -/
theorem clockCombinationalIsLeast (grade : ClockGrade) :
    clockLattice.le ClockGrade.combinational grade :=
  BoundedJoinSemilattice.bottom_le clockIsLawfulBoundedJoinSemilattice grade

/-- `crossDomainError` is the greatest element: every grade is below it. -/
theorem clockCrossDomainIsGreatest (grade : ClockGrade) :
    clockLattice.le grade ClockGrade.crossDomainError := by cases grade <;> rfl

/-! ## Cross-family composition — two antichain-bearing lattices compose -/

/-- The `clock × overflow` composite lattice — an INFINITE-antichain dimension composed with a finite
NON-CHAIN (diamond) dimension. -/
def clockOverflowProductLattice : BoundedJoinSemilattice :=
  clockLattice.product overflowLattice

/-- **Clock × overflow IS a lawful bounded join-semilattice** — two antichain-bearing dimensions (one with an
infinite antichain, one a finite diamond) compose into one lawful lattice dimension via the shipped
`productIsLawful`, with NO per-product re-proof.  Concrete evidence that the §6.8 lattice-family composition
is shape- AND cardinality-agnostic: it does not care whether a factor is a chain, a finite antichain, or an
infinite one. -/
theorem clockOverflowProductIsLawful :
    IsLawfulBoundedJoinSemilattice clockOverflowProductLattice :=
  BoundedJoinSemilattice.productIsLawful clockIsLawfulBoundedJoinSemilattice
    overflowIsLawfulBoundedJoinSemilattice

end FX1Poly.Modal
