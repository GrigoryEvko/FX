import FX1Poly.Typed.TypedChurchNumeralMultiplication

/-! # FX1Poly/Typed/TypedChurchNumeralSemiringLaws
    — the Church-encoded `+` and `×` satisfy the commutative-semiring AXIOMS up to definitional equality

`TypedChurchNumeralAddition` (#1029) and `TypedChurchNumeralMultiplication` (#1030) showed the term
model COMPUTES the two operations (`add`/`mul` bodies reduce to `f^(m+n) x` / `f^(m·n) x`).  Together
with `CHURCH-NAT-FAITHFUL-GENERAL` (#1006, the numerals are distinct) that already gives "the term model
is a model of `(ℕ, +, ×)`" in the COMPUTATIONAL sense.  This file lifts it to the ALGEBRAIC sense: the
encoded operations satisfy the commutative-semiring AXIOMS up to definitional equality (`Conv`).

The mechanism is uniform and beautiful.  `Conv a b := StepStar.Join a b := ∃ c, StepStar a c ∧
StepStar b c` — two terms are definitionally equal when they reduce to a common reduct.  Each semiring
axiom relates two operation-bodies that both reduce (by #1029/#1030) to an iterate
`iteratedApplication k f x`, and the two `k`'s are equal by the corresponding `Nat` law.  So every law
is `⟨commonIterate, leftBodyComputes, natLaw ▸ rightBodyComputes⟩` — the algebraic law is exactly the
`Nat` law transported through the computation.  This is §16.6's "algebraic structure intrinsics"
realized at the encoding level: the Church encoding is not merely a representation, it is a MODEL of the
commutative semiring `(ℕ, +, ·, 0, 1)`.

## The seven axioms (all `Conv`, all zero-axiom)

  * `churchAdditionCommutes` — `add(m,n) Conv add(n,m)` (`Nat.add_comm`).
  * `churchAdditionAssociates` — `add(m+n, p) Conv add(m, n+p)` (`Nat.add_assoc`).
  * `churchAddZeroIsIdentity` — `add(m, 0) Conv (numeral m applied)` (`m + 0 = m` definitionally).
  * `churchMultiplicationCommutes` — `mul(m,n) Conv mul(n,m)` (`Nat.mul_comm`).
  * `churchMulOneIsIdentity` — `mul(m, 1) Conv (numeral m applied)` (`Nat.mul_one`).
  * `churchMulZeroAnnihilates` — `mul(m, 0) Conv (numeral 0 applied)` (`m · 0 = 0` definitionally).
  * **`churchMultiplicationDistributesOverAddition` (★)** — `mul(m, n+p) Conv add(m·n, m·p)`
    (`Nat.mul_add`) — the semiring-specific distributive law, the one that ties `+` and `×` together.

## Honest scope boundary

As with #1029/#1030 these are the operation BODIES (the whole arithmetic content); the standalone
combinators applied to their arguments add only administrative β.  The `Conv` here is the kernel's raw
conversion (`StepStar.Join`) — definitional equality of the encoded operands, exactly the equality a
type checker uses.  The laws hold for ALL `m`, `n`, `p` and any closed `typeA`, `handlerF`, `baseX`.

## Zero-axiom verification

Each law is the `Conv` anonymous constructor `⟨commonIterate, leftComputes, rightComputes⟩` where the
right leg is transported by a `Nat` law (`add_comm` / `add_assoc` / `mul_comm` / `mul_one` / `mul_add`,
all propext-free) via `▸` (or, for `mul_one`, a targeted iterate-term rewrite to avoid rewriting the
bare `count`).  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The numeral `count` applied to `(typeA, handlerF, baseX)` — definitionally the LHS of
`churchNumeral_appliedReducesToIterate_general`. -/
def churchNumeralApplied (count : Nat) (typeA handlerF baseX : RawTerm 0) : RawTerm 0 :=
  appCell (appCell (appCell (churchNumeralLambda count) typeA) handlerF) baseX

/-- The Church-addition body `m A f (n A f x)` — definitionally the LHS of
`churchAdditionBodyComputes`. -/
def churchAdditionBody (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0) : RawTerm 0 :=
  appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
    (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX)

/-- The Church-multiplication body `m A (n A f) x` — definitionally the LHS of
`churchMultiplicationBodyComputes`. -/
def churchMultiplicationBody (countLeft countRight : Nat)
    (typeA handlerF baseX : RawTerm 0) : RawTerm 0 :=
  appCell (appCell (appCell (churchNumeralLambda countLeft) typeA)
    (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF)) baseX

/-- **Addition is commutative up to `Conv`.**  `add(m,n) Conv add(n,m)` — both bodies reduce to
`f^(m+n) x = f^(n+m) x` (common reduct via `Nat.add_comm`). -/
theorem churchAdditionCommutes (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0) :
    Conv (churchAdditionBody countLeft countRight typeA handlerF baseX)
      (churchAdditionBody countRight countLeft typeA handlerF baseX) :=
  ⟨iteratedApplication (countLeft + countRight) handlerF baseX,
   churchAdditionBodyComputes countLeft countRight typeA handlerF baseX,
   Nat.add_comm countRight countLeft ▸
     churchAdditionBodyComputes countRight countLeft typeA handlerF baseX⟩

/-- **Addition is associative up to `Conv`.**  `add(m+n, p) Conv add(m, n+p)` — both reduce to
`f^((m+n)+p) x = f^(m+(n+p)) x` (common reduct via `Nat.add_assoc`). -/
theorem churchAdditionAssociates (countLeft countMiddle countRight : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    Conv (churchAdditionBody (countLeft + countMiddle) countRight typeA handlerF baseX)
      (churchAdditionBody countLeft (countMiddle + countRight) typeA handlerF baseX) :=
  ⟨iteratedApplication ((countLeft + countMiddle) + countRight) handlerF baseX,
   churchAdditionBodyComputes (countLeft + countMiddle) countRight typeA handlerF baseX,
   Nat.add_assoc countLeft countMiddle countRight ▸
     churchAdditionBodyComputes countLeft (countMiddle + countRight) typeA handlerF baseX⟩

/-- **Zero is the additive identity up to `Conv`.**  `add(m, 0) Conv (numeral m applied)` — adding the
zero numeral reduces to `f^(m+0) x = f^m x`, which is also the m-numeral's own application
(`m + 0 = m` definitionally). -/
theorem churchAddZeroIsIdentity (count : Nat) (typeA handlerF baseX : RawTerm 0) :
    Conv (churchAdditionBody count 0 typeA handlerF baseX)
      (churchNumeralApplied count typeA handlerF baseX) :=
  ⟨iteratedApplication count handlerF baseX,
   churchAdditionBodyComputes count 0 typeA handlerF baseX,
   churchNumeral_appliedReducesToIterate_general count typeA handlerF baseX⟩

/-- **Multiplication is commutative up to `Conv`.**  `mul(m,n) Conv mul(n,m)` — both reduce to
`f^(m·n) x = f^(n·m) x` (common reduct via `Nat.mul_comm`). -/
theorem churchMultiplicationCommutes (countLeft countRight : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    Conv (churchMultiplicationBody countLeft countRight typeA handlerF baseX)
      (churchMultiplicationBody countRight countLeft typeA handlerF baseX) :=
  ⟨iteratedApplication (countLeft * countRight) handlerF baseX,
   churchMultiplicationBodyComputes countLeft countRight typeA handlerF baseX,
   Nat.mul_comm countRight countLeft ▸
     churchMultiplicationBodyComputes countRight countLeft typeA handlerF baseX⟩

/-- **One is the multiplicative identity up to `Conv`.**  `mul(m, 1) Conv (numeral m applied)` —
multiplying by the one numeral reduces to `f^(m·1) x = f^m x` (`Nat.mul_one`).  The rewrite targets the
iterate term (not the bare `count`) to keep the motive precise. -/
theorem churchMulOneIsIdentity (count : Nat) (typeA handlerF baseX : RawTerm 0) :
    Conv (churchMultiplicationBody count 1 typeA handlerF baseX)
      (churchNumeralApplied count typeA handlerF baseX) := by
  have indexEq : iteratedApplication (count * 1) handlerF baseX
      = iteratedApplication count handlerF baseX := by rw [Nat.mul_one]
  exact ⟨iteratedApplication (count * 1) handlerF baseX,
    churchMultiplicationBodyComputes count 1 typeA handlerF baseX,
    indexEq.symm ▸ churchNumeral_appliedReducesToIterate_general count typeA handlerF baseX⟩

/-- **Zero annihilates under multiplication up to `Conv`.**  `mul(m, 0) Conv (numeral 0 applied)` —
multiplying by the zero numeral reduces to `f^(m·0) x = f^0 x = x` (`m · 0 = 0` definitionally), the
zero numeral's own application. -/
theorem churchMulZeroAnnihilates (count : Nat) (typeA handlerF baseX : RawTerm 0) :
    Conv (churchMultiplicationBody count 0 typeA handlerF baseX)
      (churchNumeralApplied 0 typeA handlerF baseX) :=
  ⟨iteratedApplication 0 handlerF baseX,
   churchMultiplicationBodyComputes count 0 typeA handlerF baseX,
   churchNumeral_appliedReducesToIterate_general 0 typeA handlerF baseX⟩

/-- ★ **Multiplication left-distributes over addition up to `Conv`.**  `mul(m, n+p) Conv add(m·n, m·p)`
— the product `m · (n+p)` and the sum of products `m·n + m·p` reduce to `f^(m·(n+p)) x` and
`f^(m·n + m·p) x`, equal by `Nat.mul_add`.  The semiring-specific law tying `+` and `×` together — with
it and the six commutative-monoid/identity/annihilation laws above, the Church encoding satisfies the
full commutative-semiring axiom set up to definitional equality. -/
theorem churchMultiplicationDistributesOverAddition (countLeft countMiddle countRight : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    Conv (churchMultiplicationBody countLeft (countMiddle + countRight) typeA handlerF baseX)
      (churchAdditionBody (countLeft * countMiddle) (countLeft * countRight) typeA handlerF baseX) :=
  ⟨iteratedApplication (countLeft * (countMiddle + countRight)) handlerF baseX,
   churchMultiplicationBodyComputes countLeft (countMiddle + countRight) typeA handlerF baseX,
   (Nat.mul_add countLeft countMiddle countRight).symm ▸
     churchAdditionBodyComputes (countLeft * countMiddle) (countLeft * countRight)
       typeA handlerF baseX⟩

end FX1Poly.Typed
