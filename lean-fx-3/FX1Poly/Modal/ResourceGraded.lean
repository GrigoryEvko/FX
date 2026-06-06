/-!
# Resource-Graded Doctrine (Abel-Danielsson-Eriksson arXiv:2603.29716)

An ordered grade semiring models resource usage in quantitative type theory.
Each variable carries a grade from a partially ordered semiring R = (R, 0, 1, +, *, ≤).
The typing rules consume/scale grades per the semiring operations:
- VAR uses grade 1 at the variable position
- LAM: body's grade of the binder = function's parameter grade
- APP: grade of argument scaled by function's parameter grade
- IF: grade = join of both branches (worst case)

For FX: the Usage dimension {0, 1, ω} is the primary instance.
Security {unclassified < classified} is another instance.

Reference: arXiv:2603.29716 (Agda-formalized).
Zero external dependencies.

## Propext-free discipline

Each grade operation is defined by **full enumeration over the
product space** of the inductive arguments, rather than overlapping
curried patterns like `| .zero, g => g | g, .zero => g` (whose
overlap at `.zero, .zero` makes Lean's match compiler emit `propext`
in the auto-generated equation lemmas):

  * UsageGrade.add: 3 × 3 = 9 arms
  * UsageGrade.mul: 9 arms
  * UsageGrade.le:  9 arms
  * SecurityGrade.add: 2 × 2 = 4 arms
  * SecurityGrade.le:  4 arms

Every arm pattern is a CTOR pair with no wildcard, no overlap, so
Lean's match compiler emits no equation-lemma propext.  All seven
declarations (the five operations above plus `fxUsageSemiring` and
`fxSecuritySemiring`) pass `#print axioms` clean.

The semiring-law theorems close by full case enumeration (`cases ... <;> rfl` for the equational
laws).  The trivial fragment (`add_comm`, `add_zero`, `zero_add`, `mul_one`, `one_mul`,
`mul_zero`, `zero_mul`, `linear_div_omega_eq_zero`) appears first; the COMPLETE ordered-semiring
law set — associativity of both operations, distributivity, and the order laws (reflexivity,
transitivity, antisymmetry, `+`/`*` monotonicity) — plus the `IsLawfulOrderedGradeSemiring`
verified-semiring bundle and its witness `fxUsageSemiring_isLawful` follow at the bottom of the
file (DIM2-1, §6.1).

Pattern catalogued in
`feedback_lean_match_propext_recipe.md`.
-/

namespace FX1Poly.Modal

/-- A partially ordered semiring: the grade algebra for QTT.
(R, 0, 1, +, *, ≤) with semiring laws + order compatibility. -/
structure OrderedGradeSemiring where
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  le : Carrier → Carrier → Bool
  /-- DecidableEq on carriers. -/
  carrierDecEq : DecidableEq Carrier

/-- FX's usage semiring: {0, 1, ω} with 0+0=0, 1+1=ω, ω+ω=ω. -/
inductive UsageGrade where
  | zero
  | one
  | omega
  deriving DecidableEq, Repr

/-- Usage-grade addition.  Full 3×3 enumeration; no wildcard, no
overlapping patterns — propext-free. -/
def UsageGrade.add : UsageGrade → UsageGrade → UsageGrade
  | .zero,  .zero  => .zero
  | .zero,  .one   => .one
  | .zero,  .omega => .omega
  | .one,   .zero  => .one
  | .one,   .one   => .omega
  | .one,   .omega => .omega
  | .omega, .zero  => .omega
  | .omega, .one   => .omega
  | .omega, .omega => .omega

/-- Usage-grade multiplication.  Full 3×3 enumeration; propext-free. -/
def UsageGrade.mul : UsageGrade → UsageGrade → UsageGrade
  | .zero,  .zero  => .zero
  | .zero,  .one   => .zero
  | .zero,  .omega => .zero
  | .one,   .zero  => .zero
  | .one,   .one   => .one
  | .one,   .omega => .omega
  | .omega, .zero  => .zero
  | .omega, .one   => .omega
  | .omega, .omega => .omega

/-- Usage-grade order: `zero ≤ one ≤ omega`.  Full 3×3 enumeration;
propext-free. -/
def UsageGrade.le : UsageGrade → UsageGrade → Bool
  | .zero,  .zero  => true
  | .zero,  .one   => true
  | .zero,  .omega => true
  | .one,   .zero  => false
  | .one,   .one   => true
  | .one,   .omega => true
  | .omega, .zero  => false
  | .omega, .one   => false
  | .omega, .omega => true

/-- The FX usage semiring instance. -/
def fxUsageSemiring : OrderedGradeSemiring where
  Carrier := UsageGrade
  zero := .zero
  one := .one
  add := UsageGrade.add
  mul := UsageGrade.mul
  le := UsageGrade.le
  carrierDecEq := instDecidableEqUsageGrade

/-- FX's security semiring: {unclassified < classified}. -/
inductive SecurityGrade where
  | unclassified
  | classified
  deriving DecidableEq, Repr

/-- Security-grade addition (join): unclassified is the bottom; any
classified input poisons the result.  Full 2×2 enumeration;
propext-free. -/
def SecurityGrade.add : SecurityGrade → SecurityGrade → SecurityGrade
  | .unclassified, .unclassified => .unclassified
  | .unclassified, .classified   => .classified
  | .classified,   .unclassified => .classified
  | .classified,   .classified   => .classified

/-- Security-grade multiplication (meet on the boolean lattice
{unclassified < classified}).  Full 2×2 enumeration with
distinct-CTOR overlap-free patterns; propext-free. -/
def SecurityGrade.mul : SecurityGrade → SecurityGrade → SecurityGrade
  | .unclassified, .unclassified => .unclassified
  | .unclassified, .classified   => .unclassified
  | .classified,   .unclassified => .unclassified
  | .classified,   .classified   => .classified

/-- Security-grade order: `unclassified ≤ classified`.  Full 2×2
enumeration; propext-free. -/
def SecurityGrade.le : SecurityGrade → SecurityGrade → Bool
  | .unclassified, .unclassified => true
  | .unclassified, .classified   => true
  | .classified,   .unclassified => false
  | .classified,   .classified   => true

/-- The FX security semiring instance.  Per §6.1/§6.3 (dim 5): `add` is the JOIN (combining secrecy
— `unclassified + classified = classified`, no implicit downgrade) and `mul` is the MEET
`SecurityGrade.mul` (sequential composition with annihilation `classified * unclassified =
unclassified` — ghost computation on a secret leaks nothing).  `zero = unclassified` is the join
bottom and the meet annihilator; `one = classified` is the meet top.  The lawful-semiring witness is
`fxSecuritySemiring_isLawful` (DIM5-1, below). -/
def fxSecuritySemiring : OrderedGradeSemiring where
  Carrier := SecurityGrade
  zero := .unclassified
  one := .classified
  add := SecurityGrade.add
  mul := SecurityGrade.mul
  le := SecurityGrade.le
  carrierDecEq := instDecidableEqSecurityGrade

/-- Semiring laws verification (usage). -/
theorem UsageGrade.add_comm (firstGrade secondGrade : UsageGrade) :
    UsageGrade.add firstGrade secondGrade =
      UsageGrade.add secondGrade firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

theorem UsageGrade.add_zero (someGrade : UsageGrade) :
    UsageGrade.add someGrade .zero = someGrade := by
  cases someGrade <;> rfl

theorem UsageGrade.zero_add (someGrade : UsageGrade) :
    UsageGrade.add .zero someGrade = someGrade := by
  cases someGrade <;> rfl

theorem UsageGrade.mul_one (someGrade : UsageGrade) :
    UsageGrade.mul someGrade .one = someGrade := by
  cases someGrade <;> rfl

theorem UsageGrade.one_mul (someGrade : UsageGrade) :
    UsageGrade.mul .one someGrade = someGrade := by
  cases someGrade <;> rfl

theorem UsageGrade.mul_zero (someGrade : UsageGrade) :
    UsageGrade.mul someGrade .zero = .zero := by
  cases someGrade <;> rfl

theorem UsageGrade.zero_mul (someGrade : UsageGrade) :
    UsageGrade.mul .zero someGrade = .zero := by
  cases someGrade <;> rfl

/-- The Atkey-McBride attack: using linear variable twice in unrestricted
closure. Wood-Atkey 2022 corrected Lam rule prevents this via context
division: 1/ω = 0, so linear vars erased in replicable closures. -/
theorem UsageGrade.linear_div_omega_eq_zero :
    UsageGrade.mul .one .zero = .zero := rfl

/-! ## The complete ordered-semiring law set (DIM2-1, §6.1)

The grade algebra of §6.1 is an ORDERED semiring `(R, +, *, 0, 1, ≤)`: `(R, +, 0)` a commutative
monoid, `(R, *, 1)` a monoid, `*` distributing over `+`, `0` annihilating, and `≤` a partial order
compatible with `+` and `*`.  The identity / annihilation / add-commutativity laws above are only
the trivial fragment; the laws that actually MAKE it a semiring — associativity of both operations
and distributivity — together with the order laws are proved here.  Each closes by full case
enumeration: `cases … <;> rfl` for the equational laws; for the order laws,
`cases … <;> first | rfl | Bool.noConfusion …` discharges the impossible `false = true` premises
(the `≤`-false cases) via `Bool.noConfusion` while `rfl` closes the genuine `true` goals.  All
propext-free, all zero-axiom. -/

/-- Associativity of usage addition — the commutative-monoid law `(R, +, 0)` was missing. -/
theorem UsageGrade.add_assoc (firstGrade secondGrade thirdGrade : UsageGrade) :
    UsageGrade.add (UsageGrade.add firstGrade secondGrade) thirdGrade =
      UsageGrade.add firstGrade (UsageGrade.add secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- Associativity of usage multiplication — the monoid law `(R, *, 1)`. -/
theorem UsageGrade.mul_assoc (firstGrade secondGrade thirdGrade : UsageGrade) :
    UsageGrade.mul (UsageGrade.mul firstGrade secondGrade) thirdGrade =
      UsageGrade.mul firstGrade (UsageGrade.mul secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- Commutativity of usage multiplication.  Usage is a COMMUTATIVE semiring (sequential use of
two grades is order-independent); §6.1 only requires `*` to be a monoid, so this is a bonus
per-instance law beyond the general ordered-semiring bundle below. -/
theorem UsageGrade.mul_comm (firstGrade secondGrade : UsageGrade) :
    UsageGrade.mul firstGrade secondGrade = UsageGrade.mul secondGrade firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- Left distributivity `a * (b + c) = a * b + a * c` — the law connecting the two monoids into a
semiring.  Without it, `fxUsageSemiring` is just two unrelated monoids, not a semiring. -/
theorem UsageGrade.left_distrib (firstGrade secondGrade thirdGrade : UsageGrade) :
    UsageGrade.mul firstGrade (UsageGrade.add secondGrade thirdGrade) =
      UsageGrade.add (UsageGrade.mul firstGrade secondGrade)
        (UsageGrade.mul firstGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- Right distributivity `(a + b) * c = a * c + b * c`. -/
theorem UsageGrade.right_distrib (firstGrade secondGrade thirdGrade : UsageGrade) :
    UsageGrade.mul (UsageGrade.add firstGrade secondGrade) thirdGrade =
      UsageGrade.add (UsageGrade.mul firstGrade thirdGrade)
        (UsageGrade.mul secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- Reflexivity of the usage order `zero ≤ one ≤ omega`. -/
theorem UsageGrade.le_refl (someGrade : UsageGrade) :
    UsageGrade.le someGrade someGrade = true := by
  cases someGrade <;> rfl

/-- Transitivity of the usage order.  In the impossible cases (`a ≤ c` false) one of the premises
is `false = true`, refuted by `Bool.noConfusion`. -/
theorem UsageGrade.le_trans {firstGrade secondGrade thirdGrade : UsageGrade}
    (firstBelowSecond : UsageGrade.le firstGrade secondGrade = true)
    (secondBelowThird : UsageGrade.le secondGrade thirdGrade = true) :
    UsageGrade.le firstGrade thirdGrade = true := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;>
    first
      | rfl
      | exact Bool.noConfusion firstBelowSecond
      | exact Bool.noConfusion secondBelowThird

/-- Antisymmetry — the usage order is a PARTIAL order, not merely a preorder. -/
theorem UsageGrade.le_antisymm {firstGrade secondGrade : UsageGrade}
    (firstBelowSecond : UsageGrade.le firstGrade secondGrade = true)
    (secondBelowFirst : UsageGrade.le secondGrade firstGrade = true) :
    firstGrade = secondGrade := by
  cases firstGrade <;> cases secondGrade <;>
    first
      | rfl
      | exact Bool.noConfusion firstBelowSecond
      | exact Bool.noConfusion secondBelowFirst

/-- Order compatibility with addition: `b ≤ c → a + b ≤ a + c` (`+` is monotone). -/
theorem UsageGrade.add_le_add_left {firstGrade secondGrade : UsageGrade}
    (scaleGrade : UsageGrade) (firstBelowSecond : UsageGrade.le firstGrade secondGrade = true) :
    UsageGrade.le (UsageGrade.add scaleGrade firstGrade)
      (UsageGrade.add scaleGrade secondGrade) = true := by
  cases scaleGrade <;> cases firstGrade <;> cases secondGrade <;>
    first | rfl | exact Bool.noConfusion firstBelowSecond

/-- Order compatibility with multiplication: `b ≤ c → a * b ≤ a * c` (`*` is monotone). -/
theorem UsageGrade.mul_le_mul_left {firstGrade secondGrade : UsageGrade}
    (scaleGrade : UsageGrade) (firstBelowSecond : UsageGrade.le firstGrade secondGrade = true) :
    UsageGrade.le (UsageGrade.mul scaleGrade firstGrade)
      (UsageGrade.mul scaleGrade secondGrade) = true := by
  cases scaleGrade <;> cases firstGrade <;> cases secondGrade <;>
    first | rfl | exact Bool.noConfusion firstBelowSecond

/-- Order compatibility — two-sided: `a ≤ a' → b ≤ b' → a + b ≤ a' + b'` (`+` is monotone in both
arguments).  Companion to `add_le_add_left`; `GradeVector.IsPointwiseBelow.add_mono` lifts it
pointwise. -/
theorem UsageGrade.add_le_add {firstGrade firstBound secondGrade secondBound : UsageGrade}
    (firstBelow : UsageGrade.le firstGrade firstBound = true)
    (secondBelow : UsageGrade.le secondGrade secondBound = true) :
    UsageGrade.le (UsageGrade.add firstGrade secondGrade)
      (UsageGrade.add firstBound secondBound) = true := by
  cases firstGrade <;> cases firstBound <;> cases secondGrade <;> cases secondBound <;>
    first | rfl | exact Bool.noConfusion firstBelow | exact Bool.noConfusion secondBelow

/-- **The ordered-semiring law bundle (§6.1).**  A `Prop` predicate asserting that an
`OrderedGradeSemiring` satisfies every law of `(R, +, *, 0, 1, ≤)`: commutative monoid `(+, 0)`,
monoid `(*, 1)`, distributivity, annihilation, and a partial order `≤` compatible with both
operations.  This is the VERIFIED-semiring statement: an inhabitant proves the data bundle is a
genuine ordered semiring, not just a tuple of operations.  Note `mul_comm` is deliberately ABSENT
— §6.1 makes `*` a monoid (sequential use), not necessarily commutative; the commutativity of FX's
usage `*` is a stronger per-instance fact (`UsageGrade.mul_comm`). -/
structure IsLawfulOrderedGradeSemiring (semiring : OrderedGradeSemiring) : Prop where
  add_comm : ∀ firstGrade secondGrade : semiring.Carrier,
    semiring.add firstGrade secondGrade = semiring.add secondGrade firstGrade
  add_assoc : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.add (semiring.add firstGrade secondGrade) thirdGrade =
      semiring.add firstGrade (semiring.add secondGrade thirdGrade)
  add_zero : ∀ someGrade : semiring.Carrier, semiring.add someGrade semiring.zero = someGrade
  zero_add : ∀ someGrade : semiring.Carrier, semiring.add semiring.zero someGrade = someGrade
  mul_assoc : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.mul (semiring.mul firstGrade secondGrade) thirdGrade =
      semiring.mul firstGrade (semiring.mul secondGrade thirdGrade)
  mul_one : ∀ someGrade : semiring.Carrier, semiring.mul someGrade semiring.one = someGrade
  one_mul : ∀ someGrade : semiring.Carrier, semiring.mul semiring.one someGrade = someGrade
  mul_zero : ∀ someGrade : semiring.Carrier, semiring.mul someGrade semiring.zero = semiring.zero
  zero_mul : ∀ someGrade : semiring.Carrier, semiring.mul semiring.zero someGrade = semiring.zero
  left_distrib : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.mul firstGrade (semiring.add secondGrade thirdGrade) =
      semiring.add (semiring.mul firstGrade secondGrade) (semiring.mul firstGrade thirdGrade)
  right_distrib : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.mul (semiring.add firstGrade secondGrade) thirdGrade =
      semiring.add (semiring.mul firstGrade thirdGrade) (semiring.mul secondGrade thirdGrade)
  le_refl : ∀ someGrade : semiring.Carrier, semiring.le someGrade someGrade = true
  le_trans : ∀ firstGrade secondGrade thirdGrade : semiring.Carrier,
    semiring.le firstGrade secondGrade = true → semiring.le secondGrade thirdGrade = true →
      semiring.le firstGrade thirdGrade = true
  le_antisymm : ∀ firstGrade secondGrade : semiring.Carrier,
    semiring.le firstGrade secondGrade = true → semiring.le secondGrade firstGrade = true →
      firstGrade = secondGrade
  add_le_add_left : ∀ scaleGrade firstGrade secondGrade : semiring.Carrier,
    semiring.le firstGrade secondGrade = true →
      semiring.le (semiring.add scaleGrade firstGrade) (semiring.add scaleGrade secondGrade) = true
  mul_le_mul_left : ∀ scaleGrade firstGrade secondGrade : semiring.Carrier,
    semiring.le firstGrade secondGrade = true →
      semiring.le (semiring.mul scaleGrade firstGrade) (semiring.mul scaleGrade secondGrade) = true

/-- **The FX usage grade algebra `{0, 1, ω}` is a verified ordered semiring.**  Assembles every
ordered-semiring law (§6.1) into one inhabitant of `IsLawfulOrderedGradeSemiring fxUsageSemiring`.
This is the non-vacuous DIM2-1 deliverable: `fxUsageSemiring` is not merely a bundle of operations
but a PROVEN ordered semiring — the algebraic substrate the usage dimension's grade-checking
judgment (DIM2-3, the Wood/Atkey Lam rule) will consume. -/
theorem fxUsageSemiring_isLawful : IsLawfulOrderedGradeSemiring fxUsageSemiring where
  add_comm := UsageGrade.add_comm
  add_assoc := UsageGrade.add_assoc
  add_zero := UsageGrade.add_zero
  zero_add := UsageGrade.zero_add
  mul_assoc := UsageGrade.mul_assoc
  mul_one := UsageGrade.mul_one
  one_mul := UsageGrade.one_mul
  mul_zero := UsageGrade.mul_zero
  zero_mul := UsageGrade.zero_mul
  left_distrib := UsageGrade.left_distrib
  right_distrib := UsageGrade.right_distrib
  le_refl := UsageGrade.le_refl
  le_trans := fun _ _ _ firstBelowSecond secondBelowThird =>
    UsageGrade.le_trans firstBelowSecond secondBelowThird
  le_antisymm := fun _ _ firstBelowSecond secondBelowFirst =>
    UsageGrade.le_antisymm firstBelowSecond secondBelowFirst
  add_le_add_left := fun scaleGrade _ _ firstBelowSecond =>
    UsageGrade.add_le_add_left scaleGrade firstBelowSecond
  mul_le_mul_left := fun scaleGrade _ _ firstBelowSecond =>
    UsageGrade.mul_le_mul_left scaleGrade firstBelowSecond

/-! ## The security grade algebra `{unclassified < classified}` is a verified ordered semiring (DIM5-1, §6.1/§6.3)

The Security dimension (dim 5) is the SECOND graded instance of the §6.1 ordered semiring, after the
usage dimension `{0, 1, ω}`.  Its carrier is the two-point lattice `unclassified < classified`:
`+` is the JOIN (combining secrecy — any classified input poisons the result, the noninterference
combine rule), `*` is the MEET (`SecurityGrade.mul`, sequential composition with annihilation
`classified * unclassified = unclassified`, the §6.3 "ghost computation on a secret leaks nothing"
fact).  `zero = unclassified` is simultaneously the join bottom and the meet annihilator; `one =
classified` is the meet top.

Because `{unclassified < classified}` is a two-element chain it is a DISTRIBUTIVE lattice, so meet
distributes over join — the law that makes `(add, mul)` a genuine semiring rather than two unrelated
monoids.  Every law closes by full 2×2(×2) case enumeration (`cases … <;> rfl` for the equational
laws; `cases … <;> first | rfl | Bool.noConfusion …` for the order laws), propext-free and zero-axiom,
exactly as the usage twin.  This is the non-vacuous DIM5-1 deliverable: a SECOND dimension shown to be
a lawful ordered semiring with NO change to the type metatheory — the orthogonal-composition thesis
(DIM2-7) extended past its first witness. -/

/-- Commutativity of security join (combining secrecy is order-independent). -/
theorem SecurityGrade.add_comm (firstGrade secondGrade : SecurityGrade) :
    SecurityGrade.add firstGrade secondGrade = SecurityGrade.add secondGrade firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- Associativity of security join — the commutative-monoid law `(R, +, 0)`. -/
theorem SecurityGrade.add_assoc (firstGrade secondGrade thirdGrade : SecurityGrade) :
    SecurityGrade.add (SecurityGrade.add firstGrade secondGrade) thirdGrade =
      SecurityGrade.add firstGrade (SecurityGrade.add secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- `unclassified` is the join bottom (right identity). -/
theorem SecurityGrade.add_zero (someGrade : SecurityGrade) :
    SecurityGrade.add someGrade .unclassified = someGrade := by cases someGrade <;> rfl

/-- `unclassified` is the join bottom (left identity). -/
theorem SecurityGrade.zero_add (someGrade : SecurityGrade) :
    SecurityGrade.add .unclassified someGrade = someGrade := by cases someGrade <;> rfl

/-- Associativity of security meet — the monoid law `(R, *, 1)`. -/
theorem SecurityGrade.mul_assoc (firstGrade secondGrade thirdGrade : SecurityGrade) :
    SecurityGrade.mul (SecurityGrade.mul firstGrade secondGrade) thirdGrade =
      SecurityGrade.mul firstGrade (SecurityGrade.mul secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- `classified` is the meet top (right identity). -/
theorem SecurityGrade.mul_one (someGrade : SecurityGrade) :
    SecurityGrade.mul someGrade .classified = someGrade := by cases someGrade <;> rfl

/-- `classified` is the meet top (left identity). -/
theorem SecurityGrade.one_mul (someGrade : SecurityGrade) :
    SecurityGrade.mul .classified someGrade = someGrade := by cases someGrade <;> rfl

/-- **Annihilation `a * unclassified = unclassified`** (§6.3: ghost computation on a secret leaks
nothing — `classified * 0 = 0`).  `unclassified` is the meet bottom, so it absorbs under `*`. -/
theorem SecurityGrade.mul_zero (someGrade : SecurityGrade) :
    SecurityGrade.mul someGrade .unclassified = .unclassified := by cases someGrade <;> rfl

/-- Left annihilation `unclassified * a = unclassified`. -/
theorem SecurityGrade.zero_mul (someGrade : SecurityGrade) :
    SecurityGrade.mul .unclassified someGrade = .unclassified := by cases someGrade <;> rfl

/-- Commutativity of security meet (sequential secrecy composition is order-independent).  Security
is a COMMUTATIVE semiring; §6.1 only requires `*` to be a monoid, so this is a bonus per-instance law
beyond the general bundle. -/
theorem SecurityGrade.mul_comm (firstGrade secondGrade : SecurityGrade) :
    SecurityGrade.mul firstGrade secondGrade = SecurityGrade.mul secondGrade firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

/-- Left distributivity `a * (b + c) = a * b + a * c` — meet over join in the distributive 2-chain.
Without it `fxSecuritySemiring` would be two unrelated monoids, not a semiring. -/
theorem SecurityGrade.left_distrib (firstGrade secondGrade thirdGrade : SecurityGrade) :
    SecurityGrade.mul firstGrade (SecurityGrade.add secondGrade thirdGrade) =
      SecurityGrade.add (SecurityGrade.mul firstGrade secondGrade)
        (SecurityGrade.mul firstGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- Right distributivity `(a + b) * c = a * c + b * c`. -/
theorem SecurityGrade.right_distrib (firstGrade secondGrade thirdGrade : SecurityGrade) :
    SecurityGrade.mul (SecurityGrade.add firstGrade secondGrade) thirdGrade =
      SecurityGrade.add (SecurityGrade.mul firstGrade thirdGrade)
        (SecurityGrade.mul secondGrade thirdGrade) := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;> rfl

/-- Reflexivity of the security order `unclassified ≤ classified`. -/
theorem SecurityGrade.le_refl (someGrade : SecurityGrade) :
    SecurityGrade.le someGrade someGrade = true := by cases someGrade <;> rfl

/-- Transitivity of the security order. -/
theorem SecurityGrade.le_trans {firstGrade secondGrade thirdGrade : SecurityGrade}
    (firstBelowSecond : SecurityGrade.le firstGrade secondGrade = true)
    (secondBelowThird : SecurityGrade.le secondGrade thirdGrade = true) :
    SecurityGrade.le firstGrade thirdGrade = true := by
  cases firstGrade <;> cases secondGrade <;> cases thirdGrade <;>
    first
      | rfl
      | exact Bool.noConfusion firstBelowSecond
      | exact Bool.noConfusion secondBelowThird

/-- Antisymmetry — the security order is a PARTIAL order. -/
theorem SecurityGrade.le_antisymm {firstGrade secondGrade : SecurityGrade}
    (firstBelowSecond : SecurityGrade.le firstGrade secondGrade = true)
    (secondBelowFirst : SecurityGrade.le secondGrade firstGrade = true) :
    firstGrade = secondGrade := by
  cases firstGrade <;> cases secondGrade <;>
    first
      | rfl
      | exact Bool.noConfusion firstBelowSecond
      | exact Bool.noConfusion secondBelowFirst

/-- Order compatibility with join: `b ≤ c → a + b ≤ a + c`. -/
theorem SecurityGrade.add_le_add_left {firstGrade secondGrade : SecurityGrade}
    (scaleGrade : SecurityGrade) (firstBelowSecond : SecurityGrade.le firstGrade secondGrade = true) :
    SecurityGrade.le (SecurityGrade.add scaleGrade firstGrade)
      (SecurityGrade.add scaleGrade secondGrade) = true := by
  cases scaleGrade <;> cases firstGrade <;> cases secondGrade <;>
    first | rfl | exact Bool.noConfusion firstBelowSecond

/-- Order compatibility with meet: `b ≤ c → a * b ≤ a * c`. -/
theorem SecurityGrade.mul_le_mul_left {firstGrade secondGrade : SecurityGrade}
    (scaleGrade : SecurityGrade) (firstBelowSecond : SecurityGrade.le firstGrade secondGrade = true) :
    SecurityGrade.le (SecurityGrade.mul scaleGrade firstGrade)
      (SecurityGrade.mul scaleGrade secondGrade) = true := by
  cases scaleGrade <;> cases firstGrade <;> cases secondGrade <;>
    first | rfl | exact Bool.noConfusion firstBelowSecond

/-- **The noninterference combine fact: `classified + a = classified`** (§12.2).  A classified grade
poisons the join — mixing secret with anything yields secret, so an unclassified output can never
depend on a classified input without an explicit `declassify`.  The grade-level core of the
information-flow discipline (the security analogue of usage's `one_div_omega` Atkey-correction fact). -/
theorem SecurityGrade.classified_poisons_add (someGrade : SecurityGrade) :
    SecurityGrade.add .classified someGrade = .classified := by cases someGrade <;> rfl

/-- **The FX security grade algebra `{unclassified < classified}` is a verified ordered semiring.**
Assembles every §6.1 ordered-semiring law into one inhabitant of
`IsLawfulOrderedGradeSemiring fxSecuritySemiring`, with `mul = SecurityGrade.mul` (the MEET).  This is
DIM5-1: the second graded dimension proven a genuine ordered semiring — `mul_comm` is again ABSENT
from the bundle (`*` need only be a monoid; the security `*` commutativity is the stronger
per-instance `SecurityGrade.mul_comm`). -/
theorem fxSecuritySemiring_isLawful : IsLawfulOrderedGradeSemiring fxSecuritySemiring where
  add_comm := SecurityGrade.add_comm
  add_assoc := SecurityGrade.add_assoc
  add_zero := SecurityGrade.add_zero
  zero_add := SecurityGrade.zero_add
  mul_assoc := SecurityGrade.mul_assoc
  mul_one := SecurityGrade.mul_one
  one_mul := SecurityGrade.one_mul
  mul_zero := SecurityGrade.mul_zero
  zero_mul := SecurityGrade.zero_mul
  left_distrib := SecurityGrade.left_distrib
  right_distrib := SecurityGrade.right_distrib
  le_refl := SecurityGrade.le_refl
  le_trans := fun _ _ _ firstBelowSecond secondBelowThird =>
    SecurityGrade.le_trans firstBelowSecond secondBelowThird
  le_antisymm := fun _ _ firstBelowSecond secondBelowFirst =>
    SecurityGrade.le_antisymm firstBelowSecond secondBelowFirst
  add_le_add_left := fun scaleGrade _ _ firstBelowSecond =>
    SecurityGrade.add_le_add_left scaleGrade firstBelowSecond
  mul_le_mul_left := fun scaleGrade _ _ firstBelowSecond =>
    SecurityGrade.mul_le_mul_left scaleGrade firstBelowSecond

/-! ## Grade division — the residual of multiplication (toward DIM2-3's corrected Lam rule)

`div a b = max { d : d * b ≤ a }` is the residual (right adjoint) of `* b` — the largest grade
whose product with `b` stays below `a`.  Context division `G / p` (§6.2) divides each binding's
grade by a closure's replication grade `p`; the defining fact `1 / ω = 0` is the Wood/Atkey 2022
correction (§27.1) that erases a linear variable from a replicable closure, blocking the broken
Atkey-2018 Lam rule.  `div_residuation` proves the 3×3 table IS the genuine residual (the universal
property both ways); `mul_div_le` is the counit — scaling the divided context back up stays below
the original. -/

/-- Grade division `div a b = max { d : d * b ≤ a }` — the residual of `* b`.  Full 3×3
enumeration; propext-free. -/
def UsageGrade.div : UsageGrade → UsageGrade → UsageGrade
  | .zero,  .zero  => .omega
  | .one,   .zero  => .omega
  | .omega, .zero  => .omega
  | .zero,  .one   => .zero
  | .one,   .one   => .one
  | .omega, .one   => .omega
  | .zero,  .omega => .zero
  | .one,   .omega => .zero
  | .omega, .omega => .omega

/-- **Residuation: `d * b ≤ a ↔ d ≤ a / b`.**  Division is the right adjoint of multiplication —
the defining universal property that makes the 3×3 table the genuine residual (not an ad-hoc
inverse).  Closes by `Iff.rfl` per case: both sides reduce to the same concrete `Bool` equality. -/
theorem UsageGrade.div_residuation (dividendGrade divisorGrade quotientCandidate : UsageGrade) :
    (UsageGrade.le (UsageGrade.mul quotientCandidate divisorGrade) dividendGrade = true) ↔
      (UsageGrade.le quotientCandidate (UsageGrade.div dividendGrade divisorGrade) = true) := by
  cases dividendGrade <;> cases divisorGrade <;> cases quotientCandidate <;> exact Iff.rfl

/-- **The Wood/Atkey 2022 correction: `1 / ω = 0`** (§27.1).  A linear variable (grade `1`) divided
by a replicable closure's `ω` erases to `0` — so the corrected Lam rule cannot capture a linear
variable in an unrestricted closure (the broken Atkey-2018 rule allowed exactly this). -/
theorem UsageGrade.one_div_omega :
    UsageGrade.div UsageGrade.one UsageGrade.omega = UsageGrade.zero := rfl

/-- Division by the unit is the identity: `a / 1 = a`. -/
theorem UsageGrade.div_one (someGrade : UsageGrade) :
    UsageGrade.div someGrade UsageGrade.one = someGrade := by
  cases someGrade <;> rfl

/-- Counit / soundness: `b * (a / b) ≤ a` — scaling the divided grade back up (scalar `b` on the
left, matching `GradeVector.scale`) never exceeds the original.  The fact the corrected Lam rule
relies on for soundness; the `←` direction of `div_residuation` at the reflexive quotient. -/
theorem UsageGrade.mul_div_le (divisorGrade dividendGrade : UsageGrade) :
    UsageGrade.le (UsageGrade.mul divisorGrade (UsageGrade.div dividendGrade divisorGrade))
      dividendGrade = true := by
  cases divisorGrade <;> cases dividendGrade <;> rfl

/-! ## Security-instance multiplication: RESOLVED (DIM5-1)

The earlier `fxSecuritySemiring.mul := SecurityGrade.add` (JOIN) miswiring — which made the instance
fail `one_mul` and annihilation, so `IsLawfulOrderedGradeSemiring fxSecuritySemiring` was unprovable —
is now fixed: `mul := SecurityGrade.mul` (the MEET, §6.1/§6.3) with the complete law set and the
`fxSecuritySemiring_isLawful` witness shipped in the security-grade-algebra section above. -/

end FX1Poly.Modal
