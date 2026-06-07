import FX1Poly.Modal.ResourceGraded
import FX1Poly.Modal.GradeErasureGeneric

/-! # FX1Poly/Modal/ComplexitySemiring
    — the THIRD graded dimension: the complexity / space N-semiring over the generic `HasGradeOver` engine
      (orthogonal-composition thesis at a structurally-distinct, UNBOUNDED, non-idempotent semiring)

The usage dimension `{0, 1, ω}` (DIM2) and the security dimension `{unclassified < classified}` (DIM5) are
the first two instances of the §6.1 ordered grade semiring, both FINITE lattices with IDEMPOTENT addition.
The §6.3 complexity dimension (dim 13: `cost(f) + cost(g)` combined) and the space dimension (dim 15:
allocation tracking) are the natural-number semiring `(Nat, +, *, 0, 1, ≤)` — UNBOUNDED, with NON-idempotent
addition (`1 + 1 = 2 ≠ 1`).  Adding it is the sharpest test of the orthogonal-composition thesis: if the
generic `HasGradeOver R` engine is truly dimension-agnostic, an unbounded standard `Nat` semiring drops in and
strong normalization transfers with NO per-dimension proof — even though `Nat` differs structurally from the
two finite lattices the engine has seen.

  * `fxComplexitySemiring : OrderedGradeSemiring` — the `Nat` instance (`+`, `*`, `Nat.ble`, `DecidableEq`).
  * `fxComplexitySemiring_isLawful` — the full §6.1 ordered-semiring law bundle, ZERO-AXIOM.
  * `complexityLinearIdentity_typed` / `…_stronglyNormalizingViaGeneric` — the identity, typed in the
    complexity dimension and shown β-SN through the SHARED generic transfer
    (`linearIdentityOver_stronglyNormalizing`), no complexity-specific SN proof.
  * `complexityAddNotIdempotent` — `1 + 1 ≠ 1` in this semiring: it is genuinely a NEW semiring shape (the
    usage `ω + ω = ω` and security `classified + classified = classified` idempotence both fail here), not a
    relabeling of a finite lattice.

## Zero-axiom note (the Nat propext trap)

The stdlib `Nat.mul_assoc` and `Nat.right_distrib` (the `add_mul` flavor) DEPEND ON `propext`, so the lawful
bundle cannot cite them directly.  This file hand-rolls axiom-clean replacements: `natMulComm` (induction on
the 2nd factor via `mul_succ`/`succ_mul`), `natMulAssoc` (induction on the 3rd factor via the CLEAN
`Nat.left_distrib`), and `natRightDistrib` (via `natMulComm` + `Nat.left_distrib`).  `Nat.add_comm`,
`Nat.add_assoc`, `Nat.left_distrib`, and every `Nat.ble`/`Nat.le` order lemma used ARE axiom-clean.

## Composition-ledger payoff

The thesis: adding the complexity/space dimension cost a NEW SEMIRING INSTANCE plus its lawfulness, and NOTHING
ELSE — no change to the type metatheory, no SN re-proof.  `complexityLinearIdentity_stronglyNormalizingViaGeneric`
is the proof: it is `linearIdentityOver_stronglyNormalizing fxComplexitySemiring`, the generic transfer fired at
the third dimension.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-! ## Axiom-clean Nat arithmetic (the lawful-bundle substrate) -/

/-- `Nat.ble` reflexivity, hand-rolled (structural recursion, no propext). -/
theorem natBle_self : ∀ someGrade : Nat, Nat.ble someGrade someGrade = true
  | 0 => rfl
  | successorGrade + 1 => natBle_self successorGrade

/-- Multiplication commutes, hand-rolled by induction on the second factor (`mul_succ`/`succ_mul`), dodging
the propext-leaking `Nat.mul_comm`. -/
theorem natMulComm : ∀ firstGrade secondGrade : Nat, firstGrade * secondGrade = secondGrade * firstGrade
  | _, 0 => by rw [Nat.mul_zero, Nat.zero_mul]
  | firstGrade, secondGrade + 1 => by
      rw [Nat.mul_succ, natMulComm firstGrade secondGrade, Nat.succ_mul]

/-- Multiplication associates, hand-rolled by induction on the third factor via the CLEAN `Nat.left_distrib`,
dodging the propext-leaking `Nat.mul_assoc`. -/
theorem natMulAssoc : ∀ firstGrade secondGrade thirdGrade : Nat,
    firstGrade * secondGrade * thirdGrade = firstGrade * (secondGrade * thirdGrade)
  | _, _, 0 => by rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | firstGrade, secondGrade, thirdGrade + 1 => by
      rw [Nat.mul_succ, Nat.mul_succ, natMulAssoc firstGrade secondGrade thirdGrade, Nat.left_distrib]

/-- Right distributivity, hand-rolled via `natMulComm` + the CLEAN `Nat.left_distrib`, dodging the
propext-leaking `Nat.right_distrib`. -/
theorem natRightDistrib (firstGrade secondGrade thirdGrade : Nat) :
    (firstGrade + secondGrade) * thirdGrade = firstGrade * thirdGrade + secondGrade * thirdGrade := by
  rw [natMulComm (firstGrade + secondGrade) thirdGrade, Nat.left_distrib,
    natMulComm thirdGrade firstGrade, natMulComm thirdGrade secondGrade]

/-! ## The complexity / space N-semiring -/

/-- **The complexity / space dimension's N-semiring** (§6.3 dim 13 / dim 15): carrier `Nat`, `add = Nat.add`
(combining cost — NON-idempotent), `mul = Nat.mul` (scaling cost by a parameter grade), `zero = 0` (free),
`one = 1`, `le = Nat.ble`.  The third instance of the §6.1 ordered grade semiring, and the first UNBOUNDED
one. -/
def fxComplexitySemiring : OrderedGradeSemiring where
  Carrier := Nat
  zero := 0
  one := 1
  add := Nat.add
  mul := Nat.mul
  le := Nat.ble
  carrierDecEq := instDecidableEqNat

/-- **The complexity / space N-semiring is a verified ordered semiring** (§6.1).  The third lawful instance
after usage `{0, 1, ω}` and security `{unclassified < classified}` — and the first UNBOUNDED one, so the
`mul`-associativity and right-distributivity laws are the hand-rolled axiom-clean `natMulAssoc` /
`natRightDistrib` (the stdlib `Nat.mul_assoc` / `Nat.right_distrib` leak propext).  Non-vacuous: `Nat` is a
genuine ordered semiring, the algebraic substrate the complexity/space dimension's grade checking consumes. -/
theorem fxComplexitySemiring_isLawful : IsLawfulOrderedGradeSemiring fxComplexitySemiring where
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  mul_assoc := natMulAssoc
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  mul_zero := Nat.mul_zero
  zero_mul := Nat.zero_mul
  left_distrib := Nat.left_distrib
  right_distrib := natRightDistrib
  le_refl := natBle_self
  le_trans := fun _ _ _ firstBelowSecond secondBelowThird =>
    Nat.ble_eq_true_of_le
      (Nat.le_trans (Nat.le_of_ble_eq_true firstBelowSecond) (Nat.le_of_ble_eq_true secondBelowThird))
  le_antisymm := fun _ _ firstBelowSecond secondBelowFirst =>
    Nat.le_antisymm (Nat.le_of_ble_eq_true firstBelowSecond) (Nat.le_of_ble_eq_true secondBelowFirst)
  add_le_add_left := fun scaleGrade _ _ firstBelowSecond =>
    Nat.ble_eq_true_of_le (Nat.add_le_add_left (Nat.le_of_ble_eq_true firstBelowSecond) scaleGrade)
  mul_le_mul_left := fun scaleGrade _ _ firstBelowSecond =>
    Nat.ble_eq_true_of_le (Nat.mul_le_mul_left scaleGrade (Nat.le_of_ble_eq_true firstBelowSecond))

/-! ## The structural distinctiveness — non-idempotent addition -/

/-- **The complexity semiring's addition is NON-idempotent** (`1 + 1 ≠ 1`).  Both prior dimensions have
idempotent `+` (usage `ω + ω = ω`, security `classified + classified = classified`); the N-semiring does not,
so it is a genuinely NEW semiring shape — the orthogonal-composition thesis tested past the finite lattices. -/
theorem complexityAddNotIdempotent :
    fxComplexitySemiring.add fxComplexitySemiring.one fxComplexitySemiring.one ≠ fxComplexitySemiring.one := by
  show (2 : Nat) ≠ 1
  decide

/-! ## The orthogonal-composition payoff — SN transfers to the third dimension for free -/

/-- The linear identity, TYPED in the complexity dimension — the generic engine accepts the third dimension
with no new typing rule (`linearIdentityOver_typed` instantiated at `fxComplexitySemiring`). -/
def complexityLinearIdentity_typed :=
  linearIdentityOver_typed fxComplexitySemiring

/-- **The complexity dimension's identity is β-SN via the SHARED transfer** — `linearIdentityOver_stronglyNormalizing`
fired at `fxComplexitySemiring`, with NO complexity-specific SN proof.  The orthogonal-composition thesis at a
THIRD dimension: SN survives grade erasure regardless of which semiring `R` is, because the term and its
β-reduction are grade-agnostic.  Adding the complexity/space dimension cost the lawful semiring instance above
and NOTHING in the metatheory. -/
theorem complexityLinearIdentity_stronglyNormalizingViaGeneric :
    GradedLambda.IsStronglyNormalizing (.lam (.var 0)) :=
  linearIdentityOver_stronglyNormalizing fxComplexitySemiring

end FX1Poly.Modal
