import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeSemiring.CommutativeSemiringSeed
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # WalkingCommutativeRing/CommutativeRingSeed — the walking free COMMUTATIVE RING on ℕ: the polynomial ℤ[X] decision

The additive-inverse successor of the commutative-semiring rung (`CommutativeSemiringSeed`, whose free
commutative semiring on `ℕ` is the polynomial ring `ℕ[X]` with natural-number coefficients).  Adjoining a
formal additive inverse (a unary negation `negOp`) completes each coefficient's natural count to its group of
differences, so the free **commutative ring** on the colour set `ℕ` is the polynomial ring `ℤ[X_c : c ∈ ℕ]`
with INTEGER coefficients in commuting variables.  A tree's class is determined by its polynomial: the finite
formal `ℤ`-linear combination of monomials, where a monomial is a finite multiset of variables.  Because that
polynomial is a COMPLETE invariant with a canonical sorted representative, the word problem is DECIDED.

## ★ Integer coefficients as subtraction-free `(pos, neg)` ℕ-pairs

The KEY design decision — mirroring the ℤᵏ winding rung `ColourAbelianGroupSeed` — is to represent each integer
coefficient as a PAIR `(pos, neg) : ℕ × ℕ` denoting the difference `pos − neg`, but NEVER computed as a
subtraction.  `Int` and `Nat.sub` both LEAK `propext`; the pair representation stays entirely inside the clean
`Nat.add` / `Nat.mul` kit.  The coefficient algebra:

* `fcrCoeffAdd (p1,n1) (p2,n2) := (p1+p2, n1+n2)` (componentwise `Nat.add`);
* `fcrCoeffMul (p1,n1) (p2,n2) := (p1*p2 + n1*n2, p1*n2 + n1*p2)` (the product of differences);
* `fcrCoeffNeg (p,n) := (n,p)` (swap);
* `fcrCoeffEq (p1,n1) (p2,n2) := Nat.beq (p1+n2) (p2+n1)` (the cross-add difference-equality);
* `fcrCoeffIsZero (p,n) := Nat.beq p n` (zero iff `pos = neg`).

The coefficient ring laws (add comm/assoc/zero/neg-inverse; mul comm/assoc/one/zero; distributivity) all hold
up to `fcrCoeffEq` and are discharged by `Nat.add`/`Nat.mul` clean lemmas plus the hand-proved structural
replacements `fcrNatMulAssoc` / `fcrNatAddMul` (the standard-library `Nat.mul_assoc` / `Nat.add_mul` LEAK
`propext`).

## ★ The normal form, operations, and the SUBTRACTION-FREE decision

`FcrNF := List (List Nat × (Nat × Nat))` — a list of `(monomial, coeffPair)` terms sorted strictly by the
imported monomial order `csrCompare` (length-first then lex).  The monomial machinery is the ℕ[X] sibling's,
imported and reused VERBATIM (`csrCompare`, `csrMonoMul`, `csrMonoSorted`, and the whole order kit).  The
operations mirror ℕ[X] with pair coefficients, and — the deliberate choice that keeps every merge/convolve
proof structurally IDENTICAL to ℕ[X] — they do **not** drop cancelling terms; a zero-valued coefficient is
carried as an ordinary term and only the DECISION reads it off.  `fcrNegate` negates every coefficient.

The decision is the SUBTRACTION-FREE polynomial equality: `fcrNFEq A B := fcrNFAllZero (fcrMergeAdd A
(fcrNegate B))` — two polynomials are equal exactly when their difference has every coefficient zero-valued.
This single-list structural check (no parallel walk, no fuel) is the coefficient-pair analogue of the winding
rung's cross-added multiset equality.  Its soundness/completeness rest on the `fcrEvalCross` semantic model (the
per-monomial coefficient sum), whose merge/negate homomorphisms make `fcrNFEq` a decidable equivalence and a
congruence; the crux `fcrMergeAdd_selfNeg` (a polynomial plus its own negation is all-zero-valued) falls out of
the model.

This file ships, all zero-axiom: the coefficient ring algebra; the pair-coefficient normal-form machinery
(`fcrInsertTerm` with the crux commutation `fcrInsertTermComm`, `fcrMergeAdd` associative/commutative/unit,
`fcrMulConvolve` with annihilation / distributivity / associativity / commutativity / unit — mirroring ℕ[X]);
`fcrNegate` with its merge/involution algebra; the `fcrEvalCross` model; `FcrTree` with `negOp`, `fcrNormalize`,
and `CommRingTreeConv` (the abelian additive group with `addNegInverse` + the commutative multiplicative
monoid + distributivity + `negCongr`); soundness (`fcrNormalize_respects`), completeness
(`fcrConv_of_normalizeEq` via the rebuild `fcrCombOfNF` and reification `fcrTreeReifies`), and THE DECISION
(`commRingTreeConv_iff_normalForm`, a genuine `Decidable` instance, and `#eval` groundings — including the
headline additive-inverse `x + neg x ≈ 0`).

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`,
`Int`, `Nat.sub`, `Nat.min`/`Nat.max`, `Nat.mul_assoc`/`Nat.add_mul`, `List.append` (`++`), and every
`Nat.le`/`Nat.ble` lemma — the ordering is the imported structural `natBle`, coefficient arithmetic uses only
the clean add/mul kit, and no coefficient is ever canonicalized by subtraction. -/

namespace FX1Poly.Polygraph

/-! ## The coefficient algebra: integers as subtraction-free `(pos, neg)` ℕ-pairs -/

/-- Clean structural replacement for the propext-leaky `Nat.mul_assoc`: `a * b * c = a * (b * c)`, built from
the clean `Nat.mul_succ` / `Nat.mul_add` / `Nat.mul_zero`.  (Reused shape of the ℕ[X] sibling's
`csrNatMulAssoc`, re-proved here under the `fcr` prefix so the audit twin gates it independently.) -/
theorem fcrNatMulAssoc : (a b c : Nat) → a * b * c = a * (b * c)
  | a, b, 0 => by rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | a, b, Nat.succ c => by
      rw [Nat.mul_succ, fcrNatMulAssoc a b c, Nat.mul_succ, Nat.mul_add]

/-- Clean structural replacement for the propext-leaky `Nat.add_mul`: `(a + b) * c = a * c + b * c`, via
`Nat.mul_comm` / `Nat.mul_add`. -/
theorem fcrNatAddMul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

/-- Clean structural right-cancellation for `Nat.add`: `a + c = b + c → a = b` (structural recursion on the
cancelled summand `c`; the propext-clean tool the coefficient equivalence's difference reasoning needs). -/
theorem fcrNatAddRightCancel : (a b c : Nat) → a + c = b + c → a = b
  | a, b, 0, h => h
  | a, b, Nat.succ c, h => fcrNatAddRightCancel a b c (Nat.succ.inj h)

/-- The coefficient `add`: componentwise `Nat.add` of the two `(pos, neg)` pairs. -/
def fcrCoeffAdd : (Nat × Nat) → (Nat × Nat) → (Nat × Nat)
  | (p1, n1), (p2, n2) => (p1 + p2, n1 + n2)

/-- The coefficient `mul`: the product of differences `(p1 − n1)(p2 − n2) = (p1 p2 + n1 n2) − (p1 n2 + n1 p2)`,
all `Nat.add` / `Nat.mul`. -/
def fcrCoeffMul : (Nat × Nat) → (Nat × Nat) → (Nat × Nat)
  | (p1, n1), (p2, n2) => (p1 * p2 + n1 * n2, p1 * n2 + n1 * p2)

/-- The coefficient negation: SWAP the positive and inverse components. -/
def fcrCoeffNeg : (Nat × Nat) → (Nat × Nat)
  | (p, n) => (n, p)

/-- The coefficient CROSS-ADD equality `p1 + n2 = p2 + n1` (integer `p1 − n1 = p2 − n2` without subtraction),
via the core `Nat.beq`. -/
def fcrCoeffEq : (Nat × Nat) → (Nat × Nat) → Bool
  | (p1, n1), (p2, n2) => Nat.beq (p1 + n2) (p2 + n1)

/-- The coefficient is zero exactly when `pos = neg`, via `Nat.beq`. -/
def fcrCoeffIsZero : (Nat × Nat) → Bool
  | (p, n) => Nat.beq p n

/-! ### Coefficient `add` laws -/

theorem fcrCoeffAddComm (a b : Nat × Nat) : fcrCoeffAdd a b = fcrCoeffAdd b a := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  show (p1 + p2, n1 + n2) = (p2 + p1, n2 + n1)
  rw [Nat.add_comm p1 p2, Nat.add_comm n1 n2]

theorem fcrCoeffAddAssoc (a b c : Nat × Nat) :
    fcrCoeffAdd (fcrCoeffAdd a b) c = fcrCoeffAdd a (fcrCoeffAdd b c) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b; obtain ⟨p3, n3⟩ := c
  show (p1 + p2 + p3, n1 + n2 + n3) = (p1 + (p2 + p3), n1 + (n2 + n3))
  rw [Nat.add_assoc p1 p2 p3, Nat.add_assoc n1 n2 n3]

theorem fcrCoeffAddZeroRight (a : Nat × Nat) : fcrCoeffAdd a (0, 0) = a := by
  obtain ⟨p, n⟩ := a
  show (p + 0, n + 0) = (p, n)
  rw [Nat.add_zero, Nat.add_zero]

theorem fcrCoeffAddZeroLeft (a : Nat × Nat) : fcrCoeffAdd (0, 0) a = a := by
  rw [fcrCoeffAddComm]; exact fcrCoeffAddZeroRight a

/-- Coefficient negation distributes over addition: `neg (a + b) = neg a + neg b` (holds LITERALLY, since the
swap commutes with componentwise add). -/
theorem fcrCoeffNegAdd (a b : Nat × Nat) :
    fcrCoeffNeg (fcrCoeffAdd a b) = fcrCoeffAdd (fcrCoeffNeg a) (fcrCoeffNeg b) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  rfl

/-- Coefficient negation is involutive: `neg (neg a) = a`. -/
theorem fcrCoeffNegNeg (a : Nat × Nat) : fcrCoeffNeg (fcrCoeffNeg a) = a := by
  obtain ⟨p, n⟩ := a; rfl

/-! ### Zero-valued coefficient facts -/

/-- A coefficient plus its own negation is zero-valued: `isZero (a + neg a) = true`. -/
theorem fcrCoeffAddNegIsZero (a : Nat × Nat) : fcrCoeffIsZero (fcrCoeffAdd a (fcrCoeffNeg a)) = true := by
  obtain ⟨p, n⟩ := a
  show Nat.beq (p + n) (n + p) = true
  rw [Nat.add_comm p n]; exact csrNatBeqRefl (n + p)

/-- The sum of two zero-valued coefficients is zero-valued. -/
theorem fcrCoeffAddZeroValued (a b : Nat × Nat)
    (ha : fcrCoeffIsZero a = true) (hb : fcrCoeffIsZero b = true) :
    fcrCoeffIsZero (fcrCoeffAdd a b) = true := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  have h1 : p1 = n1 := csrNatEqOfBeq p1 n1 ha
  have h2 : p2 = n2 := csrNatEqOfBeq p2 n2 hb
  show Nat.beq (p1 + p2) (n1 + n2) = true
  rw [h1, h2]; exact csrNatBeqRefl (n1 + n2)

/-- `neg` preserves zero-valuedness (`isZero (neg a) = isZero a`). -/
theorem fcrCoeffNegIsZero (a : Nat × Nat) : fcrCoeffIsZero (fcrCoeffNeg a) = fcrCoeffIsZero a := by
  obtain ⟨p, n⟩ := a
  show Nat.beq n p = Nat.beq p n
  exact csrNatBeqSymm n p

/-- If a sum and one summand are zero-valued, so is the other summand (integer cancellation, subtraction-free
via `fcrNatAddRightCancel`). -/
theorem fcrCoeffAddCancelZero (a b : Nat × Nat)
    (hsum : fcrCoeffIsZero (fcrCoeffAdd a b) = true) (hb : fcrCoeffIsZero b = true) :
    fcrCoeffIsZero a = true := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  have hbb : p2 = n2 := csrNatEqOfBeq p2 n2 hb
  have hs : p1 + p2 = n1 + n2 := csrNatEqOfBeq (p1 + p2) (n1 + n2) hsum
  rw [hbb] at hs
  have hp1n1 : p1 = n1 := fcrNatAddRightCancel p1 n1 n2 hs
  show Nat.beq p1 n1 = true
  rw [hp1n1]; exact csrNatBeqRefl n1

/-! ### Nat add-reordering helpers (clean `Nat.add_assoc` / `Nat.add_comm` only) -/

/-- The middle-four exchange for `Nat.add`: `(a + b) + (c + d) = (a + c) + (b + d)`. -/
theorem fcrNatAddMiddleFour (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d, Nat.add_comm b c, Nat.add_assoc c b d,
      ← Nat.add_assoc a c (b + d)]

/-! ### Coefficient `mul` laws -/

theorem fcrCoeffMulComm (a b : Nat × Nat) : fcrCoeffMul a b = fcrCoeffMul b a := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  show (p1 * p2 + n1 * n2, p1 * n2 + n1 * p2) = (p2 * p1 + n2 * n1, p2 * n1 + n2 * p1)
  rw [Nat.mul_comm p1 p2, Nat.mul_comm n1 n2, Nat.mul_comm p1 n2, Nat.mul_comm n1 p2,
      Nat.add_comm (n2 * p1) (p2 * n1)]

theorem fcrCoeffMulOne (a : Nat × Nat) : fcrCoeffMul a (1, 0) = a := by
  obtain ⟨p, n⟩ := a
  show (p * 1 + n * 0, p * 0 + n * 1) = (p, n)
  rw [Nat.mul_one p, Nat.mul_zero n, Nat.add_zero, Nat.mul_zero p, Nat.mul_one n, Nat.zero_add]

theorem fcrCoeffMulZeroRight (a : Nat × Nat) : fcrCoeffMul a (0, 0) = (0, 0) := by
  obtain ⟨p, n⟩ := a
  show (p * 0 + n * 0, p * 0 + n * 0) = (0, 0)
  rw [Nat.mul_zero p, Nat.mul_zero n, Nat.add_zero]

/-- Coefficient left-distributivity `a * (b + c) = a * b + a * c` (the pair analogue of `Nat.mul_add`). -/
theorem fcrCoeffMulAddRight (a b c : Nat × Nat) :
    fcrCoeffMul a (fcrCoeffAdd b c) = fcrCoeffAdd (fcrCoeffMul a b) (fcrCoeffMul a c) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b; obtain ⟨p3, n3⟩ := c
  show (p1 * (p2 + p3) + n1 * (n2 + n3), p1 * (n2 + n3) + n1 * (p2 + p3))
      = (p1 * p2 + n1 * n2 + (p1 * p3 + n1 * n3), p1 * n2 + n1 * p2 + (p1 * n3 + n1 * p3))
  rw [Nat.mul_add p1 p2 p3, Nat.mul_add n1 n2 n3, Nat.mul_add p1 n2 n3, Nat.mul_add n1 p2 p3,
      fcrNatAddMiddleFour (p1 * p2) (p1 * p3) (n1 * n2) (n1 * n3),
      fcrNatAddMiddleFour (p1 * n2) (p1 * n3) (n1 * p2) (n1 * p3)]

/-- Coefficient right-distributivity `(a + b) * c = a * c + b * c` (the pair analogue of `fcrNatAddMul`). -/
theorem fcrCoeffAddMulRight (a b c : Nat × Nat) :
    fcrCoeffMul (fcrCoeffAdd a b) c = fcrCoeffAdd (fcrCoeffMul a c) (fcrCoeffMul b c) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b; obtain ⟨p3, n3⟩ := c
  show ((p1 + p2) * p3 + (n1 + n2) * n3, (p1 + p2) * n3 + (n1 + n2) * p3)
      = (p1 * p3 + n1 * n3 + (p2 * p3 + n2 * n3), p1 * n3 + n1 * p3 + (p2 * n3 + n2 * p3))
  rw [fcrNatAddMul p1 p2 p3, fcrNatAddMul n1 n2 n3, fcrNatAddMul p1 p2 n3, fcrNatAddMul n1 n2 p3,
      fcrNatAddMiddleFour (p1 * p3) (p2 * p3) (n1 * n3) (n2 * n3),
      fcrNatAddMiddleFour (p1 * n3) (p2 * n3) (n1 * p3) (n2 * p3)]

/-- Coefficient negation passes through multiplication on the left: `neg (a * b) = (neg a) * b`
(propositionally, via `Nat.add_comm`). -/
theorem fcrCoeffNegMulLeft (a b : Nat × Nat) :
    fcrCoeffNeg (fcrCoeffMul a b) = fcrCoeffMul (fcrCoeffNeg a) b := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  show (p1 * n2 + n1 * p2, p1 * p2 + n1 * n2) = (n1 * p2 + p1 * n2, n1 * n2 + p1 * p2)
  rw [Nat.add_comm (p1 * n2) (n1 * p2), Nat.add_comm (p1 * p2) (n1 * n2)]

/-- ★ Coefficient multiplication is associative — the hardest coefficient law: both sides expand (via
`fcrNatAddMul` / `Nat.mul_add` / `fcrNatMulAssoc`) to the same four `Nat`-monomials, matched by the
`fcrNatAddMiddleFour` exchange plus one `Nat.add_comm`. -/
theorem fcrCoeffMulAssoc (a b c : Nat × Nat) :
    fcrCoeffMul (fcrCoeffMul a b) c = fcrCoeffMul a (fcrCoeffMul b c) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b; obtain ⟨p3, n3⟩ := c
  show ((p1 * p2 + n1 * n2) * p3 + (p1 * n2 + n1 * p2) * n3,
        (p1 * p2 + n1 * n2) * n3 + (p1 * n2 + n1 * p2) * p3)
      = (p1 * (p2 * p3 + n2 * n3) + n1 * (p2 * n3 + n2 * p3),
         p1 * (p2 * n3 + n2 * p3) + n1 * (p2 * p3 + n2 * n3))
  rw [fcrNatAddMul (p1 * p2) (n1 * n2) p3, fcrNatAddMul (p1 * n2) (n1 * p2) n3,
      fcrNatAddMul (p1 * p2) (n1 * n2) n3, fcrNatAddMul (p1 * n2) (n1 * p2) p3,
      Nat.mul_add p1 (p2 * p3) (n2 * n3), Nat.mul_add n1 (p2 * n3) (n2 * p3),
      Nat.mul_add p1 (p2 * n3) (n2 * p3), Nat.mul_add n1 (p2 * p3) (n2 * n3),
      fcrNatMulAssoc p1 p2 p3, fcrNatMulAssoc n1 n2 p3, fcrNatMulAssoc p1 n2 n3, fcrNatMulAssoc n1 p2 n3,
      fcrNatMulAssoc p1 p2 n3, fcrNatMulAssoc n1 n2 n3, fcrNatMulAssoc p1 n2 p3, fcrNatMulAssoc n1 p2 p3,
      fcrNatAddMiddleFour (p1 * (p2 * p3)) (n1 * (n2 * p3)) (p1 * (n2 * n3)) (n1 * (p2 * n3)),
      Nat.add_comm (n1 * (n2 * p3)) (n1 * (p2 * n3)),
      fcrNatAddMiddleFour (p1 * (p2 * n3)) (n1 * (n2 * n3)) (p1 * (n2 * p3)) (n1 * (p2 * p3)),
      Nat.add_comm (n1 * (n2 * n3)) (n1 * (p2 * p3))]

/-! ### Coefficient cross-add equality is an equivalence -/

theorem fcrCoeffEqRefl (a : Nat × Nat) : fcrCoeffEq a a = true := by
  obtain ⟨p, n⟩ := a
  show Nat.beq (p + n) (p + n) = true
  exact csrNatBeqRefl (p + n)

theorem fcrCoeffEqSymm (a b : Nat × Nat) (h : fcrCoeffEq a b = true) : fcrCoeffEq b a = true := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  have he : p1 + n2 = p2 + n1 := csrNatEqOfBeq (p1 + n2) (p2 + n1) h
  show Nat.beq (p2 + n1) (p1 + n2) = true
  rw [he]; exact csrNatBeqRefl (p2 + n1)

/-! ## The pair-coefficient normal form and its additive engine (mirroring ℕ[X], no zero-drop) -/

/-- The normal form: a list of `(monomial, coeffPair)` terms, sorted strictly by the imported monomial order
`csrCompare`.  A zero-valued coefficient is carried as an ordinary term (the operations never drop). -/
abbrev FcrNF := List (List Nat × (Nat × Nat))

/-- Insert one term into a sorted normal form, ADDING coefficients on an equal monomial (never dropping). -/
def fcrInsertTerm : (List Nat × (Nat × Nat)) → FcrNF → FcrNF
  | term, [] => [term]
  | (m, c), (p, e) :: rest =>
      match csrCompare m p with
      | CsrMonoOrd.eq => (p, fcrCoeffAdd e c) :: rest
      | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
      | CsrMonoOrd.gt => (p, e) :: fcrInsertTerm (m, c) rest
theorem fcrInsertTermNil (m : List Nat) (c : Nat × Nat) : fcrInsertTerm (m, c) [] = [(m, c)] := rfl
theorem fcrInsertTermEqE (m : List Nat) (c : Nat × Nat) (p : List Nat) (e : Nat × Nat) (rest : FcrNF)
    (h : csrCompare m p = CsrMonoOrd.eq) :
    fcrInsertTerm (m, c) ((p, e) :: rest) = (p, fcrCoeffAdd e c) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, fcrCoeffAdd e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: fcrInsertTerm (m, c) rest) = (p, fcrCoeffAdd e c) :: rest
  rw [h]
theorem fcrInsertTermLtE (m : List Nat) (c : Nat × Nat) (p : List Nat) (e : Nat × Nat) (rest : FcrNF)
    (h : csrCompare m p = CsrMonoOrd.lt) :
    fcrInsertTerm (m, c) ((p, e) :: rest) = (m, c) :: (p, e) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, fcrCoeffAdd e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: fcrInsertTerm (m, c) rest) = (m, c) :: (p, e) :: rest
  rw [h]
theorem fcrInsertTermGtE (m : List Nat) (c : Nat × Nat) (p : List Nat) (e : Nat × Nat) (rest : FcrNF)
    (h : csrCompare m p = CsrMonoOrd.gt) :
    fcrInsertTerm (m, c) ((p, e) :: rest) = (p, e) :: fcrInsertTerm (m, c) rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, fcrCoeffAdd e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: fcrInsertTerm (m, c) rest) = (p, e) :: fcrInsertTerm (m, c) rest
  rw [h]

/-- Right-commutation of coefficient addition: `(e + d) + c = (e + c) + d`. -/
theorem fcrCoeffAddRightComm (e d c : Nat × Nat) :
    fcrCoeffAdd (fcrCoeffAdd e d) c = fcrCoeffAdd (fcrCoeffAdd e c) d := by
  rw [fcrCoeffAddAssoc e d c, fcrCoeffAddComm d c, ← fcrCoeffAddAssoc e c d]

/-- ★ The crux commutation: two term-insertions commute (permutation-invariance of the coefficient-aware
merge).  Structurally identical to the ℕ[X] sibling's `csrInsertTermComm`, with pair-coefficient addition. -/
theorem fcrInsertTermComm (m : List Nat) (c : Nat × Nat) (n : List Nat) (d : Nat × Nat) (P : FcrNF) :
    fcrInsertTerm (m, c) (fcrInsertTerm (n, d) P)
      = fcrInsertTerm (n, d) (fcrInsertTerm (m, c) P) := by
  induction P with
  | nil =>
      cases hmn : csrCompare m n with
      | eq =>
          have hmeqn : m = n := csrCompareEq_of m n hmn
          have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
          rw [fcrInsertTermNil n d, fcrInsertTermNil m c,
              fcrInsertTermEqE m c n d [] hmn, fcrInsertTermEqE n d m c [] hnm, hmeqn,
              fcrCoeffAddComm d c]
      | lt =>
          have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
          rw [fcrInsertTermNil n d, fcrInsertTermNil m c,
              fcrInsertTermLtE m c n d [] hmn, fcrInsertTermGtE n d m c [] hnm, fcrInsertTermNil n d]
      | gt =>
          have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn
          rw [fcrInsertTermNil n d, fcrInsertTermNil m c,
              fcrInsertTermGtE m c n d [] hmn, fcrInsertTermNil m c, fcrInsertTermLtE n d m c [] hnm]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [fcrInsertTermEqE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [fcrInsertTermEqE m c p (fcrCoeffAdd e d) rest hmp, fcrInsertTermEqE m c p e rest hmp,
                  fcrInsertTermEqE n d p (fcrCoeffAdd e c) rest hnp, fcrCoeffAddRightComm e d c]
          | lt =>
              have hpm : csrCompare p m = CsrMonoOrd.gt := csrCompareSwapLt m p hmp
              have hnm : csrCompare n m = CsrMonoOrd.gt := by rw [hnp_eq]; exact hpm
              rw [fcrInsertTermLtE m c p (fcrCoeffAdd e d) rest hmp, fcrInsertTermLtE m c p e rest hmp,
                  fcrInsertTermGtE n d m c ((p, e) :: rest) hnm, fcrInsertTermEqE n d p e rest hnp]
          | gt =>
              rw [fcrInsertTermGtE m c p (fcrCoeffAdd e d) rest hmp, fcrInsertTermGtE m c p e rest hmp,
                  fcrInsertTermEqE n d p e (fcrInsertTerm (m, c) rest) hnp]
      | lt =>
          rw [fcrInsertTermLtE n d p e rest hnp]
          cases hmn : csrCompare m n with
          | eq =>
              have hmeqn : m = n := csrCompareEq_of m n hmn
              have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
              have hmp : csrCompare m p = CsrMonoOrd.lt := by rw [hmeqn]; exact hnp
              rw [fcrInsertTermEqE m c n d ((p, e) :: rest) hmn, fcrInsertTermLtE m c p e rest hmp,
                  fcrInsertTermEqE n d m c ((p, e) :: rest) hnm, hmeqn, fcrCoeffAddComm d c]
          | lt =>
              have hmp : csrCompare m p = CsrMonoOrd.lt := csrCompareTransLt m n p hmn hnp
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [fcrInsertTermLtE m c n d ((p, e) :: rest) hmn, fcrInsertTermLtE m c p e rest hmp,
                  fcrInsertTermGtE n d m c ((p, e) :: rest) hnm, fcrInsertTermLtE n d p e rest hnp]
          | gt =>
              have hmn_gt : csrCompare m n = CsrMonoOrd.gt := hmn
              rw [fcrInsertTermGtE m c n d ((p, e) :: rest) hmn]
              cases hmp : csrCompare m p with
              | eq =>
                  rw [fcrInsertTermEqE m c p e rest hmp,
                      fcrInsertTermLtE n d p (fcrCoeffAdd e c) rest hnp]
              | lt =>
                  have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn_gt
                  rw [fcrInsertTermLtE m c p e rest hmp,
                      fcrInsertTermLtE n d m c ((p, e) :: rest) hnm]
              | gt =>
                  rw [fcrInsertTermGtE m c p e rest hmp,
                      fcrInsertTermLtE n d p e (fcrInsertTerm (m, c) rest) hnp]
      | gt =>
          rw [fcrInsertTermGtE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [fcrInsertTermEqE m c p e (fcrInsertTerm (n, d) rest) hmp,
                  fcrInsertTermEqE m c p e rest hmp,
                  fcrInsertTermGtE n d p (fcrCoeffAdd e c) rest hnp]
          | lt =>
              have hpn : csrCompare p n = CsrMonoOrd.lt := csrCompareSwapGt n p hnp
              have hmn : csrCompare m n = CsrMonoOrd.lt := csrCompareTransLt m p n hmp hpn
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [fcrInsertTermLtE m c p e (fcrInsertTerm (n, d) rest) hmp,
                  fcrInsertTermLtE m c p e rest hmp,
                  fcrInsertTermGtE n d m c ((p, e) :: rest) hnm,
                  fcrInsertTermGtE n d p e rest hnp]
          | gt =>
              rw [fcrInsertTermGtE m c p e (fcrInsertTerm (n, d) rest) hmp,
                  fcrInsertTermGtE m c p e rest hmp,
                  fcrInsertTermGtE n d p e (fcrInsertTerm (m, c) rest) hnp, ih]

/-- The additive merge: insert every term of the first list into the second. -/
def fcrMergeAdd : FcrNF → FcrNF → FcrNF
  | [], b => b
  | t :: a', b => fcrInsertTerm t (fcrMergeAdd a' b)
theorem fcrMergeAddNilLeft (b : FcrNF) : fcrMergeAdd [] b = b := rfl
theorem fcrMergeAddCons (t : List Nat × (Nat × Nat)) (a' b : FcrNF) :
    fcrMergeAdd (t :: a') b = fcrInsertTerm t (fcrMergeAdd a' b) := rfl
theorem fcrInsertTerm_mergeAdd (t : List Nat × (Nat × Nat)) (a b : FcrNF) :
    fcrInsertTerm t (fcrMergeAdd a b) = fcrMergeAdd a (fcrInsertTerm t b) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      obtain ⟨um, uc⟩ := u
      obtain ⟨tm, tc⟩ := t
      show fcrInsertTerm (tm, tc) (fcrInsertTerm (um, uc) (fcrMergeAdd a' b))
        = fcrMergeAdd ((um, uc) :: a') (fcrInsertTerm (tm, tc) b)
      rw [fcrMergeAddCons, fcrInsertTermComm tm tc um uc (fcrMergeAdd a' b), ih]
/-- Inserting the same monomial twice collapses (coefficients add). -/
theorem fcrInsertTermMergeSame (m : List Nat) (c1 c2 : Nat × Nat) (Z : FcrNF) :
    fcrInsertTerm (m, c1) (fcrInsertTerm (m, c2) Z) = fcrInsertTerm (m, fcrCoeffAdd c2 c1) Z := by
  induction Z with
  | nil =>
      rw [fcrInsertTermNil m c2, fcrInsertTermEqE m c1 m c2 [] (csrCompareRefl m),
          fcrInsertTermNil m (fcrCoeffAdd c2 c1)]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          rw [fcrInsertTermEqE m c2 p e rest hmp, fcrInsertTermEqE m c1 p (fcrCoeffAdd e c2) rest hmp,
              fcrInsertTermEqE m (fcrCoeffAdd c2 c1) p e rest hmp, fcrCoeffAddAssoc e c2 c1]
      | lt =>
          rw [fcrInsertTermLtE m c2 p e rest hmp, fcrInsertTermEqE m c1 m c2 ((p, e) :: rest)
                (csrCompareRefl m), fcrInsertTermLtE m (fcrCoeffAdd c2 c1) p e rest hmp]
      | gt =>
          rw [fcrInsertTermGtE m c2 p e rest hmp, fcrInsertTermGtE m c1 p e
                (fcrInsertTerm (m, c2) rest) hmp, fcrInsertTermGtE m (fcrCoeffAdd c2 c1) p e rest hmp, ih]
/-- Pulling an insertion out of the left list of a merge. -/
theorem fcrMergeAddInsertTermLeft (u : List Nat × (Nat × Nat)) (Y c : FcrNF) :
    fcrMergeAdd (fcrInsertTerm u Y) c = fcrInsertTerm u (fcrMergeAdd Y c) := by
  obtain ⟨um, uc⟩ := u
  induction Y with
  | nil => rfl
  | cons head Y' ih =>
      obtain ⟨v, ve⟩ := head
      cases huv : csrCompare um v with
      | eq =>
          have hum_eq : um = v := csrCompareEq_of um v huv
          rw [fcrInsertTermEqE um uc v ve Y' huv, fcrMergeAddCons,
              fcrMergeAddCons (v, ve) Y' c, hum_eq,
              fcrInsertTermMergeSame v uc ve (fcrMergeAdd Y' c)]
      | lt =>
          rw [fcrInsertTermLtE um uc v ve Y' huv, fcrMergeAddCons, fcrMergeAddCons (v, ve) Y' c]
      | gt =>
          rw [fcrInsertTermGtE um uc v ve Y' huv, fcrMergeAddCons (v, ve) (fcrInsertTerm (um, uc) Y') c,
              fcrMergeAddCons (v, ve) Y' c, ih,
              fcrInsertTermComm v ve um uc (fcrMergeAdd Y' c)]
theorem fcrMergeAddAssoc (a b c : FcrNF) :
    fcrMergeAdd (fcrMergeAdd a b) c = fcrMergeAdd a (fcrMergeAdd b c) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show fcrMergeAdd (fcrInsertTerm u (fcrMergeAdd a' b)) c
        = fcrInsertTerm u (fcrMergeAdd a' (fcrMergeAdd b c))
      rw [fcrMergeAddInsertTermLeft u (fcrMergeAdd a' b) c, ih]
theorem fcrMergeAddSwap (a b acc : FcrNF) :
    fcrMergeAdd a (fcrMergeAdd b acc) = fcrMergeAdd b (fcrMergeAdd a acc) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show fcrInsertTerm u (fcrMergeAdd a' (fcrMergeAdd b acc))
        = fcrMergeAdd b (fcrInsertTerm u (fcrMergeAdd a' acc))
      rw [ih, fcrInsertTerm_mergeAdd u b (fcrMergeAdd a' acc)]

/-! ## The strict-sortedness invariant -/

def fcrBelowHead (m : List Nat) : FcrNF → Bool
  | [] => true
  | (p, _) :: _ =>
      match csrCompare m p with
      | CsrMonoOrd.lt => true
      | CsrMonoOrd.eq => false
      | CsrMonoOrd.gt => false
def fcrNFSorted : FcrNF → Bool
  | [] => true
  | (m, _) :: rest => fcrBelowHead m rest && fcrNFSorted rest
theorem fcrBelowHeadNil (m : List Nat) : fcrBelowHead m [] = true := rfl
theorem fcrBelowHeadConsTrue (m p : List Nat) (e : Nat × Nat) (rest : FcrNF)
    (h : csrCompare m p = CsrMonoOrd.lt) : fcrBelowHead m ((p, e) :: rest) = true := by
  show (match csrCompare m p with
        | CsrMonoOrd.lt => true
        | CsrMonoOrd.eq => false
        | CsrMonoOrd.gt => false) = true
  rw [h]
theorem fcrBelowHeadConsLt (m p : List Nat) (e : Nat × Nat) (rest : FcrNF)
    (h : fcrBelowHead m ((p, e) :: rest) = true) : csrCompare m p = CsrMonoOrd.lt := by
  cases hc : csrCompare m p with
  | lt => rfl
  | eq => exact absurd h (by
      show (match csrCompare m p with
            | CsrMonoOrd.lt => true | CsrMonoOrd.eq => false | CsrMonoOrd.gt => false) ≠ true
      rw [hc]; exact fun hh => Bool.noConfusion hh)
  | gt => exact absurd h (by
      show (match csrCompare m p with
            | CsrMonoOrd.lt => true | CsrMonoOrd.eq => false | CsrMonoOrd.gt => false) ≠ true
      rw [hc]; exact fun hh => Bool.noConfusion hh)
theorem fcrNFSortedCons (m : List Nat) (c : Nat × Nat) (rest : FcrNF) :
    fcrNFSorted ((m, c) :: rest) = (fcrBelowHead m rest && fcrNFSorted rest) := rfl
theorem fcrBelowHeadInsert (q m : List Nat) (c : Nat × Nat) (B : FcrNF)
    (hq : csrCompare q m = CsrMonoOrd.lt) (hB : fcrBelowHead q B = true) :
    fcrBelowHead q (fcrInsertTerm (m, c) B) = true := by
  cases B with
  | nil => exact fcrBelowHeadConsTrue q m c [] hq
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq => rw [fcrInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [fcrInsertTermLtE m c p e rest hmp]; exact fcrBelowHeadConsTrue q m c ((p, e) :: rest) hq
      | gt =>
          rw [fcrInsertTermGtE m c p e rest hmp]
          exact fcrBelowHeadConsTrue q p e (fcrInsertTerm (m, c) rest) (fcrBelowHeadConsLt q p e rest hB)
theorem fcrInsertPreservesSorted (m : List Nat) (c : Nat × Nat) (B : FcrNF)
    (hB : fcrNFSorted B = true) : fcrNFSorted (fcrInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hbelow : fcrBelowHead p rest = true := csrAndTrueLeft _ _ hB
      have hrest : fcrNFSorted rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq => rw [fcrInsertTermEqE m c p e rest hmp]; exact hB
      | lt =>
          rw [fcrInsertTermLtE m c p e rest hmp, fcrNFSortedCons]
          exact csrAndIntro _ _ (fcrBelowHeadConsTrue m p e rest hmp) hB
      | gt =>
          rw [fcrInsertTermGtE m c p e rest hmp, fcrNFSortedCons]
          have hpm : csrCompare p m = CsrMonoOrd.lt := csrCompareSwapGt m p hmp
          exact csrAndIntro _ _
            (fcrBelowHeadInsert p m c rest hpm hbelow) (ih hrest)
theorem fcrInsertFront (m : List Nat) (c : Nat × Nat) (B : FcrNF) (h : fcrBelowHead m B = true) :
    fcrInsertTerm (m, c) B = (m, c) :: B := by
  cases B with
  | nil => rfl
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      exact fcrInsertTermLtE m c p e rest (fcrBelowHeadConsLt m p e rest h)
theorem fcrMergeAddNilRight (A : FcrNF) (hA : fcrNFSorted A = true) : fcrMergeAdd A [] = A := by
  induction A with
  | nil => rfl
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      have hbelow : fcrBelowHead m a' = true := csrAndTrueLeft _ _ hA
      have hrest : fcrNFSorted a' = true := csrAndTrueRight _ _ hA
      show fcrInsertTerm (m, c) (fcrMergeAdd a' []) = (m, c) :: a'
      rw [ih hrest, fcrInsertFront m c a' hbelow]
theorem fcrMergeAddComm (A B : FcrNF) (hA : fcrNFSorted A = true) (hB : fcrNFSorted B = true) :
    fcrMergeAdd A B = fcrMergeAdd B A := by
  have h := fcrMergeAddSwap A B []
  rw [fcrMergeAddNilRight B hB, fcrMergeAddNilRight A hA] at h
  exact h
theorem fcrMergeAddPreservesSorted (A B : FcrNF) (hB : fcrNFSorted B = true) :
    fcrNFSorted (fcrMergeAdd A B) = true := by
  induction A with
  | nil => exact hB
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      show fcrNFSorted (fcrInsertTerm (m, c) (fcrMergeAdd a' B)) = true
      exact fcrInsertPreservesSorted m c (fcrMergeAdd a' B) ih

/-! ## The multiplicative convolution (monomial multiset union × coefficient product) -/

/-- A single term `(m, c)` times a polynomial (right multiply): monomial product is the imported
`csrMonoMul` (multiset union), coefficient product is `fcrCoeffMul`. -/
def fcrTermMul (m : List Nat) (c : Nat × Nat) : FcrNF → FcrNF
  | [] => []
  | (n, d) :: rest => fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c rest)
/-- The Cauchy convolution of two polynomials. -/
def fcrMulConvolve : FcrNF → FcrNF → FcrNF
  | [], _ => []
  | (m, c) :: rest, b => fcrMergeAdd (fcrTermMul m c b) (fcrMulConvolve rest b)
theorem fcrTermMulNil (m : List Nat) (c : Nat × Nat) : fcrTermMul m c [] = [] := rfl
theorem fcrTermMulCons (m : List Nat) (c : Nat × Nat) (n : List Nat) (d : Nat × Nat) (rest : FcrNF) :
    fcrTermMul m c ((n, d) :: rest) = fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c rest) :=
  rfl
theorem fcrMulConvolveNil (b : FcrNF) : fcrMulConvolve [] b = [] := rfl
theorem fcrMulConvolveCons (m : List Nat) (c : Nat × Nat) (rest b : FcrNF) :
    fcrMulConvolve ((m, c) :: rest) b = fcrMergeAdd (fcrTermMul m c b) (fcrMulConvolve rest b) := rfl

theorem fcrTermMulSorted (m : List Nat) (c : Nat × Nat) (B : FcrNF) :
    fcrNFSorted (fcrTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show fcrNFSorted (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c rest)) = true
      exact fcrInsertPreservesSorted (csrMonoMul m n) (fcrCoeffMul c d) (fcrTermMul m c rest) ih
theorem fcrMulConvolveSorted (A B : FcrNF) : fcrNFSorted (fcrMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show fcrNFSorted (fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve rest B)) = true
      exact fcrMergeAddPreservesSorted (fcrTermMul m c B) (fcrMulConvolve rest B) ih

/-- termMul commutes with a single insertion (coefficients distribute via `fcrCoeffMulAddRight`). -/
theorem fcrTermMul_insertTerm (m : List Nat) (c : Nat × Nat) (n : List Nat) (d : Nat × Nat) (B : FcrNF) :
    fcrTermMul m c (fcrInsertTerm (n, d) B)
      = fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [fcrInsertTermEqE n d p e rest hnp, fcrTermMulCons m c p (fcrCoeffAdd e d) rest,
              fcrTermMulCons m c p e rest, hnp_eq,
              fcrInsertTermMergeSame (csrMonoMul m p) (fcrCoeffMul c d) (fcrCoeffMul c e)
                (fcrTermMul m c rest), fcrCoeffMulAddRight c e d]
      | lt =>
          rw [fcrInsertTermLtE n d p e rest hnp, fcrTermMulCons m c n d ((p, e) :: rest),
              fcrTermMulCons m c p e rest]
      | gt =>
          rw [fcrInsertTermGtE n d p e rest hnp, fcrTermMulCons m c p e (fcrInsertTerm (n, d) rest),
              ih, fcrTermMulCons m c p e rest,
              fcrInsertTermComm (csrMonoMul m p) (fcrCoeffMul c e) (csrMonoMul m n) (fcrCoeffMul c d)
                (fcrTermMul m c rest)]

theorem fcrTermMul_merge (m : List Nat) (c : Nat × Nat) (B C : FcrNF) :
    fcrTermMul m c (fcrMergeAdd B C) = fcrMergeAdd (fcrTermMul m c B) (fcrTermMul m c C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show fcrTermMul m c (fcrInsertTerm (n, d) (fcrMergeAdd B' C))
        = fcrMergeAdd (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c B')) (fcrTermMul m c C)
      rw [fcrTermMul_insertTerm m c n d (fcrMergeAdd B' C), ih,
          fcrMergeAddInsertTermLeft (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c B') (fcrTermMul m c C)]

theorem fcrMulConvolveAnnihil (A : FcrNF) : fcrMulConvolve A [] = [] := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show fcrMergeAdd (fcrTermMul m c []) (fcrMulConvolve rest []) = []
      rw [fcrTermMulNil m c, fcrMergeAddNilLeft, ih]

/-- Rearrange a merge of four sorted NFs, swapping the inner two. -/
theorem fcrMergeAdd4Swap (a b c d : FcrNF)
    (hb : fcrNFSorted b = true) (hc : fcrNFSorted c = true) :
    fcrMergeAdd (fcrMergeAdd a b) (fcrMergeAdd c d)
      = fcrMergeAdd (fcrMergeAdd a c) (fcrMergeAdd b d) := by
  rw [fcrMergeAddAssoc a b (fcrMergeAdd c d), ← fcrMergeAddAssoc b c d,
      fcrMergeAddComm b c hb hc, fcrMergeAddAssoc c b d, ← fcrMergeAddAssoc a c (fcrMergeAdd b d)]

/-- ★ left distributivity: `A * (B + C) = A*B + A*C`. -/
theorem fcrMulConvolve_leftDistrib (A B C : FcrNF) :
    fcrMulConvolve A (fcrMergeAdd B C)
      = fcrMergeAdd (fcrMulConvolve A B) (fcrMulConvolve A C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show fcrMergeAdd (fcrTermMul m c (fcrMergeAdd B C)) (fcrMulConvolve A' (fcrMergeAdd B C))
        = fcrMergeAdd (fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B))
            (fcrMergeAdd (fcrTermMul m c C) (fcrMulConvolve A' C))
      rw [fcrTermMul_merge m c B C, ih]
      exact fcrMergeAdd4Swap (fcrTermMul m c B) (fcrTermMul m c C) (fcrMulConvolve A' B)
        (fcrMulConvolve A' C) (fcrTermMulSorted m c C) (fcrMulConvolveSorted A' B)

/-- termMul distributes over a coefficient sum. -/
theorem fcrTermMul_coeffAdd (m : List Nat) (c1 c2 : Nat × Nat) (Z : FcrNF) :
    fcrTermMul m (fcrCoeffAdd c1 c2) Z = fcrMergeAdd (fcrTermMul m c1 Z) (fcrTermMul m c2 Z) := by
  induction Z with
  | nil => rfl
  | cons head Z' ih =>
      obtain ⟨n, d⟩ := head
      show fcrInsertTerm (csrMonoMul m n, fcrCoeffMul (fcrCoeffAdd c1 c2) d) (fcrTermMul m (fcrCoeffAdd c1 c2) Z')
        = fcrMergeAdd (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c1 d) (fcrTermMul m c1 Z'))
            (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c2 d) (fcrTermMul m c2 Z'))
      rw [fcrMergeAddInsertTermLeft (csrMonoMul m n, fcrCoeffMul c1 d) (fcrTermMul m c1 Z')
            (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c2 d) (fcrTermMul m c2 Z')),
          ← fcrInsertTerm_mergeAdd (csrMonoMul m n, fcrCoeffMul c2 d) (fcrTermMul m c1 Z') (fcrTermMul m c2 Z'),
          fcrInsertTermMergeSame (csrMonoMul m n) (fcrCoeffMul c1 d) (fcrCoeffMul c2 d)
            (fcrMergeAdd (fcrTermMul m c1 Z') (fcrTermMul m c2 Z')),
          ih, fcrCoeffAddMulRight c1 c2 d, fcrCoeffAddComm (fcrCoeffMul c1 d) (fcrCoeffMul c2 d)]

/-- convolving after one insertion into the first argument. -/
theorem fcrConvolve_insertTermLeft (m : List Nat) (c : Nat × Nat) (W Z : FcrNF) :
    fcrMulConvolve (fcrInsertTerm (m, c) W) Z
      = fcrMergeAdd (fcrTermMul m c Z) (fcrMulConvolve W Z) := by
  induction W with
  | nil => rfl
  | cons head W' ih =>
      obtain ⟨p, g⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [fcrInsertTermEqE m c p g W' hmp, fcrMulConvolveCons p (fcrCoeffAdd g c) W' Z,
              fcrMulConvolveCons p g W' Z, hmeqp,
              fcrTermMul_coeffAdd p g c Z,
              fcrMergeAddAssoc (fcrTermMul p g Z) (fcrTermMul p c Z) (fcrMulConvolve W' Z),
              fcrMergeAddSwap (fcrTermMul p g Z) (fcrTermMul p c Z) (fcrMulConvolve W' Z)]
      | lt =>
          rw [fcrInsertTermLtE m c p g W' hmp, fcrMulConvolveCons m c ((p, g) :: W') Z]
      | gt =>
          rw [fcrInsertTermGtE m c p g W' hmp,
              fcrMulConvolveCons p g (fcrInsertTerm (m, c) W') Z, ih,
              fcrMulConvolveCons p g W' Z,
              fcrMergeAddSwap (fcrTermMul p g Z) (fcrTermMul m c Z) (fcrMulConvolve W' Z)]

/-- ★ right distributivity: `(X + Y) * Z = X*Z + Y*Z`. -/
theorem fcrMulConvolve_rightDistrib (X Y Z : FcrNF) :
    fcrMulConvolve (fcrMergeAdd X Y) Z
      = fcrMergeAdd (fcrMulConvolve X Z) (fcrMulConvolve Y Z) := by
  induction X with
  | nil => rfl
  | cons head X' ih =>
      obtain ⟨m, c⟩ := head
      show fcrMulConvolve (fcrInsertTerm (m, c) (fcrMergeAdd X' Y)) Z
        = fcrMergeAdd (fcrMergeAdd (fcrTermMul m c Z) (fcrMulConvolve X' Z)) (fcrMulConvolve Y Z)
      rw [fcrConvolve_insertTermLeft m c (fcrMergeAdd X' Y) Z, ih,
          fcrMergeAddAssoc (fcrTermMul m c Z) (fcrMulConvolve X' Z) (fcrMulConvolve Y Z)]

/-- termMul composition: `(m*n)·(c*d)` applied to `C` equals scaling by `(m,c)` then `(n,d)`. -/
theorem fcrTermMul_compose (m : List Nat) (c : Nat × Nat) (n : List Nat) (d : Nat × Nat) (C : FcrNF) :
    fcrTermMul (csrMonoMul m n) (fcrCoeffMul c d) C = fcrTermMul m c (fcrTermMul n d C) := by
  induction C with
  | nil => rfl
  | cons head C' ih =>
      obtain ⟨p, f⟩ := head
      show fcrInsertTerm (csrMonoMul (csrMonoMul m n) p, fcrCoeffMul (fcrCoeffMul c d) f)
            (fcrTermMul (csrMonoMul m n) (fcrCoeffMul c d) C')
        = fcrTermMul m c (fcrInsertTerm (csrMonoMul n p, fcrCoeffMul d f) (fcrTermMul n d C'))
      rw [fcrTermMul_insertTerm m c (csrMonoMul n p) (fcrCoeffMul d f) (fcrTermMul n d C'), ih,
          csrMonoMulAssoc m n p, fcrCoeffMulAssoc c d f]

/-- convolving a termMul equals termMul of a convolve. -/
theorem fcrTermMul_convolve (m : List Nat) (c : Nat × Nat) (B C : FcrNF) :
    fcrMulConvolve (fcrTermMul m c B) C = fcrTermMul m c (fcrMulConvolve B C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show fcrMulConvolve (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c B')) C
        = fcrTermMul m c (fcrMergeAdd (fcrTermMul n d C) (fcrMulConvolve B' C))
      rw [fcrConvolve_insertTermLeft (csrMonoMul m n) (fcrCoeffMul c d) (fcrTermMul m c B') C, ih,
          fcrTermMul_merge m c (fcrTermMul n d C) (fcrMulConvolve B' C),
          fcrTermMul_compose m c n d C]

/-- ★ associativity of the convolution: `(A*B)*C = A*(B*C)`. -/
theorem fcrMulConvolveAssoc (A B C : FcrNF) :
    fcrMulConvolve (fcrMulConvolve A B) C = fcrMulConvolve A (fcrMulConvolve B C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show fcrMulConvolve (fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B)) C
        = fcrMergeAdd (fcrTermMul m c (fcrMulConvolve B C)) (fcrMulConvolve A' (fcrMulConvolve B C))
      rw [fcrMulConvolve_rightDistrib (fcrTermMul m c B) (fcrMulConvolve A' B) C, ih,
          fcrTermMul_convolve m c B C]

/-! ## Monomial-sortedness of every term, and convolution commutativity / unit -/

def fcrNFMonoSorted : FcrNF → Bool
  | [] => true
  | (m, _) :: rest => csrMonoSorted m && fcrNFMonoSorted rest
theorem fcrNFMonoSortedCons (m : List Nat) (c : Nat × Nat) (rest : FcrNF) :
    fcrNFMonoSorted ((m, c) :: rest) = (csrMonoSorted m && fcrNFMonoSorted rest) := rfl
theorem fcrInsertTermMonoSorted (m : List Nat) (c : Nat × Nat) (B : FcrNF)
    (hm : csrMonoSorted m = true) (hB : fcrNFMonoSorted B = true) :
    fcrNFMonoSorted (fcrInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rw [fcrInsertTermNil m c, fcrNFMonoSortedCons]; exact csrAndIntro _ _ hm rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hp : csrMonoSorted p = true := csrAndTrueLeft _ _ hB
      have hrest : fcrNFMonoSorted rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq => rw [fcrInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [fcrInsertTermLtE m c p e rest hmp, fcrNFMonoSortedCons]; exact csrAndIntro _ _ hm hB
      | gt =>
          rw [fcrInsertTermGtE m c p e rest hmp, fcrNFMonoSortedCons]
          exact csrAndIntro _ _ hp (ih hrest)
theorem fcrMergeAddMonoSorted (A B : FcrNF) (hA : fcrNFMonoSorted A = true)
    (hB : fcrNFMonoSorted B = true) : fcrNFMonoSorted (fcrMergeAdd A B) = true := by
  induction A with
  | nil => exact hB
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hm : csrMonoSorted m = true := csrAndTrueLeft _ _ hA
      have hA' : fcrNFMonoSorted A' = true := csrAndTrueRight _ _ hA
      show fcrNFMonoSorted (fcrInsertTerm (m, c) (fcrMergeAdd A' B)) = true
      exact fcrInsertTermMonoSorted m c (fcrMergeAdd A' B) hm (ih hA')
theorem fcrTermMulMonoSorted (m : List Nat) (c : Nat × Nat) (B : FcrNF) (hm : csrMonoSorted m = true) :
    fcrNFMonoSorted (fcrTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show fcrNFMonoSorted (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c rest)) = true
      exact fcrInsertTermMonoSorted (csrMonoMul m n) (fcrCoeffMul c d) (fcrTermMul m c rest)
        (csrMonoMulSorted m n hm) ih
theorem fcrMulConvolveMonoSorted (A B : FcrNF) (hA : fcrNFMonoSorted A = true)
    (_hB : fcrNFMonoSorted B = true) : fcrNFMonoSorted (fcrMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hm : csrMonoSorted m = true := csrAndTrueLeft _ _ hA
      have hA' : fcrNFMonoSorted A' = true := csrAndTrueRight _ _ hA
      show fcrNFMonoSorted (fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B)) = true
      exact fcrMergeAddMonoSorted (fcrTermMul m c B) (fcrMulConvolve A' B)
        (fcrTermMulMonoSorted m c B hm) (ih hA')

/-- termMul equals convolving with a single-term poly (needs sorted monomials for `csrMonoMul` comm). -/
theorem fcrTermMulEqConvolveSingle (m : List Nat) (c : Nat × Nat) (hm : csrMonoSorted m = true) :
    (B : FcrNF) → fcrNFMonoSorted B = true → fcrTermMul m c B = fcrMulConvolve B [(m, c)]
  | [], _ => rfl
  | (n, d) :: B', hB => by
      have hn : csrMonoSorted n = true := csrAndTrueLeft _ _ hB
      have hB' : fcrNFMonoSorted B' = true := csrAndTrueRight _ _ hB
      have ih := fcrTermMulEqConvolveSingle m c hm B' hB'
      show fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c B')
        = fcrMergeAdd (fcrTermMul n d [(m, c)]) (fcrMulConvolve B' [(m, c)])
      rw [fcrTermMulCons n d m c [], fcrTermMulNil n d,
          fcrMergeAddInsertTermLeft (csrMonoMul n m, fcrCoeffMul d c) [] (fcrMulConvolve B' [(m, c)]),
          fcrMergeAddNilLeft, ← ih, csrMonoMulComm m n hm hn, fcrCoeffMulComm c d]

/-- ★ commutativity of the convolution (needs sorted first arg + sorted monomials). -/
theorem fcrMulConvolveComm : (A B : FcrNF) → fcrNFSorted A = true → fcrNFMonoSorted A = true →
    fcrNFMonoSorted B = true → fcrMulConvolve A B = fcrMulConvolve B A
  | [], B, _, _, _ => (fcrMulConvolveAnnihil B).symm
  | (m, c) :: A', B, hAs, hAm, hBm => by
      have hbelow : fcrBelowHead m A' = true := csrAndTrueLeft _ _ hAs
      have hAs' : fcrNFSorted A' = true := csrAndTrueRight _ _ hAs
      have hm : csrMonoSorted m = true := csrAndTrueLeft _ _ hAm
      have hAm' : fcrNFMonoSorted A' = true := csrAndTrueRight _ _ hAm
      have ih := fcrMulConvolveComm A' B hAs' hAm' hBm
      show fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B) = fcrMulConvolve B ((m, c) :: A')
      rw [fcrTermMulEqConvolveSingle m c hm B hBm, ih,
          ← fcrMulConvolve_leftDistrib B [(m, c)] A', fcrMergeAddCons (m, c) [] A',
          fcrMergeAddNilLeft, fcrInsertFront m c A' hbelow]

/-- ★ multiplicative unit: `A * [([], (1,0))] = A` for a sorted NF. -/
theorem fcrMulConvolveUnit : (A : FcrNF) → fcrNFSorted A = true → fcrMulConvolve A [([], (1, 0))] = A
  | [], _ => rfl
  | (m, c) :: A', hAs => by
      have hbelow : fcrBelowHead m A' = true := csrAndTrueLeft _ _ hAs
      have hAs' : fcrNFSorted A' = true := csrAndTrueRight _ _ hAs
      have ih := fcrMulConvolveUnit A' hAs'
      show fcrMergeAdd (fcrTermMul m c [([], (1, 0))]) (fcrMulConvolve A' [([], (1, 0))]) = (m, c) :: A'
      rw [fcrTermMulCons m c [] (1, 0) [], fcrTermMulNil m c, csrMonoMulNilRight m, fcrCoeffMulOne c,
          fcrMergeAddInsertTermLeft (m, c) [] (fcrMulConvolve A' [([], (1, 0))]), fcrMergeAddNilLeft,
          ih, fcrInsertFront m c A' hbelow]

/-! ## Negation of a normal form (negate every coefficient) -/

/-- Negate every coefficient of a normal form (monomials and order unchanged). -/
def fcrNegate : FcrNF → FcrNF
  | [] => []
  | (m, c) :: rest => (m, fcrCoeffNeg c) :: fcrNegate rest
theorem fcrNegateCons (m : List Nat) (c : Nat × Nat) (rest : FcrNF) :
    fcrNegate ((m, c) :: rest) = (m, fcrCoeffNeg c) :: fcrNegate rest := rfl

/-- Negation ignores what the head coefficient is, so it preserves the below-head test. -/
theorem fcrNegateBelowHead (m : List Nat) (A : FcrNF) :
    fcrBelowHead m (fcrNegate A) = fcrBelowHead m A := by
  cases A with
  | nil => rfl
  | cons head rest => obtain ⟨p, e⟩ := head; rfl

theorem fcrNegateSorted (A : FcrNF) (hA : fcrNFSorted A = true) : fcrNFSorted (fcrNegate A) = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      have hbelow : fcrBelowHead m rest = true := csrAndTrueLeft _ _ hA
      have hrest : fcrNFSorted rest = true := csrAndTrueRight _ _ hA
      rw [fcrNegateCons, fcrNFSortedCons]
      exact csrAndIntro _ _ (by rw [fcrNegateBelowHead m rest]; exact hbelow) (ih hrest)

theorem fcrNegateInvol (A : FcrNF) : fcrNegate (fcrNegate A) = A := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      rw [fcrNegateCons, fcrNegateCons, fcrCoeffNegNeg c, ih]

theorem fcrNegate_insertTerm (m : List Nat) (c : Nat × Nat) (X : FcrNF) :
    fcrNegate (fcrInsertTerm (m, c) X) = fcrInsertTerm (m, fcrCoeffNeg c) (fcrNegate X) := by
  induction X with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          rw [fcrInsertTermEqE m c p e rest hmp, fcrNegateCons, fcrNegateCons,
              fcrInsertTermEqE m (fcrCoeffNeg c) p (fcrCoeffNeg e) (fcrNegate rest) hmp,
              fcrCoeffNegAdd e c]
      | lt =>
          rw [fcrInsertTermLtE m c p e rest hmp, fcrNegateCons, fcrNegateCons,
              fcrInsertTermLtE m (fcrCoeffNeg c) p (fcrCoeffNeg e) (fcrNegate rest) hmp]
      | gt =>
          rw [fcrInsertTermGtE m c p e rest hmp, fcrNegateCons, fcrNegateCons, ih,
              fcrInsertTermGtE m (fcrCoeffNeg c) p (fcrCoeffNeg e) (fcrNegate rest) hmp]

theorem fcrNegate_mergeAdd (A B : FcrNF) :
    fcrNegate (fcrMergeAdd A B) = fcrMergeAdd (fcrNegate A) (fcrNegate B) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show fcrNegate (fcrInsertTerm (m, c) (fcrMergeAdd A' B))
        = fcrInsertTerm (m, fcrCoeffNeg c) (fcrMergeAdd (fcrNegate A') (fcrNegate B))
      rw [fcrNegate_insertTerm m c (fcrMergeAdd A' B), ih]

/-! ## The all-zero-valued predicate and its closure lemmas -/

/-- Every coefficient is zero-valued (`pos = neg`).  The single-list structural check underlying the decision. -/
def fcrNFAllZero : FcrNF → Bool
  | [] => true
  | (_, c) :: rest => fcrCoeffIsZero c && fcrNFAllZero rest
theorem fcrNFAllZeroCons (m : List Nat) (c : Nat × Nat) (rest : FcrNF) :
    fcrNFAllZero ((m, c) :: rest) = (fcrCoeffIsZero c && fcrNFAllZero rest) := rfl

/-- `fcrNegate` preserves all-zero-valuedness. -/
theorem fcrNegatePreservesAllZero (A : FcrNF) : fcrNFAllZero (fcrNegate A) = fcrNFAllZero A := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      rw [fcrNegateCons, fcrNFAllZeroCons, fcrNFAllZeroCons, fcrCoeffNegIsZero c, ih]

/-- Inserting a zero-valued term into an all-zero NF stays all-zero. -/
theorem fcrInsertTermAllZero (m : List Nat) (c : Nat × Nat) (B : FcrNF)
    (hc : fcrCoeffIsZero c = true) (hB : fcrNFAllZero B = true) :
    fcrNFAllZero (fcrInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rw [fcrInsertTermNil m c, fcrNFAllZeroCons]; exact csrAndIntro _ _ hc rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have he : fcrCoeffIsZero e = true := csrAndTrueLeft _ _ hB
      have hrest : fcrNFAllZero rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq =>
          rw [fcrInsertTermEqE m c p e rest hmp, fcrNFAllZeroCons]
          exact csrAndIntro _ _ (fcrCoeffAddZeroValued e c he hc) hrest
      | lt =>
          rw [fcrInsertTermLtE m c p e rest hmp, fcrNFAllZeroCons]
          exact csrAndIntro _ _ hc hB
      | gt =>
          rw [fcrInsertTermGtE m c p e rest hmp, fcrNFAllZeroCons]
          exact csrAndIntro _ _ he (ih hrest)

/-- Merging two all-zero NFs stays all-zero. -/
theorem fcrMergeAddAllZero (A B : FcrNF) (hA : fcrNFAllZero A = true) (hB : fcrNFAllZero B = true) :
    fcrNFAllZero (fcrMergeAdd A B) = true := by
  induction A with
  | nil => exact hB
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hc : fcrCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hA' : fcrNFAllZero A' = true := csrAndTrueRight _ _ hA
      show fcrNFAllZero (fcrInsertTerm (m, c) (fcrMergeAdd A' B)) = true
      exact fcrInsertTermAllZero m c (fcrMergeAdd A' B) hc (ih hA')

/-! ## The `fcrEvalCross` semantic model: the per-monomial coefficient sum -/

/-- The coefficient contributed by a term at a queried monomial: `d` on a match, `(0,0)` otherwise. -/
def fcrCondCoeff : Bool → (Nat × Nat) → (Nat × Nat)
  | true, d => d
  | false, _ => (0, 0)
theorem fcrCondCoeffTrue (d : Nat × Nat) : fcrCondCoeff true d = d := rfl
theorem fcrCondCoeffFalse (d : Nat × Nat) : fcrCondCoeff false d = (0, 0) := rfl
theorem fcrCondCoeffZero (b : Bool) (c : Nat × Nat) (hc : fcrCoeffIsZero c = true) :
    fcrCoeffIsZero (fcrCondCoeff b c) = true := by
  cases b with
  | true => exact hc
  | false => rfl

/-- Coefficient add-swap of the first two summands: `x + (y + z) = y + (x + z)`. -/
theorem fcrCoeffAddSwap13 (x y z : Nat × Nat) :
    fcrCoeffAdd x (fcrCoeffAdd y z) = fcrCoeffAdd y (fcrCoeffAdd x z) := by
  rw [← fcrCoeffAddAssoc x y z, fcrCoeffAddComm x y, fcrCoeffAddAssoc y x z]

/-- `neg c + c` is zero-valued. -/
theorem fcrCoeffNegAddIsZero (c : Nat × Nat) : fcrCoeffIsZero (fcrCoeffAdd (fcrCoeffNeg c) c) = true := by
  obtain ⟨p, n⟩ := c
  show Nat.beq (n + p) (p + n) = true
  rw [Nat.add_comm n p]; exact csrNatBeqRefl (p + n)

/-- A monomial `m` distinct from `q` (witnessed by `csrCompare m q = lt`) has `csrNatListEq m q = false`. -/
theorem fcrNatListEqFalseOfLt (m q : List Nat) (h : csrCompare m q = CsrMonoOrd.lt) :
    csrNatListEq m q = false := by
  cases hb : csrNatListEq m q with
  | false => rfl
  | true =>
      have hmq : m = q := csrNatListEq_eq m q hb
      rw [csrCompareOfEq m q hmq] at h
      exact CsrMonoOrd.noConfusion h

/-- The per-monomial coefficient sum of a normal form. -/
def fcrEvalCross (m : List Nat) : FcrNF → (Nat × Nat)
  | [] => (0, 0)
  | (p, c) :: rest => fcrCoeffAdd (fcrCondCoeff (csrNatListEq m p) c) (fcrEvalCross m rest)
theorem fcrEvalCrossNil (m : List Nat) : fcrEvalCross m [] = (0, 0) := rfl
theorem fcrEvalCrossCons (m p : List Nat) (c : Nat × Nat) (rest : FcrNF) :
    fcrEvalCross m ((p, c) :: rest) = fcrCoeffAdd (fcrCondCoeff (csrNatListEq m p) c) (fcrEvalCross m rest) :=
  rfl

/-- `fcrEvalCross` homomorphism for a single insertion. -/
theorem fcrEvalCross_insertTerm (m n : List Nat) (d : Nat × Nat) (B : FcrNF) :
    fcrEvalCross m (fcrInsertTerm (n, d) B)
      = fcrCoeffAdd (fcrCondCoeff (csrNatListEq m n) d) (fcrEvalCross m B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hn_eq : n = p := csrCompareEq_of n p hnp
          rw [fcrInsertTermEqE n d p e rest hnp, fcrEvalCrossCons, fcrEvalCrossCons, hn_eq]
          cases hmp : csrNatListEq m p with
          | true =>
              rw [fcrCondCoeffTrue, fcrCondCoeffTrue, fcrCondCoeffTrue,
                  fcrCoeffAddAssoc e d (fcrEvalCross m rest), fcrCoeffAddSwap13 e d (fcrEvalCross m rest)]
          | false =>
              rw [fcrCondCoeffFalse, fcrCondCoeffFalse, fcrCondCoeffFalse,
                  fcrCoeffAddZeroLeft, fcrCoeffAddZeroLeft]
      | lt =>
          rw [fcrInsertTermLtE n d p e rest hnp, fcrEvalCrossCons]
      | gt =>
          rw [fcrInsertTermGtE n d p e rest hnp, fcrEvalCrossCons, ih, fcrEvalCrossCons]
          exact fcrCoeffAddSwap13 (fcrCondCoeff (csrNatListEq m p) e)
            (fcrCondCoeff (csrNatListEq m n) d) (fcrEvalCross m rest)

/-- `fcrEvalCross` homomorphism for the additive merge. -/
theorem fcrEvalCross_mergeAdd (m : List Nat) (A B : FcrNF) :
    fcrEvalCross m (fcrMergeAdd A B) = fcrCoeffAdd (fcrEvalCross m A) (fcrEvalCross m B) := by
  induction A with
  | nil => rw [fcrMergeAddNilLeft, fcrEvalCrossNil, fcrCoeffAddZeroLeft]
  | cons head A' ih =>
      obtain ⟨p, c⟩ := head
      show fcrEvalCross m (fcrInsertTerm (p, c) (fcrMergeAdd A' B))
        = fcrCoeffAdd (fcrCoeffAdd (fcrCondCoeff (csrNatListEq m p) c) (fcrEvalCross m A')) (fcrEvalCross m B)
      rw [fcrEvalCross_insertTerm m p c (fcrMergeAdd A' B), ih,
          fcrCoeffAddAssoc (fcrCondCoeff (csrNatListEq m p) c) (fcrEvalCross m A') (fcrEvalCross m B)]

/-- An all-zero NF evaluates to a zero-valued coefficient at every monomial. -/
theorem fcrAllZero_evalZero (m : List Nat) (W : FcrNF) (hW : fcrNFAllZero W = true) :
    fcrCoeffIsZero (fcrEvalCross m W) = true := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      have hc : fcrCoeffIsZero c = true := csrAndTrueLeft _ _ hW
      have hrest : fcrNFAllZero rest = true := csrAndTrueRight _ _ hW
      rw [fcrEvalCrossCons]
      exact fcrCoeffAddZeroValued _ _ (fcrCondCoeffZero (csrNatListEq m p) c hc) (ih hrest)

/-- Below the head, a sorted NF evaluates to `(0,0)`: the queried monomial is strictly below every term. -/
theorem fcrEvalBelowZero (m : List Nat) (W : FcrNF) (hbelow : fcrBelowHead m W = true)
    (hsorted : fcrNFSorted W = true) : fcrEvalCross m W = (0, 0) := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨q, e⟩ := head
      have hmq : csrCompare m q = CsrMonoOrd.lt := fcrBelowHeadConsLt m q e rest hbelow
      have hmqEq : csrNatListEq m q = false := fcrNatListEqFalseOfLt m q hmq
      have hqbelow : fcrBelowHead q rest = true := csrAndTrueLeft _ _ hsorted
      have hrest : fcrNFSorted rest = true := csrAndTrueRight _ _ hsorted
      have hmrest : fcrBelowHead m rest = true := by
        cases rest with
        | nil => rfl
        | cons head2 rest2 =>
            obtain ⟨r, f⟩ := head2
            have hqr : csrCompare q r = CsrMonoOrd.lt := fcrBelowHeadConsLt q r f rest2 hqbelow
            exact fcrBelowHeadConsTrue m r f rest2 (csrCompareTransLt m q r hmq hqr)
      rw [fcrEvalCrossCons, hmqEq, fcrCondCoeffFalse, fcrCoeffAddZeroLeft, ih hmrest hrest]

/-- The extensionality that inverts `fcrAllZero_evalZero` on sorted NFs: if a sorted NF evaluates to a
zero-valued coefficient at every monomial, every stored coefficient is zero-valued. -/
theorem fcrSortedEvalZero_allZero (W : FcrNF) (hsorted : fcrNFSorted W = true)
    (hzero : ∀ m, fcrCoeffIsZero (fcrEvalCross m W) = true) : fcrNFAllZero W = true := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      have hbelow : fcrBelowHead p rest = true := csrAndTrueLeft _ _ hsorted
      have hrest : fcrNFSorted rest = true := csrAndTrueRight _ _ hsorted
      have hevalPrest : fcrEvalCross p rest = (0, 0) := fcrEvalBelowZero p rest hbelow hrest
      have hc : fcrCoeffIsZero c = true := by
        have h := hzero p
        rw [fcrEvalCrossCons, csrNatListEqRefl p, hevalPrest, fcrCoeffAddZeroRight, fcrCondCoeffTrue] at h
        exact h
      have hrestZero : ∀ mm, fcrCoeffIsZero (fcrEvalCross mm rest) = true := by
        intro mm
        cases hmp : csrNatListEq mm p with
        | true =>
            have hmeqp : mm = p := csrNatListEq_eq mm p hmp
            rw [hmeqp, hevalPrest]; rfl
        | false =>
            have h := hzero mm
            rw [fcrEvalCrossCons, hmp, fcrCondCoeffFalse, fcrCoeffAddZeroLeft] at h
            exact h
      rw [fcrNFAllZeroCons]
      exact csrAndIntro _ _ hc (ih hrest hrestZero)

/-- ★ The all-zero cancellation: if `mergeAdd X Z` and `Z` are both all-zero (with `X` sorted), so is `X`.
The crux of the decision equivalence's transitivity, routed entirely through `fcrEvalCross`. -/
theorem fcrMergeAddAllZeroCancel (X Z : FcrNF) (hX : fcrNFSorted X = true)
    (hXZ : fcrNFAllZero (fcrMergeAdd X Z) = true) (hZ : fcrNFAllZero Z = true) :
    fcrNFAllZero X = true := by
  apply fcrSortedEvalZero_allZero X hX
  intro m
  have hmerge : fcrCoeffIsZero (fcrEvalCross m (fcrMergeAdd X Z)) = true := fcrAllZero_evalZero m _ hXZ
  rw [fcrEvalCross_mergeAdd m X Z] at hmerge
  exact fcrCoeffAddCancelZero (fcrEvalCross m X) (fcrEvalCross m Z) hmerge (fcrAllZero_evalZero m Z hZ)

/-- `fcrCondCoeff` commutes with negation. -/
theorem fcrCondCoeffNeg (b : Bool) (c : Nat × Nat) :
    fcrCondCoeff b (fcrCoeffNeg c) = fcrCoeffNeg (fcrCondCoeff b c) := by
  cases b with | true => rfl | false => rfl

/-- `fcrEvalCross` homomorphism for negation. -/
theorem fcrEvalCross_negate (m : List Nat) (A : FcrNF) :
    fcrEvalCross m (fcrNegate A) = fcrCoeffNeg (fcrEvalCross m A) := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      rw [fcrNegateCons, fcrEvalCrossCons, fcrEvalCrossCons, ih, fcrCoeffNegAdd, fcrCondCoeffNeg]

/-- ★ `fcrMergeAdd_selfNeg`: a polynomial plus its own negation is all-zero-valued (the crux the additive
inverse rests on — every monomial's `c + neg c` cancels; read off `fcrEvalCross`). -/
theorem fcrMergeAddSelfNegAllZero (A : FcrNF) (hA : fcrNFSorted A = true) :
    fcrNFAllZero (fcrMergeAdd A (fcrNegate A)) = true := by
  apply fcrSortedEvalZero_allZero _ (fcrMergeAddPreservesSorted A (fcrNegate A) (fcrNegateSorted A hA))
  intro m
  rw [fcrEvalCross_mergeAdd m A (fcrNegate A), fcrEvalCross_negate m A]
  exact fcrCoeffAddNegIsZero (fcrEvalCross m A)

/-! ## Multiplying by a zero-valued polynomial, and negation through multiplication -/

theorem fcrCoeffMulZeroValuedLeft (c d : Nat × Nat) (hc : fcrCoeffIsZero c = true) :
    fcrCoeffIsZero (fcrCoeffMul c d) = true := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
  have hk : c1 = c2 := csrNatEqOfBeq c1 c2 hc
  show Nat.beq (c1 * d1 + c2 * d2) (c1 * d2 + c2 * d1) = true
  rw [hk, Nat.add_comm (c2 * d1) (c2 * d2)]
  exact csrNatBeqRefl (c2 * d2 + c2 * d1)

theorem fcrCoeffMulZeroValuedRight (c d : Nat × Nat) (hd : fcrCoeffIsZero d = true) :
    fcrCoeffIsZero (fcrCoeffMul c d) = true := by
  rw [fcrCoeffMulComm c d]; exact fcrCoeffMulZeroValuedLeft d c hd

/-- Coefficient negation passes through multiplication on the right (literally). -/
theorem fcrCoeffNegMulRight (c d : Nat × Nat) :
    fcrCoeffNeg (fcrCoeffMul c d) = fcrCoeffMul c (fcrCoeffNeg d) := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d; rfl

theorem fcrTermMulCoeffZeroAllZero (m : List Nat) (c : Nat × Nat) (hc : fcrCoeffIsZero c = true) (B : FcrNF) :
    fcrNFAllZero (fcrTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show fcrNFAllZero (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c rest)) = true
      exact fcrInsertTermAllZero _ _ _ (fcrCoeffMulZeroValuedLeft c d hc) ih

theorem fcrTermMulRightAllZero (m : List Nat) (c : Nat × Nat) (B : FcrNF) (hB : fcrNFAllZero B = true) :
    fcrNFAllZero (fcrTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      have hd : fcrCoeffIsZero d = true := csrAndTrueLeft _ _ hB
      have hrest : fcrNFAllZero rest = true := csrAndTrueRight _ _ hB
      show fcrNFAllZero (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c rest)) = true
      exact fcrInsertTermAllZero _ _ _ (fcrCoeffMulZeroValuedRight c d hd) (ih hrest)

theorem fcrMulConvolveLeftAllZero (A B : FcrNF) (hA : fcrNFAllZero A = true) :
    fcrNFAllZero (fcrMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hc : fcrCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hA' : fcrNFAllZero A' = true := csrAndTrueRight _ _ hA
      show fcrNFAllZero (fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B)) = true
      exact fcrMergeAddAllZero _ _ (fcrTermMulCoeffZeroAllZero m c hc B) (ih hA')

theorem fcrMulConvolveRightAllZero (A B : FcrNF) (hB : fcrNFAllZero B = true) :
    fcrNFAllZero (fcrMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show fcrNFAllZero (fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B)) = true
      exact fcrMergeAddAllZero _ _ (fcrTermMulRightAllZero m c B hB) ih

theorem fcrNegate_termMulLeft (m : List Nat) (c : Nat × Nat) (B : FcrNF) :
    fcrNegate (fcrTermMul m c B) = fcrTermMul m (fcrCoeffNeg c) B := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show fcrNegate (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c rest))
        = fcrInsertTerm (csrMonoMul m n, fcrCoeffMul (fcrCoeffNeg c) d) (fcrTermMul m (fcrCoeffNeg c) rest)
      rw [fcrNegate_insertTerm (csrMonoMul m n) (fcrCoeffMul c d) (fcrTermMul m c rest), ih,
          fcrCoeffNegMulLeft c d]

theorem fcrNegate_termMulRight (m : List Nat) (c : Nat × Nat) (B : FcrNF) :
    fcrNegate (fcrTermMul m c B) = fcrTermMul m c (fcrNegate B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show fcrNegate (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c rest))
        = fcrTermMul m c ((n, fcrCoeffNeg d) :: fcrNegate rest)
      rw [fcrNegate_insertTerm (csrMonoMul m n) (fcrCoeffMul c d) (fcrTermMul m c rest), ih,
          fcrTermMulCons m c n (fcrCoeffNeg d) (fcrNegate rest), fcrCoeffNegMulRight c d]

theorem fcrNegate_mulConvolveLeft (A B : FcrNF) :
    fcrNegate (fcrMulConvolve A B) = fcrMulConvolve (fcrNegate A) B := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show fcrNegate (fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B))
        = fcrMulConvolve ((m, fcrCoeffNeg c) :: fcrNegate A') B
      rw [fcrNegate_mergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B), fcrNegate_termMulLeft m c B, ih,
          fcrMulConvolveCons m (fcrCoeffNeg c) (fcrNegate A') B]

theorem fcrNegate_mulConvolveRight (A B : FcrNF) :
    fcrNegate (fcrMulConvolve A B) = fcrMulConvolve A (fcrNegate B) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show fcrNegate (fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B))
        = fcrMergeAdd (fcrTermMul m c (fcrNegate B)) (fcrMulConvolve A' (fcrNegate B))
      rw [fcrNegate_mergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B), fcrNegate_termMulRight m c B, ih]

/-! ## The decision equivalence `fcrNFEq` and its equivalence + congruence structure -/

/-- The SUBTRACTION-FREE polynomial equality: two normal forms are equal exactly when their difference has
every coefficient zero-valued.  A single-list structural check (no parallel walk, no fuel). -/
def fcrNFEq (A B : FcrNF) : Bool := fcrNFAllZero (fcrMergeAdd A (fcrNegate B))

/-- ★ `fcrNFEq` is reflexive on a sorted NF — this IS `fcrMergeAdd_selfNeg`. -/
theorem fcrNFEqRefl (A : FcrNF) (hA : fcrNFSorted A = true) : fcrNFEq A A = true :=
  fcrMergeAddSelfNegAllZero A hA

/-- Literal-equal (sorted) normal forms are `fcrNFEq`. -/
theorem fcrNFEqOfEq (A B : FcrNF) (hB : fcrNFSorted B = true) (h : A = B) : fcrNFEq A B = true := by
  rw [h]; exact fcrNFEqRefl B hB

/-- `fcrNFEq` is symmetric on sorted NFs. -/
theorem fcrNFEqSymm (A B : FcrNF) (hA : fcrNFSorted A = true) (hB : fcrNFSorted B = true)
    (h : fcrNFEq A B = true) : fcrNFEq B A = true := by
  show fcrNFAllZero (fcrMergeAdd B (fcrNegate A)) = true
  have hkey : fcrMergeAdd B (fcrNegate A) = fcrNegate (fcrMergeAdd A (fcrNegate B)) := by
    rw [fcrNegate_mergeAdd A (fcrNegate B), fcrNegateInvol B]
    exact fcrMergeAddComm B (fcrNegate A) hB (fcrNegateSorted A hA)
  rw [hkey, fcrNegatePreservesAllZero]
  exact h

/-- ★ `fcrNFEq` is transitive on sorted NFs — routed through the all-zero cancellation. -/
theorem fcrNFEqTrans (A B C : FcrNF) (hA : fcrNFSorted A = true) (hB : fcrNFSorted B = true)
    (hC : fcrNFSorted C = true) (hAB : fcrNFEq A B = true) (hBC : fcrNFEq B C = true) :
    fcrNFEq A C = true := by
  have hnegB : fcrNFSorted (fcrNegate B) = true := fcrNegateSorted B hB
  have hnegC : fcrNFSorted (fcrNegate C) = true := fcrNegateSorted C hC
  have hrearr : fcrMergeAdd (fcrMergeAdd A (fcrNegate B)) (fcrMergeAdd B (fcrNegate C))
              = fcrMergeAdd (fcrMergeAdd A (fcrNegate C)) (fcrMergeAdd B (fcrNegate B)) := by
    rw [fcrMergeAdd4Swap A (fcrNegate B) B (fcrNegate C) hnegB hB,
        fcrMergeAdd4Swap A (fcrNegate C) B (fcrNegate B) hnegC hB,
        fcrMergeAddComm (fcrNegate B) (fcrNegate C) hnegB hnegC]
  have hall : fcrNFAllZero (fcrMergeAdd (fcrMergeAdd A (fcrNegate C)) (fcrMergeAdd B (fcrNegate B))) = true := by
    rw [← hrearr]; exact fcrMergeAddAllZero _ _ hAB hBC
  exact fcrMergeAddAllZeroCancel (fcrMergeAdd A (fcrNegate C)) (fcrMergeAdd B (fcrNegate B))
    (fcrMergeAddPreservesSorted A (fcrNegate C) hnegC) hall (fcrMergeAddSelfNegAllZero B hB)

/-- ★ `fcrNFEq` respects the additive merge. -/
theorem fcrNFEqMergeCongr (A A' B B' : FcrNF) (hA' : fcrNFSorted A' = true) (hB : fcrNFSorted B = true)
    (hAA' : fcrNFEq A A' = true) (hBB' : fcrNFEq B B' = true) :
    fcrNFEq (fcrMergeAdd A B) (fcrMergeAdd A' B') = true := by
  show fcrNFAllZero (fcrMergeAdd (fcrMergeAdd A B) (fcrNegate (fcrMergeAdd A' B'))) = true
  rw [fcrNegate_mergeAdd A' B', fcrMergeAdd4Swap A B (fcrNegate A') (fcrNegate B') hB (fcrNegateSorted A' hA')]
  exact fcrMergeAddAllZero _ _ hAA' hBB'

/-- ★ `fcrNFEq` respects the multiplicative convolution (via distributivity + the zero-poly product laws +
transitivity — no eval-convolution homomorphism needed). -/
theorem fcrNFEqMulCongr (A A' B B' : FcrNF) (hAA' : fcrNFEq A A' = true) (hBB' : fcrNFEq B B' = true) :
    fcrNFEq (fcrMulConvolve A B) (fcrMulConvolve A' B') = true := by
  have step1 : fcrNFEq (fcrMulConvolve A B) (fcrMulConvolve A' B) = true := by
    show fcrNFAllZero (fcrMergeAdd (fcrMulConvolve A B) (fcrNegate (fcrMulConvolve A' B))) = true
    rw [fcrNegate_mulConvolveLeft A' B, ← fcrMulConvolve_rightDistrib A (fcrNegate A') B]
    exact fcrMulConvolveLeftAllZero (fcrMergeAdd A (fcrNegate A')) B hAA'
  have step2 : fcrNFEq (fcrMulConvolve A' B) (fcrMulConvolve A' B') = true := by
    show fcrNFAllZero (fcrMergeAdd (fcrMulConvolve A' B) (fcrNegate (fcrMulConvolve A' B'))) = true
    rw [fcrNegate_mulConvolveRight A' B', ← fcrMulConvolve_leftDistrib A' B (fcrNegate B')]
    exact fcrMulConvolveRightAllZero A' (fcrMergeAdd B (fcrNegate B')) hBB'
  exact fcrNFEqTrans (fcrMulConvolve A B) (fcrMulConvolve A' B) (fcrMulConvolve A' B')
    (fcrMulConvolveSorted A B) (fcrMulConvolveSorted A' B) (fcrMulConvolveSorted A' B') step1 step2

/-- ★ `fcrNFEq` respects negation. -/
theorem fcrNFEqNegCongr (A A' : FcrNF) (h : fcrNFEq A A' = true) :
    fcrNFEq (fcrNegate A) (fcrNegate A') = true := by
  show fcrNFAllZero (fcrMergeAdd (fcrNegate A) (fcrNegate (fcrNegate A'))) = true
  rw [fcrNegateInvol A']
  have hkey : fcrMergeAdd (fcrNegate A) A' = fcrNegate (fcrMergeAdd A (fcrNegate A')) := by
    rw [fcrNegate_mergeAdd A (fcrNegate A'), fcrNegateInvol A']
  rw [hkey, fcrNegatePreservesAllZero]
  exact h

/-- An all-zero (sorted) NF is `fcrNFEq` to the empty NF. -/
theorem fcrNFEqNil (X : FcrNF) (hX : fcrNFSorted X = true) (hall : fcrNFAllZero X = true) :
    fcrNFEq X [] = true := by
  show fcrNFAllZero (fcrMergeAdd X (fcrNegate [])) = true
  rw [show fcrNegate ([] : FcrNF) = [] from rfl, fcrMergeAddNilRight X hX]
  exact hall

/-! ## The free commutative-ring tree carrier and its normal form -/

/-- ★ The free commutative-ring tree carrier: colour-tagged generators plus the additive unit `0`, the
multiplicative unit `1`, binary addition and multiplication, and — the new content — the unary additive
inverse `negOp`. -/
inductive FcrTree where
  /-- a colour-tagged generator (variable). -/
  | gen (colour : Nat)
  /-- the additive unit `0`. -/
  | zeroOp
  /-- the multiplicative unit `1`. -/
  | oneOp
  /-- binary addition. -/
  | addOp : FcrTree → FcrTree → FcrTree
  /-- binary multiplication. -/
  | mulOp : FcrTree → FcrTree → FcrTree
  /-- the unary additive inverse (negation). -/
  | negOp : FcrTree → FcrTree

/-- ★ normalize a tree to its polynomial normal form (sorted terms, `(pos, neg)` integer coefficients). -/
def fcrNormalize : FcrTree → FcrNF
  | .gen colour => [([colour], (1, 0))]
  | .zeroOp => []
  | .oneOp => [([], (1, 0))]
  | .addOp l r => fcrMergeAdd (fcrNormalize l) (fcrNormalize r)
  | .mulOp l r => fcrMulConvolve (fcrNormalize l) (fcrNormalize r)
  | .negOp a => fcrNegate (fcrNormalize a)

theorem fcrNormalize_gen (c : Nat) : fcrNormalize (FcrTree.gen c) = [([c], (1, 0))] := rfl
theorem fcrNegateMonoSorted (A : FcrNF) (hA : fcrNFMonoSorted A = true) :
    fcrNFMonoSorted (fcrNegate A) = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      have hm : csrMonoSorted m = true := csrAndTrueLeft _ _ hA
      have hrest : fcrNFMonoSorted rest = true := csrAndTrueRight _ _ hA
      rw [fcrNegateCons, fcrNFMonoSortedCons]
      exact csrAndIntro _ _ hm (ih hrest)
theorem fcrNormalizeSorted (t : FcrTree) : fcrNFSorted (fcrNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | addOp l r _ ihr => exact fcrMergeAddPreservesSorted (fcrNormalize l) (fcrNormalize r) ihr
  | mulOp l r _ _ => exact fcrMulConvolveSorted (fcrNormalize l) (fcrNormalize r)
  | negOp a ih => exact fcrNegateSorted (fcrNormalize a) ih
theorem fcrNormalizeMonoSorted (t : FcrTree) : fcrNFMonoSorted (fcrNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | addOp l r ihl ihr => exact fcrMergeAddMonoSorted (fcrNormalize l) (fcrNormalize r) ihl ihr
  | mulOp l r ihl ihr => exact fcrMulConvolveMonoSorted (fcrNormalize l) (fcrNormalize r) ihl ihr
  | negOp a ih => exact fcrNegateMonoSorted (fcrNormalize a) ih

/-- rfl smokes for the normal form. -/
theorem fcrNormalize_zero_smoke : fcrNormalize FcrTree.zeroOp = [] := rfl
theorem fcrNormalize_one_smoke : fcrNormalize FcrTree.oneOp = [([], (1, 0))] := rfl
theorem fcrNormalize_negGen_smoke :
    fcrNormalize (FcrTree.negOp (FcrTree.gen 0)) = [([0], (0, 1))] := rfl

/-! ## The commutative-ring tree convertibility -/

/-- ★ The free convertibility of the `{+, *, 0, 1, neg}` signature over colour-tagged generators, closed under
the commutative-ring laws: the additive ABELIAN GROUP (associativity, commutativity, right unit, and the new
`addNegInverse`), the commutative multiplicative monoid (associativity, commutativity, right unit),
distributivity and right-annihilation, the full congruences `addCongr` / `mulCongr` / `negCongr`, and
`refl` / `symm` / `trans`. -/
inductive CommRingTreeConv : FcrTree → FcrTree → Prop where
  | addAssoc (a b c : FcrTree) :
      CommRingTreeConv (FcrTree.addOp (FcrTree.addOp a b) c) (FcrTree.addOp a (FcrTree.addOp b c))
  | addComm (a b : FcrTree) : CommRingTreeConv (FcrTree.addOp a b) (FcrTree.addOp b a)
  | addZero (a : FcrTree) : CommRingTreeConv (FcrTree.addOp a FcrTree.zeroOp) a
  /-- ★ the additive inverse — the whole new content: `a + neg a ≈ 0`. -/
  | addNegInverse (a : FcrTree) :
      CommRingTreeConv (FcrTree.addOp a (FcrTree.negOp a)) FcrTree.zeroOp
  | mulAssoc (a b c : FcrTree) :
      CommRingTreeConv (FcrTree.mulOp (FcrTree.mulOp a b) c) (FcrTree.mulOp a (FcrTree.mulOp b c))
  | mulComm (a b : FcrTree) : CommRingTreeConv (FcrTree.mulOp a b) (FcrTree.mulOp b a)
  | mulOne (a : FcrTree) : CommRingTreeConv (FcrTree.mulOp a FcrTree.oneOp) a
  | distribLeft (a b c : FcrTree) :
      CommRingTreeConv (FcrTree.mulOp a (FcrTree.addOp b c))
        (FcrTree.addOp (FcrTree.mulOp a b) (FcrTree.mulOp a c))
  | annihilRight (a : FcrTree) : CommRingTreeConv (FcrTree.mulOp a FcrTree.zeroOp) FcrTree.zeroOp
  | addCongr {leftOld leftNew rightOld rightNew : FcrTree} :
      CommRingTreeConv leftOld leftNew → CommRingTreeConv rightOld rightNew →
      CommRingTreeConv (FcrTree.addOp leftOld rightOld) (FcrTree.addOp leftNew rightNew)
  | mulCongr {leftOld leftNew rightOld rightNew : FcrTree} :
      CommRingTreeConv leftOld leftNew → CommRingTreeConv rightOld rightNew →
      CommRingTreeConv (FcrTree.mulOp leftOld rightOld) (FcrTree.mulOp leftNew rightNew)
  | negCongr {innerOld innerNew : FcrTree} :
      CommRingTreeConv innerOld innerNew →
      CommRingTreeConv (FcrTree.negOp innerOld) (FcrTree.negOp innerNew)
  | refl (t : FcrTree) : CommRingTreeConv t t
  | symm {s t : FcrTree} : CommRingTreeConv s t → CommRingTreeConv t s
  | trans {s t u : FcrTree} : CommRingTreeConv s t → CommRingTreeConv t u → CommRingTreeConv s u

/-! ## Soundness: convertible ⟹ `fcrNFEq` normal forms -/

/-- ★ Soundness — convertible trees have `fcrNFEq` normal forms.  Every core semiring law is a LITERAL
normal-form equality (discharged by `fcrNFEqOfEq` off the merge/convolve algebra); the additive inverse falls
to `fcrMergeAdd_selfNeg` (`fcrNFEqNil`), and the congruences / equivalence to the `fcrNFEq` structure. -/
theorem fcrNormalize_respects {s t : FcrTree} (conv : CommRingTreeConv s t) :
    fcrNFEq (fcrNormalize s) (fcrNormalize t) = true := by
  induction conv with
  | addAssoc a b c =>
      exact fcrNFEqOfEq _ _
        (fcrMergeAddPreservesSorted _ _ (fcrMergeAddPreservesSorted _ _ (fcrNormalizeSorted c)))
        (fcrMergeAddAssoc (fcrNormalize a) (fcrNormalize b) (fcrNormalize c))
  | addComm a b =>
      exact fcrNFEqOfEq _ _
        (fcrMergeAddPreservesSorted _ _ (fcrNormalizeSorted a))
        (fcrMergeAddComm (fcrNormalize a) (fcrNormalize b) (fcrNormalizeSorted a) (fcrNormalizeSorted b))
  | addZero a =>
      exact fcrNFEqOfEq _ _ (fcrNormalizeSorted a)
        (fcrMergeAddNilRight (fcrNormalize a) (fcrNormalizeSorted a))
  | addNegInverse a =>
      exact fcrNFEqNil _
        (fcrMergeAddPreservesSorted _ _ (fcrNegateSorted _ (fcrNormalizeSorted a)))
        (fcrMergeAddSelfNegAllZero (fcrNormalize a) (fcrNormalizeSorted a))
  | mulAssoc a b c =>
      exact fcrNFEqOfEq _ _
        (fcrMulConvolveSorted _ _)
        (fcrMulConvolveAssoc (fcrNormalize a) (fcrNormalize b) (fcrNormalize c))
  | mulComm a b =>
      exact fcrNFEqOfEq _ _ (fcrMulConvolveSorted _ _)
        (fcrMulConvolveComm (fcrNormalize a) (fcrNormalize b)
          (fcrNormalizeSorted a) (fcrNormalizeMonoSorted a) (fcrNormalizeMonoSorted b))
  | mulOne a =>
      exact fcrNFEqOfEq _ _ (fcrNormalizeSorted a)
        (fcrMulConvolveUnit (fcrNormalize a) (fcrNormalizeSorted a))
  | distribLeft a b c =>
      exact fcrNFEqOfEq _ _
        (fcrMergeAddPreservesSorted _ _ (fcrMulConvolveSorted _ _))
        (fcrMulConvolve_leftDistrib (fcrNormalize a) (fcrNormalize b) (fcrNormalize c))
  | annihilRight a =>
      exact fcrNFEqOfEq _ _ rfl (fcrMulConvolveAnnihil (fcrNormalize a))
  | @addCongr lo ln ro rn _ _ ihl ihr =>
      exact fcrNFEqMergeCongr (fcrNormalize lo) (fcrNormalize ln) (fcrNormalize ro) (fcrNormalize rn)
        (fcrNormalizeSorted ln) (fcrNormalizeSorted ro) ihl ihr
  | @mulCongr lo ln ro rn _ _ ihl ihr =>
      exact fcrNFEqMulCongr (fcrNormalize lo) (fcrNormalize ln) (fcrNormalize ro) (fcrNormalize rn) ihl ihr
  | @negCongr ao an _ ih =>
      exact fcrNFEqNegCongr (fcrNormalize ao) (fcrNormalize an) ih
  | refl t => exact fcrNFEqRefl (fcrNormalize t) (fcrNormalizeSorted t)
  | @symm s t _ ih =>
      exact fcrNFEqSymm (fcrNormalize s) (fcrNormalize t)
        (fcrNormalizeSorted s) (fcrNormalizeSorted t) ih
  | @trans s t u _ _ ih1 ih2 =>
      exact fcrNFEqTrans (fcrNormalize s) (fcrNormalize t) (fcrNormalize u)
        (fcrNormalizeSorted s) (fcrNormalizeSorted t) (fcrNormalizeSorted u) ih1 ih2

/-! ## Derived ring-convertibility lemmas (for the rebuild reification) -/

theorem fcrConvAddZeroLeft (a : FcrTree) : CommRingTreeConv (FcrTree.addOp FcrTree.zeroOp a) a :=
  (CommRingTreeConv.addComm FcrTree.zeroOp a).trans (CommRingTreeConv.addZero a)
theorem fcrConvMulOneLeft (a : FcrTree) : CommRingTreeConv (FcrTree.mulOp FcrTree.oneOp a) a :=
  (CommRingTreeConv.mulComm FcrTree.oneOp a).trans (CommRingTreeConv.mulOne a)
theorem fcrConvAnnihilLeft (a : FcrTree) :
    CommRingTreeConv (FcrTree.mulOp FcrTree.zeroOp a) FcrTree.zeroOp :=
  (CommRingTreeConv.mulComm FcrTree.zeroOp a).trans (CommRingTreeConv.annihilRight a)
theorem fcrConvDistribRight (a b c : FcrTree) :
    CommRingTreeConv (FcrTree.mulOp (FcrTree.addOp a b) c)
      (FcrTree.addOp (FcrTree.mulOp a c) (FcrTree.mulOp b c)) :=
  (CommRingTreeConv.mulComm (FcrTree.addOp a b) c).trans
    ((CommRingTreeConv.distribLeft c a b).trans
      (CommRingTreeConv.addCongr (CommRingTreeConv.mulComm c a) (CommRingTreeConv.mulComm c b)))
theorem fcrConvAddSwap13 (x y z : FcrTree) :
    CommRingTreeConv (FcrTree.addOp x (FcrTree.addOp y z)) (FcrTree.addOp y (FcrTree.addOp x z)) :=
  (CommRingTreeConv.symm (CommRingTreeConv.addAssoc x y z)).trans
    ((CommRingTreeConv.addCongr (CommRingTreeConv.addComm x y) (CommRingTreeConv.refl z)).trans
      (CommRingTreeConv.addAssoc y x z))
theorem fcrConvMulSwap13 (x y z : FcrTree) :
    CommRingTreeConv (FcrTree.mulOp x (FcrTree.mulOp y z)) (FcrTree.mulOp y (FcrTree.mulOp x z)) :=
  (CommRingTreeConv.symm (CommRingTreeConv.mulAssoc x y z)).trans
    ((CommRingTreeConv.mulCongr (CommRingTreeConv.mulComm x y) (CommRingTreeConv.refl z)).trans
      (CommRingTreeConv.mulAssoc y x z))
theorem fcrConvAddMiddleFour (a b c d : FcrTree) :
    CommRingTreeConv (FcrTree.addOp (FcrTree.addOp a b) (FcrTree.addOp c d))
      (FcrTree.addOp (FcrTree.addOp a c) (FcrTree.addOp b d)) :=
  (CommRingTreeConv.addAssoc a b (FcrTree.addOp c d)).trans
    ((CommRingTreeConv.addCongr (CommRingTreeConv.refl a)
        (CommRingTreeConv.symm (CommRingTreeConv.addAssoc b c d))).trans
      ((CommRingTreeConv.addCongr (CommRingTreeConv.refl a)
          (CommRingTreeConv.addCongr (CommRingTreeConv.addComm b c) (CommRingTreeConv.refl d))).trans
        ((CommRingTreeConv.addCongr (CommRingTreeConv.refl a) (CommRingTreeConv.addAssoc c b d)).trans
          (CommRingTreeConv.symm (CommRingTreeConv.addAssoc a c (FcrTree.addOp b d))))))
theorem fcrConvAddNegInverseLeft (a : FcrTree) :
    CommRingTreeConv (FcrTree.addOp (FcrTree.negOp a) a) FcrTree.zeroOp :=
  (CommRingTreeConv.addComm (FcrTree.negOp a) a).trans (CommRingTreeConv.addNegInverse a)

/-- Uniqueness of additive inverses: if `z + x ≈ 0` and `z + y ≈ 0` then `x ≈ y`. -/
theorem fcrConvInvUnique (z x y : FcrTree)
    (hx : CommRingTreeConv (FcrTree.addOp z x) FcrTree.zeroOp)
    (hy : CommRingTreeConv (FcrTree.addOp z y) FcrTree.zeroOp) : CommRingTreeConv x y :=
  (CommRingTreeConv.symm (CommRingTreeConv.addZero x)).trans
    ((CommRingTreeConv.addCongr (CommRingTreeConv.refl x) (CommRingTreeConv.symm hy)).trans
      ((CommRingTreeConv.symm (CommRingTreeConv.addAssoc x z y)).trans
        ((CommRingTreeConv.addCongr ((CommRingTreeConv.addComm x z).trans hx)
            (CommRingTreeConv.refl y)).trans
          (fcrConvAddZeroLeft y))))

/-- `neg 0 ≈ 0`. -/
theorem fcrConvNegZero : CommRingTreeConv (FcrTree.negOp FcrTree.zeroOp) FcrTree.zeroOp :=
  (CommRingTreeConv.symm (fcrConvAddZeroLeft (FcrTree.negOp FcrTree.zeroOp))).trans
    (CommRingTreeConv.addNegInverse FcrTree.zeroOp)

/-- `neg (neg a) ≈ a`. -/
theorem fcrConvNegNeg (a : FcrTree) : CommRingTreeConv (FcrTree.negOp (FcrTree.negOp a)) a :=
  fcrConvInvUnique (FcrTree.negOp a) (FcrTree.negOp (FcrTree.negOp a)) a
    (CommRingTreeConv.addNegInverse (FcrTree.negOp a)) (fcrConvAddNegInverseLeft a)

/-- `a * neg b ≈ neg (a * b)`. -/
theorem fcrConvMulNegRight (a b : FcrTree) :
    CommRingTreeConv (FcrTree.mulOp a (FcrTree.negOp b)) (FcrTree.negOp (FcrTree.mulOp a b)) :=
  fcrConvInvUnique (FcrTree.mulOp a b) (FcrTree.mulOp a (FcrTree.negOp b))
    (FcrTree.negOp (FcrTree.mulOp a b))
    ((CommRingTreeConv.symm (CommRingTreeConv.distribLeft a b (FcrTree.negOp b))).trans
      ((CommRingTreeConv.mulCongr (CommRingTreeConv.refl a) (CommRingTreeConv.addNegInverse b)).trans
        (CommRingTreeConv.annihilRight a)))
    (CommRingTreeConv.addNegInverse (FcrTree.mulOp a b))

/-- `neg a * b ≈ neg (a * b)`. -/
theorem fcrConvMulNegLeft (a b : FcrTree) :
    CommRingTreeConv (FcrTree.mulOp (FcrTree.negOp a) b) (FcrTree.negOp (FcrTree.mulOp a b)) :=
  (CommRingTreeConv.mulComm (FcrTree.negOp a) b).trans
    ((fcrConvMulNegRight b a).trans (CommRingTreeConv.negCongr (CommRingTreeConv.mulComm b a)))

/-- `neg a * neg b ≈ a * b`. -/
theorem fcrConvMulNegNeg (a b : FcrTree) :
    CommRingTreeConv (FcrTree.mulOp (FcrTree.negOp a) (FcrTree.negOp b)) (FcrTree.mulOp a b) :=
  (fcrConvMulNegLeft a (FcrTree.negOp b)).trans
    ((CommRingTreeConv.negCongr (fcrConvMulNegRight a b)).trans (fcrConvNegNeg (FcrTree.mulOp a b)))

/-- `neg (a + b) ≈ neg a + neg b` (inverse homomorphism; the group is abelian). -/
theorem fcrConvNegAdd (a b : FcrTree) :
    CommRingTreeConv (FcrTree.negOp (FcrTree.addOp a b))
      (FcrTree.addOp (FcrTree.negOp a) (FcrTree.negOp b)) :=
  CommRingTreeConv.symm
    (fcrConvInvUnique (FcrTree.addOp a b) (FcrTree.addOp (FcrTree.negOp a) (FcrTree.negOp b))
      (FcrTree.negOp (FcrTree.addOp a b))
      ((fcrConvAddMiddleFour a b (FcrTree.negOp a) (FcrTree.negOp b)).trans
        ((CommRingTreeConv.addCongr (CommRingTreeConv.addNegInverse a)
            (CommRingTreeConv.addNegInverse b)).trans (CommRingTreeConv.addZero FcrTree.zeroOp)))
      (CommRingTreeConv.addNegInverse (FcrTree.addOp a b)))

/-- Product of two sums expands to four products. -/
theorem fcrConvMulAddAdd (a b c d : FcrTree) :
    CommRingTreeConv (FcrTree.mulOp (FcrTree.addOp a b) (FcrTree.addOp c d))
      (FcrTree.addOp (FcrTree.addOp (FcrTree.mulOp a c) (FcrTree.mulOp a d))
        (FcrTree.addOp (FcrTree.mulOp b c) (FcrTree.mulOp b d))) :=
  (fcrConvDistribRight a b (FcrTree.addOp c d)).trans
    (CommRingTreeConv.addCongr (CommRingTreeConv.distribLeft a c d) (CommRingTreeConv.distribLeft b c d))

/-! ## Scale trees (coefficient-many copies) -/

/-- `n` copies of a tree added together (`0 ↦ zeroOp`). -/
def fcrScaleTree (mono : FcrTree) : Nat → FcrTree
  | 0 => FcrTree.zeroOp
  | Nat.succ k => FcrTree.addOp mono (fcrScaleTree mono k)
theorem fcrScaleTreeCongr {mono1 mono2 : FcrTree} (h : CommRingTreeConv mono1 mono2) (n : Nat) :
    CommRingTreeConv (fcrScaleTree mono1 n) (fcrScaleTree mono2 n) := by
  induction n with
  | zero => exact CommRingTreeConv.refl FcrTree.zeroOp
  | succ k ih => exact CommRingTreeConv.addCongr h ih
theorem fcrScaleAdd (mono : FcrTree) (a b : Nat) :
    CommRingTreeConv (fcrScaleTree mono (a + b))
      (FcrTree.addOp (fcrScaleTree mono a) (fcrScaleTree mono b)) := by
  induction b with
  | zero => exact (CommRingTreeConv.addZero (fcrScaleTree mono a)).symm
  | succ k ih =>
      exact (CommRingTreeConv.addCongr (CommRingTreeConv.refl mono) ih).trans
        (fcrConvAddSwap13 mono (fcrScaleTree mono a) (fcrScaleTree mono k))
theorem fcrScaleTreeMulLeft (p q : FcrTree) (c : Nat) :
    CommRingTreeConv (fcrScaleTree (FcrTree.mulOp p q) c) (FcrTree.mulOp (fcrScaleTree p c) q) := by
  induction c with
  | zero => exact (fcrConvAnnihilLeft q).symm
  | succ k ih =>
      exact (CommRingTreeConv.addCongr (CommRingTreeConv.refl (FcrTree.mulOp p q)) ih).trans
        (fcrConvDistribRight p (fcrScaleTree p k) q).symm
theorem fcrScaleTreeMulRight (p q : FcrTree) (d : Nat) :
    CommRingTreeConv (fcrScaleTree (FcrTree.mulOp p q) d) (FcrTree.mulOp p (fcrScaleTree q d)) := by
  induction d with
  | zero => exact (CommRingTreeConv.annihilRight p).symm
  | succ k ih =>
      exact (CommRingTreeConv.addCongr (CommRingTreeConv.refl (FcrTree.mulOp p q)) ih).trans
        (CommRingTreeConv.distribLeft p q (fcrScaleTree q k)).symm
theorem fcrScaleTreeMulCoeff (X : FcrTree) (c d : Nat) :
    CommRingTreeConv (fcrScaleTree X (c * d)) (fcrScaleTree (fcrScaleTree X d) c) := by
  induction c with
  | zero => rw [Nat.zero_mul d]; exact CommRingTreeConv.refl FcrTree.zeroOp
  | succ k ih =>
      rw [Nat.succ_mul k d]
      exact (fcrScaleAdd X (k * d) d).trans
        ((CommRingTreeConv.addCongr ih (CommRingTreeConv.refl (fcrScaleTree X d))).trans
          (CommRingTreeConv.addComm (fcrScaleTree (fcrScaleTree X d) k) (fcrScaleTree X d)))
/-- Product of two scaled trees: `(a·X) * (b·Y) ≈ (a*b)·(X*Y)`. -/
theorem fcrScaleTreeMulBoth (X Y : FcrTree) (a b : Nat) :
    CommRingTreeConv (fcrScaleTree (FcrTree.mulOp X Y) (a * b))
      (FcrTree.mulOp (fcrScaleTree X a) (fcrScaleTree Y b)) :=
  ((fcrScaleTreeMulCoeff (FcrTree.mulOp X Y) a b).trans
    ((fcrScaleTreeCongr (fcrScaleTreeMulRight X Y b) a).trans
      (fcrScaleTreeMulLeft X (fcrScaleTree Y b) a)))

/-! ## The monomial tree and its multiplicative reification -/

def fcrMonoToTree : List Nat → FcrTree
  | [] => FcrTree.oneOp
  | c :: rest => FcrTree.mulOp (FcrTree.gen c) (fcrMonoToTree rest)
theorem fcrMonoToTreeInsertSorted (v : Nat) (xs : List Nat) :
    CommRingTreeConv (fcrMonoToTree (insertSorted v xs))
      (FcrTree.mulOp (FcrTree.gen v) (fcrMonoToTree xs)) := by
  induction xs with
  | nil => exact CommRingTreeConv.refl (FcrTree.mulOp (FcrTree.gen v) FcrTree.oneOp)
  | cons a rest ih =>
      cases hva : natBle v a with
      | true =>
          rw [insertSortedConsTrue v a rest hva]
          exact CommRingTreeConv.refl _
      | false =>
          rw [insertSortedConsFalse v a rest hva]
          show CommRingTreeConv (FcrTree.mulOp (FcrTree.gen a) (fcrMonoToTree (insertSorted v rest)))
            (FcrTree.mulOp (FcrTree.gen v) (FcrTree.mulOp (FcrTree.gen a) (fcrMonoToTree rest)))
          exact (CommRingTreeConv.mulCongr (CommRingTreeConv.refl (FcrTree.gen a)) ih).trans
            (fcrConvMulSwap13 (FcrTree.gen a) (FcrTree.gen v) (fcrMonoToTree rest))
theorem fcrMonoToTreeInsertMany (n m : List Nat) :
    CommRingTreeConv (fcrMonoToTree (insertMany n m))
      (FcrTree.mulOp (fcrMonoToTree n) (fcrMonoToTree m)) := by
  induction n with
  | nil => exact (fcrConvMulOneLeft (fcrMonoToTree m)).symm
  | cons a n' ih =>
      show CommRingTreeConv (fcrMonoToTree (insertSorted a (insertMany n' m)))
        (FcrTree.mulOp (FcrTree.mulOp (FcrTree.gen a) (fcrMonoToTree n')) (fcrMonoToTree m))
      exact (fcrMonoToTreeInsertSorted a (insertMany n' m)).trans
        ((CommRingTreeConv.mulCongr (CommRingTreeConv.refl (FcrTree.gen a)) ih).trans
          (CommRingTreeConv.symm
            (CommRingTreeConv.mulAssoc (FcrTree.gen a) (fcrMonoToTree n') (fcrMonoToTree m))))
theorem fcrMonoToTreeMonoMul (m n : List Nat) :
    CommRingTreeConv (fcrMonoToTree (csrMonoMul m n))
      (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n)) := by
  show CommRingTreeConv (fcrMonoToTree (insertMany n m))
    (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n))
  exact (fcrMonoToTreeInsertMany n m).trans
    (CommRingTreeConv.mulComm (fcrMonoToTree n) (fcrMonoToTree m))

/-! ## The term tree (a `(pos, neg)` coefficient applied to a monomial) and its reification -/

/-- The tree of a single term `(mono, (p, n))`: `p` copies of the monomial tree added, minus `n` copies (via
`negOp`).  This is the integer scale of the monomial. -/
def fcrTermToTree (mono : List Nat) : (Nat × Nat) → FcrTree
  | (p, n) => FcrTree.addOp (fcrScaleTree (fcrMonoToTree mono) p)
                (fcrScaleTree (FcrTree.negOp (fcrMonoToTree mono)) n)
theorem fcrTermToTreeEq (mono : List Nat) (p n : Nat) :
    fcrTermToTree mono (p, n) = FcrTree.addOp (fcrScaleTree (fcrMonoToTree mono) p)
      (fcrScaleTree (FcrTree.negOp (fcrMonoToTree mono)) n) := rfl

/-- The term tree distributes over coefficient addition. -/
theorem fcrTermToTreeAdd (mono : List Nat) (e c : Nat × Nat) :
    CommRingTreeConv (fcrTermToTree mono (fcrCoeffAdd e c))
      (FcrTree.addOp (fcrTermToTree mono e) (fcrTermToTree mono c)) := by
  obtain ⟨e1, e2⟩ := e; obtain ⟨c1, c2⟩ := c
  exact (CommRingTreeConv.addCongr (fcrScaleAdd (fcrMonoToTree mono) e1 c1)
      (fcrScaleAdd (FcrTree.negOp (fcrMonoToTree mono)) e2 c2)).trans
    (fcrConvAddMiddleFour (fcrScaleTree (fcrMonoToTree mono) e1) (fcrScaleTree (fcrMonoToTree mono) c1)
      (fcrScaleTree (FcrTree.negOp (fcrMonoToTree mono)) e2)
      (fcrScaleTree (FcrTree.negOp (fcrMonoToTree mono)) c2))

/-- ★ The term-product reification — the crux of completeness, where negation passes through multiplication:
`termToTree (m ⊎ n') (c1 * c2) ≈ (termToTree m c1) * (termToTree n' c2)`.  The mul side expands to four scaled
products (`fcrConvMulAddAdd`), each collapsed by `fcrScaleTreeMulBoth` with `x·neg y ≈ neg(x·y)` / `neg·neg`;
the term side re-associates the two integer scales onto the merged monomial tree. -/
theorem fcrTermToTreeMul (m : List Nat) (c1 : Nat × Nat) (n' : List Nat) (c2 : Nat × Nat) :
    CommRingTreeConv (fcrTermToTree (csrMonoMul m n') (fcrCoeffMul c1 c2))
      (FcrTree.mulOp (fcrTermToTree m c1) (fcrTermToTree n' c2)) := by
  obtain ⟨p1, q1⟩ := c1; obtain ⟨p2, q2⟩ := c2
  -- the four collapsed scaled products, in terms of MN := M * N and nMN := neg MN
  have hm1 : CommRingTreeConv
      (FcrTree.mulOp (fcrScaleTree (fcrMonoToTree m) p1) (fcrScaleTree (fcrMonoToTree n') p2))
      (fcrScaleTree (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (p1 * p2)) :=
    (fcrScaleTreeMulBoth (fcrMonoToTree m) (fcrMonoToTree n') p1 p2).symm
  have hm2 : CommRingTreeConv
      (FcrTree.mulOp (fcrScaleTree (fcrMonoToTree m) p1)
        (fcrScaleTree (FcrTree.negOp (fcrMonoToTree n')) q2))
      (fcrScaleTree (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (p1 * q2)) :=
    (fcrScaleTreeMulBoth (fcrMonoToTree m) (FcrTree.negOp (fcrMonoToTree n')) p1 q2).symm.trans
      (fcrScaleTreeCongr (fcrConvMulNegRight (fcrMonoToTree m) (fcrMonoToTree n')) (p1 * q2))
  have hm3 : CommRingTreeConv
      (FcrTree.mulOp (fcrScaleTree (FcrTree.negOp (fcrMonoToTree m)) q1) (fcrScaleTree (fcrMonoToTree n') p2))
      (fcrScaleTree (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (q1 * p2)) :=
    (fcrScaleTreeMulBoth (FcrTree.negOp (fcrMonoToTree m)) (fcrMonoToTree n') q1 p2).symm.trans
      (fcrScaleTreeCongr (fcrConvMulNegLeft (fcrMonoToTree m) (fcrMonoToTree n')) (q1 * p2))
  have hm4 : CommRingTreeConv
      (FcrTree.mulOp (fcrScaleTree (FcrTree.negOp (fcrMonoToTree m)) q1)
        (fcrScaleTree (FcrTree.negOp (fcrMonoToTree n')) q2))
      (fcrScaleTree (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (q1 * q2)) :=
    (fcrScaleTreeMulBoth (FcrTree.negOp (fcrMonoToTree m)) (FcrTree.negOp (fcrMonoToTree n')) q1 q2).symm.trans
      (fcrScaleTreeCongr (fcrConvMulNegNeg (fcrMonoToTree m) (fcrMonoToTree n')) (q1 * q2))
  -- the mul side reaches the canonical middle C
  have hRHStoC : CommRingTreeConv
      (FcrTree.mulOp (fcrTermToTree m (p1, q1)) (fcrTermToTree n' (p2, q2)))
      (FcrTree.addOp
        (FcrTree.addOp (fcrScaleTree (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (p1 * p2))
          (fcrScaleTree (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (p1 * q2)))
        (FcrTree.addOp (fcrScaleTree (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (q1 * p2))
          (fcrScaleTree (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (q1 * q2)))) :=
    (fcrConvMulAddAdd (fcrScaleTree (fcrMonoToTree m) p1) (fcrScaleTree (FcrTree.negOp (fcrMonoToTree m)) q1)
        (fcrScaleTree (fcrMonoToTree n') p2) (fcrScaleTree (FcrTree.negOp (fcrMonoToTree n')) q2)).trans
      (CommRingTreeConv.addCongr (CommRingTreeConv.addCongr hm1 hm2) (CommRingTreeConv.addCongr hm3 hm4))
  -- the term side reaches the same canonical middle C
  have hLHStoC : CommRingTreeConv
      (fcrTermToTree (csrMonoMul m n') (p1 * p2 + q1 * q2, p1 * q2 + q1 * p2))
      (FcrTree.addOp
        (FcrTree.addOp (fcrScaleTree (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (p1 * p2))
          (fcrScaleTree (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (p1 * q2)))
        (FcrTree.addOp (fcrScaleTree (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (q1 * p2))
          (fcrScaleTree (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (q1 * q2)))) :=
    (CommRingTreeConv.addCongr
        (fcrScaleTreeCongr (fcrMonoToTreeMonoMul m n') (p1 * p2 + q1 * q2))
        (fcrScaleTreeCongr (CommRingTreeConv.negCongr (fcrMonoToTreeMonoMul m n')) (p1 * q2 + q1 * p2))).trans
      ((CommRingTreeConv.addCongr
          (fcrScaleAdd (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (p1 * p2) (q1 * q2))
          (fcrScaleAdd (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (p1 * q2) (q1 * p2))).trans
        ((fcrConvAddMiddleFour
            (fcrScaleTree (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (p1 * p2))
            (fcrScaleTree (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (q1 * q2))
            (fcrScaleTree (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (p1 * q2))
            (fcrScaleTree (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (q1 * p2))).trans
          (CommRingTreeConv.addCongr (CommRingTreeConv.refl _)
            (CommRingTreeConv.addComm
              (fcrScaleTree (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n')) (q1 * q2))
              (fcrScaleTree (FcrTree.negOp (FcrTree.mulOp (fcrMonoToTree m) (fcrMonoToTree n'))) (q1 * p2))))))
  exact hLHStoC.trans hRHStoC.symm

/-! ## The normal-form rebuild `fcrCombOfNF` and its convertibility algebra -/

/-- Rebuild a canonical tree from a normal form. -/
def fcrCombOfNF : FcrNF → FcrTree
  | [] => FcrTree.zeroOp
  | (m, c) :: rest => FcrTree.addOp (fcrTermToTree m c) (fcrCombOfNF rest)
theorem fcrCombOfNFCons (m : List Nat) (c : Nat × Nat) (rest : FcrNF) :
    fcrCombOfNF ((m, c) :: rest) = FcrTree.addOp (fcrTermToTree m c) (fcrCombOfNF rest) := rfl

theorem fcrCombInsertTerm (m : List Nat) (c : Nat × Nat) (A : FcrNF) :
    CommRingTreeConv (fcrCombOfNF (fcrInsertTerm (m, c) A))
      (FcrTree.addOp (fcrTermToTree m c) (fcrCombOfNF A)) := by
  induction A with
  | nil => exact CommRingTreeConv.refl _
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [fcrInsertTermEqE m c p e rest hmp, fcrCombOfNFCons p (fcrCoeffAdd e c) rest,
              fcrCombOfNFCons p e rest, hmeqp]
          exact (CommRingTreeConv.addCongr (fcrTermToTreeAdd p e c)
              (CommRingTreeConv.refl (fcrCombOfNF rest))).trans
            ((CommRingTreeConv.addAssoc (fcrTermToTree p e) (fcrTermToTree p c) (fcrCombOfNF rest)).trans
              (fcrConvAddSwap13 (fcrTermToTree p e) (fcrTermToTree p c) (fcrCombOfNF rest)))
      | lt =>
          rw [fcrInsertTermLtE m c p e rest hmp, fcrCombOfNFCons m c ((p, e) :: rest)]
          exact CommRingTreeConv.refl _
      | gt =>
          rw [fcrInsertTermGtE m c p e rest hmp, fcrCombOfNFCons p e (fcrInsertTerm (m, c) rest),
              fcrCombOfNFCons p e rest]
          exact (CommRingTreeConv.addCongr (CommRingTreeConv.refl (fcrTermToTree p e)) ih).trans
            (fcrConvAddSwap13 (fcrTermToTree p e) (fcrTermToTree m c) (fcrCombOfNF rest))

theorem fcrCombMergeAdd (A B : FcrNF) :
    CommRingTreeConv (fcrCombOfNF (fcrMergeAdd A B))
      (FcrTree.addOp (fcrCombOfNF A) (fcrCombOfNF B)) := by
  induction A with
  | nil => exact (fcrConvAddZeroLeft (fcrCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show CommRingTreeConv (fcrCombOfNF (fcrInsertTerm (m, c) (fcrMergeAdd A' B)))
        (FcrTree.addOp (FcrTree.addOp (fcrTermToTree m c) (fcrCombOfNF A')) (fcrCombOfNF B))
      exact ((fcrCombInsertTerm m c (fcrMergeAdd A' B)).trans
          (CommRingTreeConv.addCongr (CommRingTreeConv.refl (fcrTermToTree m c)) ih)).trans
        (CommRingTreeConv.symm
          (CommRingTreeConv.addAssoc (fcrTermToTree m c) (fcrCombOfNF A') (fcrCombOfNF B)))

theorem fcrCombTermMul (m : List Nat) (c : Nat × Nat) (B : FcrNF) :
    CommRingTreeConv (fcrCombOfNF (fcrTermMul m c B))
      (FcrTree.mulOp (fcrTermToTree m c) (fcrCombOfNF B)) := by
  induction B with
  | nil => exact (CommRingTreeConv.annihilRight (fcrTermToTree m c)).symm
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show CommRingTreeConv (fcrCombOfNF (fcrInsertTerm (csrMonoMul m n, fcrCoeffMul c d) (fcrTermMul m c B')))
        (FcrTree.mulOp (fcrTermToTree m c) (FcrTree.addOp (fcrTermToTree n d) (fcrCombOfNF B')))
      exact ((fcrCombInsertTerm (csrMonoMul m n) (fcrCoeffMul c d) (fcrTermMul m c B')).trans
          (CommRingTreeConv.addCongr (fcrTermToTreeMul m c n d) ih)).trans
        (CommRingTreeConv.symm
          (CommRingTreeConv.distribLeft (fcrTermToTree m c) (fcrTermToTree n d) (fcrCombOfNF B')))

theorem fcrCombMulConvolve (A B : FcrNF) :
    CommRingTreeConv (fcrCombOfNF (fcrMulConvolve A B))
      (FcrTree.mulOp (fcrCombOfNF A) (fcrCombOfNF B)) := by
  induction A with
  | nil => exact (fcrConvAnnihilLeft (fcrCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show CommRingTreeConv (fcrCombOfNF (fcrMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B)))
        (FcrTree.mulOp (FcrTree.addOp (fcrTermToTree m c) (fcrCombOfNF A')) (fcrCombOfNF B))
      exact ((fcrCombMergeAdd (fcrTermMul m c B) (fcrMulConvolve A' B)).trans
          (CommRingTreeConv.addCongr (fcrCombTermMul m c B) ih)).trans
        (CommRingTreeConv.symm (fcrConvDistribRight (fcrTermToTree m c) (fcrCombOfNF A') (fcrCombOfNF B)))

/-! ## Negation through the rebuild -/

/-- Negation passes through a scale tree: `neg (k·X) ≈ k·(neg X)`. -/
theorem fcrScaleTreeNeg (X : FcrTree) (k : Nat) :
    CommRingTreeConv (FcrTree.negOp (fcrScaleTree X k)) (fcrScaleTree (FcrTree.negOp X) k) := by
  induction k with
  | zero => exact fcrConvNegZero
  | succ j ih =>
      exact (fcrConvNegAdd X (fcrScaleTree X j)).trans
        (CommRingTreeConv.addCongr (CommRingTreeConv.refl (FcrTree.negOp X)) ih)

/-- Negating a term tree negates its coefficient: `termToTree m (neg c) ≈ neg (termToTree m c)`. -/
theorem fcrTermToTreeNeg (m : List Nat) (c : Nat × Nat) :
    CommRingTreeConv (fcrTermToTree m (fcrCoeffNeg c)) (FcrTree.negOp (fcrTermToTree m c)) := by
  obtain ⟨p, n⟩ := c
  have hswap : CommRingTreeConv (fcrTermToTree m (n, p))
      (FcrTree.addOp (fcrScaleTree (FcrTree.negOp (fcrMonoToTree m)) p) (fcrScaleTree (fcrMonoToTree m) n)) :=
    CommRingTreeConv.addComm (fcrScaleTree (fcrMonoToTree m) n)
      (fcrScaleTree (FcrTree.negOp (fcrMonoToTree m)) p)
  have hback : CommRingTreeConv (FcrTree.negOp (fcrTermToTree m (p, n)))
      (FcrTree.addOp (fcrScaleTree (FcrTree.negOp (fcrMonoToTree m)) p) (fcrScaleTree (fcrMonoToTree m) n)) :=
    (fcrConvNegAdd (fcrScaleTree (fcrMonoToTree m) p)
        (fcrScaleTree (FcrTree.negOp (fcrMonoToTree m)) n)).trans
      (CommRingTreeConv.addCongr (fcrScaleTreeNeg (fcrMonoToTree m) p)
        ((fcrScaleTreeNeg (FcrTree.negOp (fcrMonoToTree m)) n).trans
          (fcrScaleTreeCongr (fcrConvNegNeg (fcrMonoToTree m)) n)))
  exact hswap.trans hback.symm

theorem fcrCombNegate (A : FcrNF) :
    CommRingTreeConv (fcrCombOfNF (fcrNegate A)) (FcrTree.negOp (fcrCombOfNF A)) := by
  induction A with
  | nil => exact fcrConvNegZero.symm
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show CommRingTreeConv (FcrTree.addOp (fcrTermToTree m (fcrCoeffNeg c)) (fcrCombOfNF (fcrNegate rest)))
        (FcrTree.negOp (FcrTree.addOp (fcrTermToTree m c) (fcrCombOfNF rest)))
      exact (CommRingTreeConv.addCongr (fcrTermToTreeNeg m c) ih).trans
        (fcrConvNegAdd (fcrTermToTree m c) (fcrCombOfNF rest)).symm

/-! ## The all-zero rebuild is convertible to `0` -/

/-- `k·X + k·(neg X) ≈ 0`. -/
theorem fcrScaleTreeNegCancel (X : FcrTree) (k : Nat) :
    CommRingTreeConv (FcrTree.addOp (fcrScaleTree X k) (fcrScaleTree (FcrTree.negOp X) k)) FcrTree.zeroOp := by
  induction k with
  | zero => exact CommRingTreeConv.addZero FcrTree.zeroOp
  | succ j ih =>
      exact (fcrConvAddMiddleFour X (fcrScaleTree X j) (FcrTree.negOp X) (fcrScaleTree (FcrTree.negOp X) j)).trans
        ((CommRingTreeConv.addCongr (CommRingTreeConv.addNegInverse X) ih).trans
          (CommRingTreeConv.addZero FcrTree.zeroOp))

/-- A zero-valued term tree is convertible to `0`. -/
theorem fcrTermToTreeZero (m : List Nat) (c : Nat × Nat) (hc : fcrCoeffIsZero c = true) :
    CommRingTreeConv (fcrTermToTree m c) FcrTree.zeroOp := by
  obtain ⟨p, n⟩ := c
  have hpn : p = n := csrNatEqOfBeq p n hc
  rw [fcrTermToTreeEq m p n, hpn]
  exact fcrScaleTreeNegCancel (fcrMonoToTree m) n

/-- An all-zero rebuild reduces to `0`. -/
theorem fcrCombAllZero (A : FcrNF) (hA : fcrNFAllZero A = true) :
    CommRingTreeConv (fcrCombOfNF A) FcrTree.zeroOp := by
  induction A with
  | nil => exact CommRingTreeConv.refl FcrTree.zeroOp
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      have hc : fcrCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hrest : fcrNFAllZero rest = true := csrAndTrueRight _ _ hA
      show CommRingTreeConv (FcrTree.addOp (fcrTermToTree m c) (fcrCombOfNF rest)) FcrTree.zeroOp
      exact (CommRingTreeConv.addCongr (fcrTermToTreeZero m c hc) (ih hrest)).trans
        (CommRingTreeConv.addZero FcrTree.zeroOp)

/-! ## Reification: every tree is convertible to the rebuild of its own normal form -/

/-- `monoToTree m ≈ termToTree m (1,0)` (the unit-coefficient term is the monomial). -/
theorem fcrMonoToTreeTermOne (m : List Nat) :
    CommRingTreeConv (fcrMonoToTree m) (fcrTermToTree m (1, 0)) :=
  (CommRingTreeConv.addZero (fcrMonoToTree m)).symm.trans
    (CommRingTreeConv.addZero (FcrTree.addOp (fcrMonoToTree m) FcrTree.zeroOp)).symm

/-- ★ Every tree is convertible to the rebuild of its own normal form. -/
theorem fcrTreeReifies (t : FcrTree) : CommRingTreeConv t (fcrCombOfNF (fcrNormalize t)) := by
  induction t with
  | gen c =>
      show CommRingTreeConv (FcrTree.gen c)
        (FcrTree.addOp (fcrTermToTree [c] (1, 0)) FcrTree.zeroOp)
      have hgen : CommRingTreeConv (FcrTree.gen c) (fcrMonoToTree [c]) :=
        (CommRingTreeConv.mulOne (FcrTree.gen c)).symm
      exact (hgen.trans (fcrMonoToTreeTermOne [c])).trans
        (CommRingTreeConv.addZero (fcrTermToTree [c] (1, 0))).symm
  | zeroOp => exact CommRingTreeConv.refl FcrTree.zeroOp
  | oneOp =>
      show CommRingTreeConv FcrTree.oneOp (FcrTree.addOp (fcrTermToTree [] (1, 0)) FcrTree.zeroOp)
      exact (fcrMonoToTreeTermOne []).trans (CommRingTreeConv.addZero (fcrTermToTree [] (1, 0))).symm
  | addOp l r ihl ihr =>
      show CommRingTreeConv (FcrTree.addOp l r)
        (fcrCombOfNF (fcrMergeAdd (fcrNormalize l) (fcrNormalize r)))
      exact (CommRingTreeConv.addCongr ihl ihr).trans
        (CommRingTreeConv.symm (fcrCombMergeAdd (fcrNormalize l) (fcrNormalize r)))
  | mulOp l r ihl ihr =>
      show CommRingTreeConv (FcrTree.mulOp l r)
        (fcrCombOfNF (fcrMulConvolve (fcrNormalize l) (fcrNormalize r)))
      exact (CommRingTreeConv.mulCongr ihl ihr).trans
        (CommRingTreeConv.symm (fcrCombMulConvolve (fcrNormalize l) (fcrNormalize r)))
  | negOp a ih =>
      show CommRingTreeConv (FcrTree.negOp a) (fcrCombOfNF (fcrNegate (fcrNormalize a)))
      exact (CommRingTreeConv.negCongr ih).trans
        (CommRingTreeConv.symm (fcrCombNegate (fcrNormalize a)))

/-! ## Completeness: `fcrNFEq` normal forms give convertible trees -/

/-- If `x + neg y ≈ 0` then `x ≈ y` (move a subtraction to the other side). -/
theorem fcrConvOfSubZero (x y : FcrTree)
    (h : CommRingTreeConv (FcrTree.addOp x (FcrTree.negOp y)) FcrTree.zeroOp) : CommRingTreeConv x y :=
  (CommRingTreeConv.addZero x).symm.trans
    ((CommRingTreeConv.addCongr (CommRingTreeConv.refl x) (fcrConvAddNegInverseLeft y).symm).trans
      ((CommRingTreeConv.addAssoc x (FcrTree.negOp y) y).symm.trans
        ((CommRingTreeConv.addCongr h (CommRingTreeConv.refl y)).trans (fcrConvAddZeroLeft y))))

/-- The rebuilds of `fcrNFEq` normal forms are convertible: `fcrNFEq A B → comb A ≈ comb B`. -/
theorem fcrCombOfNFEqConv (A B : FcrNF) (h : fcrNFEq A B = true) :
    CommRingTreeConv (fcrCombOfNF A) (fcrCombOfNF B) := by
  apply fcrConvOfSubZero (fcrCombOfNF A) (fcrCombOfNF B)
  have hall : CommRingTreeConv (fcrCombOfNF (fcrMergeAdd A (fcrNegate B))) FcrTree.zeroOp :=
    fcrCombAllZero (fcrMergeAdd A (fcrNegate B)) h
  exact (CommRingTreeConv.symm ((fcrCombMergeAdd A (fcrNegate B)).trans
      (CommRingTreeConv.addCongr (CommRingTreeConv.refl (fcrCombOfNF A)) (fcrCombNegate B)))).trans hall

/-- ★ Completeness — `fcrNFEq` normal forms give convertible trees.  Both trees reify to the rebuild of their
normal form, and equal normal forms rebuild convertibly. -/
theorem fcrConv_of_normalizeEq {s t : FcrTree} (h : fcrNFEq (fcrNormalize s) (fcrNormalize t) = true) :
    CommRingTreeConv s t :=
  (fcrTreeReifies s).trans
    ((fcrCombOfNFEqConv (fcrNormalize s) (fcrNormalize t) h).trans (CommRingTreeConv.symm (fcrTreeReifies t)))

/-! ## The decision -/

/-- ★★ the decision procedure: convertible iff the polynomial difference has every coefficient zero-valued. -/
def fcrDecideConv (s t : FcrTree) : Bool := fcrNFEq (fcrNormalize s) (fcrNormalize t)

/-- ★★ THE DECISION: convertibility ⟺ equal polynomial (ℤ[X]) normal form. -/
theorem commRingTreeConv_iff_normalForm (s t : FcrTree) :
    CommRingTreeConv s t ↔ fcrDecideConv s t = true := by
  constructor
  · intro conv
    exact fcrNormalize_respects conv
  · intro hdec
    exact fcrConv_of_normalizeEq hdec

/-- ★ decidability, via the biconditional (no `propext`). -/
instance fcrDecidableConv (s t : FcrTree) : Decidable (CommRingTreeConv s t) :=
  if h : fcrDecideConv s t = true then
    isTrue ((commRingTreeConv_iff_normalForm s t).mpr h)
  else
    isFalse (fun conv => h ((commRingTreeConv_iff_normalForm s t).mp conv))

/-- ★★ the walking free commutative ring on ℕ (the polynomial ring `ℤ[X]`) is DECIDED. -/
def fxWalkingCommutativeRing_hasNormalFormDecision : Bool := true

-- genuineness smokes
-- THE HEADLINE — the additive inverse: x + neg x is 0 (true)
#eval fcrDecideConv (FcrTree.addOp (FcrTree.gen 0) (FcrTree.negOp (FcrTree.gen 0))) FcrTree.zeroOp
-- distributivity x * (y + z) is x*y + x*z (true)
#eval fcrDecideConv (FcrTree.mulOp (FcrTree.gen 0) (FcrTree.addOp (FcrTree.gen 1) (FcrTree.gen 2)))
  (FcrTree.addOp (FcrTree.mulOp (FcrTree.gen 0) (FcrTree.gen 1))
    (FcrTree.mulOp (FcrTree.gen 0) (FcrTree.gen 2)))
-- commutativity x*y is y*x (true)
#eval fcrDecideConv (FcrTree.mulOp (FcrTree.gen 0) (FcrTree.gen 1))
  (FcrTree.mulOp (FcrTree.gen 1) (FcrTree.gen 0))
-- difference of squares (x + neg y)*(x + neg y) is x*x + neg(x*y) + neg(x*y) + y*y (true; neg through mul)
#eval fcrDecideConv
  (FcrTree.mulOp (FcrTree.addOp (FcrTree.gen 0) (FcrTree.negOp (FcrTree.gen 1)))
    (FcrTree.addOp (FcrTree.gen 0) (FcrTree.negOp (FcrTree.gen 1))))
  (FcrTree.addOp
    (FcrTree.addOp (FcrTree.addOp (FcrTree.mulOp (FcrTree.gen 0) (FcrTree.gen 0))
      (FcrTree.negOp (FcrTree.mulOp (FcrTree.gen 0) (FcrTree.gen 1))))
      (FcrTree.negOp (FcrTree.mulOp (FcrTree.gen 0) (FcrTree.gen 1))))
    (FcrTree.mulOp (FcrTree.gen 1) (FcrTree.gen 1)))
-- double negation neg(neg x) is x (true)
#eval fcrDecideConv (FcrTree.negOp (FcrTree.negOp (FcrTree.gen 0))) (FcrTree.gen 0)
-- separation x + x is NOT x (false)
#eval fcrDecideConv (FcrTree.addOp (FcrTree.gen 0) (FcrTree.gen 0)) (FcrTree.gen 0)
-- separation x is NOT neg x (false)
#eval fcrDecideConv (FcrTree.gen 0) (FcrTree.negOp (FcrTree.gen 0))

end FX1Poly.Polygraph
