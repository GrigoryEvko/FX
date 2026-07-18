import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeRing.CommutativeRingSeed
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # WalkingRing/RingSeed — the walking free NON-COMMUTATIVE RING on ℕ: the polynomial ℤ⟨X⟩ decision

The mechanical MERGE of two already-decided siblings.  From the non-commutative semiring rung
(`WalkingSemiring/SemiringSeed`, whose free algebra was `ℕ⟨X⟩`) it takes the ORDER-SIGNIFICANT WORD monomials
(a plain `List Nat`, with monomial product = cons-only word CONCATENATION `frWordCat`, no commutativity, both
distributivities, both annihilations, both units).  From the commutative ring rung
(`WalkingCommutativeRing/CommutativeRingSeed`, whose free algebra was `ℤ[X]`) it takes the subtraction-free
INTEGER coefficients — each an ℕ-pair `(pos, neg)` denoting `pos − neg` (never a `Nat.sub`) — the unary
negation `negOp`, and the DIFFERENCE-based decision.  Adjoining a formal additive inverse to `ℕ⟨X⟩` completes
each coefficient's natural count to its group of differences, so the free **non-commutative ring** on the
colour set `ℕ` is the polynomial ring `ℤ⟨X_c : c ∈ ℕ⟩` in NON-commuting variables with integer coefficients.
A tree's class is determined by its non-commutative polynomial — the finite formal `ℤ`-linear combination of
words — and because that polynomial is a COMPLETE invariant, the word problem is DECIDED.  There is no crux:
both constituent patterns are proven, and this is their merge.

## ★ Words × integer coefficients — reusing the imported total order

A monomial is an ORDER-SIGNIFICANT WORD, a plain `List Nat` carrying its own order; monomial product is
CONCATENATION via the cons-only `frWordCat` (never `List.append`/`++`), which is associative but NOT
commutative.  The normal form `FrNF := List (List Nat × (Nat × Nat))` is a list of `(word, coeffPair)` terms
sorted strictly by the imported total word order `csrCompare` (length-first then lex, on ARBITRARY `List Nat`
— it distinguishes `[0,1]` from `[1,0]`, which is exactly what non-commutativity needs).  Following the `ℤ[X]`
pattern, the operations do NOT drop cancelling terms: a zero-valued coefficient is carried as an ordinary term
and only the DECISION reads it off.

The coefficient algebra is the `ℤ[X]` sibling's, re-proved here under the `fr` prefix so the audit twin gates
it independently: `frCoeffAdd (p1,n1) (p2,n2) := (p1+p2, n1+n2)`; `frCoeffMul (p1,n1) (p2,n2) :=
(p1 p2 + n1 n2, p1 n2 + n1 p2)` (product of differences — COMMUTATIVE as an integer product, even though the
WORD product is not); `frCoeffNeg (p,n) := (n,p)`; `frCoeffEq (p1,n1) (p2,n2) := Nat.beq (p1+n2) (p2+n1)`;
`frCoeffIsZero (p,n) := Nat.beq p n`.  The coefficient ring laws are discharged by the clean `Nat.add`/`Nat.mul`
kit plus the hand-proved structural replacements `frNatMulAssoc` / `frNatAddMul` (the library `Nat.mul_assoc` /
`Nat.add_mul` LEAK `propext`).

## ★ The multiplicative MONOID (no commutativity) and the subtraction-free decision

`frMulConvolve` is the Cauchy convolution: word product = `frWordCat` (concatenation), coefficient product =
`frCoeffMul`.  It has BOTH ANNIHILATIONS, LEFT and RIGHT DISTRIBUTIVITY (neither derivable from the other
absent commutativity), ASSOCIATIVITY (via `frTermMul_compose` reducing to `frWordCatAssoc` + `frCoeffMulAssoc`),
and BOTH UNITS (`frMulConvolveUnitLeft` `1·a` and `frMulConvolveUnitRight` `a·1`).  There is deliberately NO
convolution-commutativity lemma — that is the whole point of this walker.

The decision is the SUBTRACTION-FREE polynomial equality `frNFEq A B := frNFAllZero (frMergeAdd A (frNegate B))`
— two polynomials are equal exactly when their difference has every coefficient zero-valued.  Its soundness /
completeness rest on the `frEvalCross` per-word coefficient-sum model, whose merge/negate homomorphisms make
`frNFEq` a decidable equivalence and a congruence; the crux `frMergeAddSelfNegAllZero` (a polynomial plus its
own negation is all-zero-valued) falls out of the model.  Completeness rebuilds a canonical tree from a normal
form (`frCombOfNF`) and reifies every tree to that rebuild (`frTreeReifies`), where word concatenation reifies
by `mulAssoc` + the LEFT unit (no commutativity) and negation passes through multiplication on BOTH sides.

This file ships, all zero-axiom: the coefficient ring algebra; the pair-coefficient normal-form machinery;
`frMulConvolve` with annihilation / distributivity / associativity / both units; `frNegate` with its
merge/involution algebra; the `frEvalCross` model; `FrTree` with `negOp`, `frNormalize`, and `RingTreeConv`
(the abelian additive group with `addNegInverse` + the NON-commutative multiplicative monoid + both
distributivities + both annihilations + `negCongr`); soundness (`frNormalize_respects`), completeness
(`frConv_of_normalizeEq`), and THE DECISION (`ringTreeConv_iff_normalForm`, a genuine `Decidable` instance, and
`#eval` groundings — the additive-inverse headline `x + neg x ≈ 0` AND the non-commutativity headline
`x·y ≉ y·x`).

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`,
`Int`, `Nat.sub`, `Nat.min`/`Nat.max`, `Nat.mul_assoc`/`Nat.add_mul`, `List.append` (`++`), and every
`Nat.le`/`Nat.ble` lemma — the word order is the imported structural `csrCompare` (built on `natBle`), word
concatenation is the cons-only `frWordCat`, integer coefficients are `(pos, neg)` ℕ-pairs, and no coefficient
is ever canonicalized by subtraction. -/

namespace FX1Poly.Polygraph

/-! ## Word concatenation: the NON-commutative monomial product (cons-only, never `++`) -/

/-- Word multiplication = CONCATENATION (order-significant, cons-only recursion on the first word). -/
def frWordCat : List Nat → List Nat → List Nat
  | [], n => n
  | a :: as, n => a :: frWordCat as n
theorem frWordCatNilLeft (n : List Nat) : frWordCat [] n = n := rfl
theorem frWordCatNilRight : (m : List Nat) → frWordCat m [] = m
  | [] => rfl
  | a :: as => by
      show a :: frWordCat as [] = a :: as
      rw [frWordCatNilRight as]
theorem frWordCatAssoc : (m n p : List Nat) →
    frWordCat (frWordCat m n) p = frWordCat m (frWordCat n p)
  | [], _, _ => rfl
  | a :: as, n, p => by
      show a :: frWordCat (frWordCat as n) p = a :: frWordCat as (frWordCat n p)
      rw [frWordCatAssoc as n p]

/-! ## The clean `Nat` kit (replacing the propext-leaky `Nat.mul_assoc` / `Nat.add_mul`) -/

/-- Clean structural replacement for `Nat.mul_assoc`. -/
theorem frNatMulAssoc : (a b c : Nat) → a * b * c = a * (b * c)
  | a, b, 0 => by rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | a, b, Nat.succ c => by
      rw [Nat.mul_succ, frNatMulAssoc a b c, Nat.mul_succ, Nat.mul_add]

/-- Clean structural replacement for `Nat.add_mul`. -/
theorem frNatAddMul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

/-- Clean structural right-cancellation for `Nat.add`. -/
theorem frNatAddRightCancel : (a b c : Nat) → a + c = b + c → a = b
  | a, b, 0, h => h
  | a, b, Nat.succ c, h => frNatAddRightCancel a b c (Nat.succ.inj h)

/-- Clean `1 * d = d` (via `Nat.mul_comm` / `Nat.mul_one`), feeding the coefficient LEFT unit. -/
theorem frNatOneMul (d : Nat) : 1 * d = d := by
  rw [Nat.mul_comm 1 d, Nat.mul_one d]

/-! ## The coefficient algebra: integers as subtraction-free `(pos, neg)` ℕ-pairs -/

/-- The coefficient `add`: componentwise `Nat.add`. -/
def frCoeffAdd : (Nat × Nat) → (Nat × Nat) → (Nat × Nat)
  | (p1, n1), (p2, n2) => (p1 + p2, n1 + n2)

/-- The coefficient `mul`: the product of differences `(p1 − n1)(p2 − n2)`. -/
def frCoeffMul : (Nat × Nat) → (Nat × Nat) → (Nat × Nat)
  | (p1, n1), (p2, n2) => (p1 * p2 + n1 * n2, p1 * n2 + n1 * p2)

/-- The coefficient negation: SWAP the positive and inverse components. -/
def frCoeffNeg : (Nat × Nat) → (Nat × Nat)
  | (p, n) => (n, p)

/-- The coefficient CROSS-ADD equality `p1 + n2 = p2 + n1`. -/
def frCoeffEq : (Nat × Nat) → (Nat × Nat) → Bool
  | (p1, n1), (p2, n2) => Nat.beq (p1 + n2) (p2 + n1)

/-- The coefficient is zero exactly when `pos = neg`. -/
def frCoeffIsZero : (Nat × Nat) → Bool
  | (p, n) => Nat.beq p n

/-! ### Coefficient `add` laws -/

theorem frCoeffAddComm (a b : Nat × Nat) : frCoeffAdd a b = frCoeffAdd b a := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  show (p1 + p2, n1 + n2) = (p2 + p1, n2 + n1)
  rw [Nat.add_comm p1 p2, Nat.add_comm n1 n2]

theorem frCoeffAddAssoc (a b c : Nat × Nat) :
    frCoeffAdd (frCoeffAdd a b) c = frCoeffAdd a (frCoeffAdd b c) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b; obtain ⟨p3, n3⟩ := c
  show (p1 + p2 + p3, n1 + n2 + n3) = (p1 + (p2 + p3), n1 + (n2 + n3))
  rw [Nat.add_assoc p1 p2 p3, Nat.add_assoc n1 n2 n3]

theorem frCoeffAddZeroRight (a : Nat × Nat) : frCoeffAdd a (0, 0) = a := by
  obtain ⟨p, n⟩ := a
  show (p + 0, n + 0) = (p, n)
  rw [Nat.add_zero, Nat.add_zero]

theorem frCoeffAddZeroLeft (a : Nat × Nat) : frCoeffAdd (0, 0) a = a := by
  rw [frCoeffAddComm]; exact frCoeffAddZeroRight a

theorem frCoeffNegAdd (a b : Nat × Nat) :
    frCoeffNeg (frCoeffAdd a b) = frCoeffAdd (frCoeffNeg a) (frCoeffNeg b) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  rfl

theorem frCoeffNegNeg (a : Nat × Nat) : frCoeffNeg (frCoeffNeg a) = a := by
  obtain ⟨p, n⟩ := a; rfl

/-! ### Zero-valued coefficient facts -/

theorem frCoeffAddNegIsZero (a : Nat × Nat) : frCoeffIsZero (frCoeffAdd a (frCoeffNeg a)) = true := by
  obtain ⟨p, n⟩ := a
  show Nat.beq (p + n) (n + p) = true
  rw [Nat.add_comm p n]; exact csrNatBeqRefl (n + p)

theorem frCoeffAddZeroValued (a b : Nat × Nat)
    (ha : frCoeffIsZero a = true) (hb : frCoeffIsZero b = true) :
    frCoeffIsZero (frCoeffAdd a b) = true := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  have h1 : p1 = n1 := csrNatEqOfBeq p1 n1 ha
  have h2 : p2 = n2 := csrNatEqOfBeq p2 n2 hb
  show Nat.beq (p1 + p2) (n1 + n2) = true
  rw [h1, h2]; exact csrNatBeqRefl (n1 + n2)

theorem frCoeffNegIsZero (a : Nat × Nat) : frCoeffIsZero (frCoeffNeg a) = frCoeffIsZero a := by
  obtain ⟨p, n⟩ := a
  show Nat.beq n p = Nat.beq p n
  exact csrNatBeqSymm n p

theorem frCoeffAddCancelZero (a b : Nat × Nat)
    (hsum : frCoeffIsZero (frCoeffAdd a b) = true) (hb : frCoeffIsZero b = true) :
    frCoeffIsZero a = true := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  have hbb : p2 = n2 := csrNatEqOfBeq p2 n2 hb
  have hs : p1 + p2 = n1 + n2 := csrNatEqOfBeq (p1 + p2) (n1 + n2) hsum
  rw [hbb] at hs
  have hp1n1 : p1 = n1 := frNatAddRightCancel p1 n1 n2 hs
  show Nat.beq p1 n1 = true
  rw [hp1n1]; exact csrNatBeqRefl n1

/-! ### Nat add-reordering helper -/

theorem frNatAddMiddleFour (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d, Nat.add_comm b c, Nat.add_assoc c b d,
      ← Nat.add_assoc a c (b + d)]

/-! ### Coefficient `mul` laws (the integer product is commutative even though the WORD product is not) -/

theorem frCoeffMulComm (a b : Nat × Nat) : frCoeffMul a b = frCoeffMul b a := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  show (p1 * p2 + n1 * n2, p1 * n2 + n1 * p2) = (p2 * p1 + n2 * n1, p2 * n1 + n2 * p1)
  rw [Nat.mul_comm p1 p2, Nat.mul_comm n1 n2, Nat.mul_comm p1 n2, Nat.mul_comm n1 p2,
      Nat.add_comm (n2 * p1) (p2 * n1)]

theorem frCoeffMulOne (a : Nat × Nat) : frCoeffMul a (1, 0) = a := by
  obtain ⟨p, n⟩ := a
  show (p * 1 + n * 0, p * 0 + n * 1) = (p, n)
  rw [Nat.mul_one p, Nat.mul_zero n, Nat.add_zero, Nat.mul_zero p, Nat.mul_one n, Nat.zero_add]

/-- Coefficient LEFT unit `(1,0) * a = a` (the multiplicative left unit `1·a = a` needs this directly, absent
convolution commutativity). -/
theorem frCoeffOneMul (a : Nat × Nat) : frCoeffMul (1, 0) a = a := by
  obtain ⟨p, n⟩ := a
  show (1 * p + 0 * n, 1 * n + 0 * p) = (p, n)
  rw [Nat.zero_mul n, Nat.zero_mul p, Nat.add_zero, Nat.add_zero, frNatOneMul p, frNatOneMul n]

theorem frCoeffMulZeroRight (a : Nat × Nat) : frCoeffMul a (0, 0) = (0, 0) := by
  obtain ⟨p, n⟩ := a
  show (p * 0 + n * 0, p * 0 + n * 0) = (0, 0)
  rw [Nat.mul_zero p, Nat.mul_zero n, Nat.add_zero]

/-- Coefficient left-distributivity `a * (b + c) = a * b + a * c`. -/
theorem frCoeffMulAddRight (a b c : Nat × Nat) :
    frCoeffMul a (frCoeffAdd b c) = frCoeffAdd (frCoeffMul a b) (frCoeffMul a c) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b; obtain ⟨p3, n3⟩ := c
  show (p1 * (p2 + p3) + n1 * (n2 + n3), p1 * (n2 + n3) + n1 * (p2 + p3))
      = (p1 * p2 + n1 * n2 + (p1 * p3 + n1 * n3), p1 * n2 + n1 * p2 + (p1 * n3 + n1 * p3))
  rw [Nat.mul_add p1 p2 p3, Nat.mul_add n1 n2 n3, Nat.mul_add p1 n2 n3, Nat.mul_add n1 p2 p3,
      frNatAddMiddleFour (p1 * p2) (p1 * p3) (n1 * n2) (n1 * n3),
      frNatAddMiddleFour (p1 * n2) (p1 * n3) (n1 * p2) (n1 * p3)]

/-- Coefficient right-distributivity `(a + b) * c = a * c + b * c`. -/
theorem frCoeffAddMulRight (a b c : Nat × Nat) :
    frCoeffMul (frCoeffAdd a b) c = frCoeffAdd (frCoeffMul a c) (frCoeffMul b c) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b; obtain ⟨p3, n3⟩ := c
  show ((p1 + p2) * p3 + (n1 + n2) * n3, (p1 + p2) * n3 + (n1 + n2) * p3)
      = (p1 * p3 + n1 * n3 + (p2 * p3 + n2 * n3), p1 * n3 + n1 * p3 + (p2 * n3 + n2 * p3))
  rw [frNatAddMul p1 p2 p3, frNatAddMul n1 n2 n3, frNatAddMul p1 p2 n3, frNatAddMul n1 n2 p3,
      frNatAddMiddleFour (p1 * p3) (p2 * p3) (n1 * n3) (n2 * n3),
      frNatAddMiddleFour (p1 * n3) (p2 * n3) (n1 * p3) (n2 * p3)]

/-- Coefficient negation passes through multiplication on the left. -/
theorem frCoeffNegMulLeft (a b : Nat × Nat) :
    frCoeffNeg (frCoeffMul a b) = frCoeffMul (frCoeffNeg a) b := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  show (p1 * n2 + n1 * p2, p1 * p2 + n1 * n2) = (n1 * p2 + p1 * n2, n1 * n2 + p1 * p2)
  rw [Nat.add_comm (p1 * n2) (n1 * p2), Nat.add_comm (p1 * p2) (n1 * n2)]

/-- ★ Coefficient multiplication is associative — the hardest coefficient law. -/
theorem frCoeffMulAssoc (a b c : Nat × Nat) :
    frCoeffMul (frCoeffMul a b) c = frCoeffMul a (frCoeffMul b c) := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b; obtain ⟨p3, n3⟩ := c
  show ((p1 * p2 + n1 * n2) * p3 + (p1 * n2 + n1 * p2) * n3,
        (p1 * p2 + n1 * n2) * n3 + (p1 * n2 + n1 * p2) * p3)
      = (p1 * (p2 * p3 + n2 * n3) + n1 * (p2 * n3 + n2 * p3),
         p1 * (p2 * n3 + n2 * p3) + n1 * (p2 * p3 + n2 * n3))
  rw [frNatAddMul (p1 * p2) (n1 * n2) p3, frNatAddMul (p1 * n2) (n1 * p2) n3,
      frNatAddMul (p1 * p2) (n1 * n2) n3, frNatAddMul (p1 * n2) (n1 * p2) p3,
      Nat.mul_add p1 (p2 * p3) (n2 * n3), Nat.mul_add n1 (p2 * n3) (n2 * p3),
      Nat.mul_add p1 (p2 * n3) (n2 * p3), Nat.mul_add n1 (p2 * p3) (n2 * n3),
      frNatMulAssoc p1 p2 p3, frNatMulAssoc n1 n2 p3, frNatMulAssoc p1 n2 n3, frNatMulAssoc n1 p2 n3,
      frNatMulAssoc p1 p2 n3, frNatMulAssoc n1 n2 n3, frNatMulAssoc p1 n2 p3, frNatMulAssoc n1 p2 p3,
      frNatAddMiddleFour (p1 * (p2 * p3)) (n1 * (n2 * p3)) (p1 * (n2 * n3)) (n1 * (p2 * n3)),
      Nat.add_comm (n1 * (n2 * p3)) (n1 * (p2 * n3)),
      frNatAddMiddleFour (p1 * (p2 * n3)) (n1 * (n2 * n3)) (p1 * (n2 * p3)) (n1 * (p2 * p3)),
      Nat.add_comm (n1 * (n2 * n3)) (n1 * (p2 * p3))]

/-! ### Coefficient cross-add equality is an equivalence -/

theorem frCoeffEqRefl (a : Nat × Nat) : frCoeffEq a a = true := by
  obtain ⟨p, n⟩ := a
  show Nat.beq (p + n) (p + n) = true
  exact csrNatBeqRefl (p + n)

theorem frCoeffEqSymm (a b : Nat × Nat) (h : frCoeffEq a b = true) : frCoeffEq b a = true := by
  obtain ⟨p1, n1⟩ := a; obtain ⟨p2, n2⟩ := b
  have he : p1 + n2 = p2 + n1 := csrNatEqOfBeq (p1 + n2) (p2 + n1) h
  show Nat.beq (p2 + n1) (p1 + n2) = true
  rw [he]; exact csrNatBeqRefl (p2 + n1)

/-! ## The pair-coefficient normal form and its additive engine (words sorted by `csrCompare`, no zero-drop) -/

/-- The normal form: a list of `(word, coeffPair)` terms, sorted strictly by the imported total word order
`csrCompare`.  A zero-valued coefficient is carried as an ordinary term (the operations never drop). -/
abbrev FrNF := List (List Nat × (Nat × Nat))

/-- Insert one term into a sorted normal form, ADDING coefficients on an equal word (never dropping). -/
def frInsertTerm : (List Nat × (Nat × Nat)) → FrNF → FrNF
  | term, [] => [term]
  | (m, c), (p, e) :: rest =>
      match csrCompare m p with
      | CsrMonoOrd.eq => (p, frCoeffAdd e c) :: rest
      | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
      | CsrMonoOrd.gt => (p, e) :: frInsertTerm (m, c) rest
theorem frInsertTermNil (m : List Nat) (c : Nat × Nat) : frInsertTerm (m, c) [] = [(m, c)] := rfl
theorem frInsertTermEqE (m : List Nat) (c : Nat × Nat) (p : List Nat) (e : Nat × Nat) (rest : FrNF)
    (h : csrCompare m p = CsrMonoOrd.eq) :
    frInsertTerm (m, c) ((p, e) :: rest) = (p, frCoeffAdd e c) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, frCoeffAdd e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: frInsertTerm (m, c) rest) = (p, frCoeffAdd e c) :: rest
  rw [h]
theorem frInsertTermLtE (m : List Nat) (c : Nat × Nat) (p : List Nat) (e : Nat × Nat) (rest : FrNF)
    (h : csrCompare m p = CsrMonoOrd.lt) :
    frInsertTerm (m, c) ((p, e) :: rest) = (m, c) :: (p, e) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, frCoeffAdd e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: frInsertTerm (m, c) rest) = (m, c) :: (p, e) :: rest
  rw [h]
theorem frInsertTermGtE (m : List Nat) (c : Nat × Nat) (p : List Nat) (e : Nat × Nat) (rest : FrNF)
    (h : csrCompare m p = CsrMonoOrd.gt) :
    frInsertTerm (m, c) ((p, e) :: rest) = (p, e) :: frInsertTerm (m, c) rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, frCoeffAdd e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: frInsertTerm (m, c) rest) = (p, e) :: frInsertTerm (m, c) rest
  rw [h]

theorem frCoeffAddRightComm (e d c : Nat × Nat) :
    frCoeffAdd (frCoeffAdd e d) c = frCoeffAdd (frCoeffAdd e c) d := by
  rw [frCoeffAddAssoc e d c, frCoeffAddComm d c, ← frCoeffAddAssoc e c d]

/-- ★ The crux commutation: two term-insertions commute. -/
theorem frInsertTermComm (m : List Nat) (c : Nat × Nat) (n : List Nat) (d : Nat × Nat) (P : FrNF) :
    frInsertTerm (m, c) (frInsertTerm (n, d) P)
      = frInsertTerm (n, d) (frInsertTerm (m, c) P) := by
  induction P with
  | nil =>
      cases hmn : csrCompare m n with
      | eq =>
          have hmeqn : m = n := csrCompareEq_of m n hmn
          have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
          rw [frInsertTermNil n d, frInsertTermNil m c,
              frInsertTermEqE m c n d [] hmn, frInsertTermEqE n d m c [] hnm, hmeqn,
              frCoeffAddComm d c]
      | lt =>
          have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
          rw [frInsertTermNil n d, frInsertTermNil m c,
              frInsertTermLtE m c n d [] hmn, frInsertTermGtE n d m c [] hnm, frInsertTermNil n d]
      | gt =>
          have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn
          rw [frInsertTermNil n d, frInsertTermNil m c,
              frInsertTermGtE m c n d [] hmn, frInsertTermNil m c, frInsertTermLtE n d m c [] hnm]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [frInsertTermEqE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [frInsertTermEqE m c p (frCoeffAdd e d) rest hmp, frInsertTermEqE m c p e rest hmp,
                  frInsertTermEqE n d p (frCoeffAdd e c) rest hnp, frCoeffAddRightComm e d c]
          | lt =>
              have hpm : csrCompare p m = CsrMonoOrd.gt := csrCompareSwapLt m p hmp
              have hnm : csrCompare n m = CsrMonoOrd.gt := by rw [hnp_eq]; exact hpm
              rw [frInsertTermLtE m c p (frCoeffAdd e d) rest hmp, frInsertTermLtE m c p e rest hmp,
                  frInsertTermGtE n d m c ((p, e) :: rest) hnm, frInsertTermEqE n d p e rest hnp]
          | gt =>
              rw [frInsertTermGtE m c p (frCoeffAdd e d) rest hmp, frInsertTermGtE m c p e rest hmp,
                  frInsertTermEqE n d p e (frInsertTerm (m, c) rest) hnp]
      | lt =>
          rw [frInsertTermLtE n d p e rest hnp]
          cases hmn : csrCompare m n with
          | eq =>
              have hmeqn : m = n := csrCompareEq_of m n hmn
              have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
              have hmp : csrCompare m p = CsrMonoOrd.lt := by rw [hmeqn]; exact hnp
              rw [frInsertTermEqE m c n d ((p, e) :: rest) hmn, frInsertTermLtE m c p e rest hmp,
                  frInsertTermEqE n d m c ((p, e) :: rest) hnm, hmeqn, frCoeffAddComm d c]
          | lt =>
              have hmp : csrCompare m p = CsrMonoOrd.lt := csrCompareTransLt m n p hmn hnp
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [frInsertTermLtE m c n d ((p, e) :: rest) hmn, frInsertTermLtE m c p e rest hmp,
                  frInsertTermGtE n d m c ((p, e) :: rest) hnm, frInsertTermLtE n d p e rest hnp]
          | gt =>
              have hmn_gt : csrCompare m n = CsrMonoOrd.gt := hmn
              rw [frInsertTermGtE m c n d ((p, e) :: rest) hmn]
              cases hmp : csrCompare m p with
              | eq =>
                  rw [frInsertTermEqE m c p e rest hmp,
                      frInsertTermLtE n d p (frCoeffAdd e c) rest hnp]
              | lt =>
                  have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn_gt
                  rw [frInsertTermLtE m c p e rest hmp,
                      frInsertTermLtE n d m c ((p, e) :: rest) hnm]
              | gt =>
                  rw [frInsertTermGtE m c p e rest hmp,
                      frInsertTermLtE n d p e (frInsertTerm (m, c) rest) hnp]
      | gt =>
          rw [frInsertTermGtE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [frInsertTermEqE m c p e (frInsertTerm (n, d) rest) hmp,
                  frInsertTermEqE m c p e rest hmp,
                  frInsertTermGtE n d p (frCoeffAdd e c) rest hnp]
          | lt =>
              have hpn : csrCompare p n = CsrMonoOrd.lt := csrCompareSwapGt n p hnp
              have hmn : csrCompare m n = CsrMonoOrd.lt := csrCompareTransLt m p n hmp hpn
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [frInsertTermLtE m c p e (frInsertTerm (n, d) rest) hmp,
                  frInsertTermLtE m c p e rest hmp,
                  frInsertTermGtE n d m c ((p, e) :: rest) hnm,
                  frInsertTermGtE n d p e rest hnp]
          | gt =>
              rw [frInsertTermGtE m c p e (frInsertTerm (n, d) rest) hmp,
                  frInsertTermGtE m c p e rest hmp,
                  frInsertTermGtE n d p e (frInsertTerm (m, c) rest) hnp, ih]

/-- The additive merge: insert every term of the first list into the second. -/
def frMergeAdd : FrNF → FrNF → FrNF
  | [], b => b
  | t :: a', b => frInsertTerm t (frMergeAdd a' b)
theorem frMergeAddNilLeft (b : FrNF) : frMergeAdd [] b = b := rfl
theorem frMergeAddCons (t : List Nat × (Nat × Nat)) (a' b : FrNF) :
    frMergeAdd (t :: a') b = frInsertTerm t (frMergeAdd a' b) := rfl
theorem frInsertTerm_mergeAdd (t : List Nat × (Nat × Nat)) (a b : FrNF) :
    frInsertTerm t (frMergeAdd a b) = frMergeAdd a (frInsertTerm t b) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      obtain ⟨um, uc⟩ := u
      obtain ⟨tm, tc⟩ := t
      show frInsertTerm (tm, tc) (frInsertTerm (um, uc) (frMergeAdd a' b))
        = frMergeAdd ((um, uc) :: a') (frInsertTerm (tm, tc) b)
      rw [frMergeAddCons, frInsertTermComm tm tc um uc (frMergeAdd a' b), ih]
/-- Inserting the same word twice collapses (coefficients add). -/
theorem frInsertTermMergeSame (m : List Nat) (c1 c2 : Nat × Nat) (Z : FrNF) :
    frInsertTerm (m, c1) (frInsertTerm (m, c2) Z) = frInsertTerm (m, frCoeffAdd c2 c1) Z := by
  induction Z with
  | nil =>
      rw [frInsertTermNil m c2, frInsertTermEqE m c1 m c2 [] (csrCompareRefl m),
          frInsertTermNil m (frCoeffAdd c2 c1)]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          rw [frInsertTermEqE m c2 p e rest hmp, frInsertTermEqE m c1 p (frCoeffAdd e c2) rest hmp,
              frInsertTermEqE m (frCoeffAdd c2 c1) p e rest hmp, frCoeffAddAssoc e c2 c1]
      | lt =>
          rw [frInsertTermLtE m c2 p e rest hmp, frInsertTermEqE m c1 m c2 ((p, e) :: rest)
                (csrCompareRefl m), frInsertTermLtE m (frCoeffAdd c2 c1) p e rest hmp]
      | gt =>
          rw [frInsertTermGtE m c2 p e rest hmp, frInsertTermGtE m c1 p e
                (frInsertTerm (m, c2) rest) hmp, frInsertTermGtE m (frCoeffAdd c2 c1) p e rest hmp, ih]
/-- Pulling an insertion out of the left list of a merge. -/
theorem frMergeAddInsertTermLeft (u : List Nat × (Nat × Nat)) (Y c : FrNF) :
    frMergeAdd (frInsertTerm u Y) c = frInsertTerm u (frMergeAdd Y c) := by
  obtain ⟨um, uc⟩ := u
  induction Y with
  | nil => rfl
  | cons head Y' ih =>
      obtain ⟨v, ve⟩ := head
      cases huv : csrCompare um v with
      | eq =>
          have hum_eq : um = v := csrCompareEq_of um v huv
          rw [frInsertTermEqE um uc v ve Y' huv, frMergeAddCons,
              frMergeAddCons (v, ve) Y' c, hum_eq,
              frInsertTermMergeSame v uc ve (frMergeAdd Y' c)]
      | lt =>
          rw [frInsertTermLtE um uc v ve Y' huv, frMergeAddCons, frMergeAddCons (v, ve) Y' c]
      | gt =>
          rw [frInsertTermGtE um uc v ve Y' huv, frMergeAddCons (v, ve) (frInsertTerm (um, uc) Y') c,
              frMergeAddCons (v, ve) Y' c, ih,
              frInsertTermComm v ve um uc (frMergeAdd Y' c)]
theorem frMergeAddAssoc (a b c : FrNF) :
    frMergeAdd (frMergeAdd a b) c = frMergeAdd a (frMergeAdd b c) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show frMergeAdd (frInsertTerm u (frMergeAdd a' b)) c
        = frInsertTerm u (frMergeAdd a' (frMergeAdd b c))
      rw [frMergeAddInsertTermLeft u (frMergeAdd a' b) c, ih]
theorem frMergeAddSwap (a b acc : FrNF) :
    frMergeAdd a (frMergeAdd b acc) = frMergeAdd b (frMergeAdd a acc) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show frInsertTerm u (frMergeAdd a' (frMergeAdd b acc))
        = frMergeAdd b (frInsertTerm u (frMergeAdd a' acc))
      rw [ih, frInsertTerm_mergeAdd u b (frMergeAdd a' acc)]

/-! ## The strict-sortedness invariant -/

def frBelowHead (m : List Nat) : FrNF → Bool
  | [] => true
  | (p, _) :: _ =>
      match csrCompare m p with
      | CsrMonoOrd.lt => true
      | CsrMonoOrd.eq => false
      | CsrMonoOrd.gt => false
def frNFSorted : FrNF → Bool
  | [] => true
  | (m, _) :: rest => frBelowHead m rest && frNFSorted rest
theorem frBelowHeadNil (m : List Nat) : frBelowHead m [] = true := rfl
theorem frBelowHeadConsTrue (m p : List Nat) (e : Nat × Nat) (rest : FrNF)
    (h : csrCompare m p = CsrMonoOrd.lt) : frBelowHead m ((p, e) :: rest) = true := by
  show (match csrCompare m p with
        | CsrMonoOrd.lt => true
        | CsrMonoOrd.eq => false
        | CsrMonoOrd.gt => false) = true
  rw [h]
theorem frBelowHeadConsLt (m p : List Nat) (e : Nat × Nat) (rest : FrNF)
    (h : frBelowHead m ((p, e) :: rest) = true) : csrCompare m p = CsrMonoOrd.lt := by
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
theorem frNFSortedCons (m : List Nat) (c : Nat × Nat) (rest : FrNF) :
    frNFSorted ((m, c) :: rest) = (frBelowHead m rest && frNFSorted rest) := rfl
theorem frBelowHeadInsert (q m : List Nat) (c : Nat × Nat) (B : FrNF)
    (hq : csrCompare q m = CsrMonoOrd.lt) (hB : frBelowHead q B = true) :
    frBelowHead q (frInsertTerm (m, c) B) = true := by
  cases B with
  | nil => exact frBelowHeadConsTrue q m c [] hq
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq => rw [frInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [frInsertTermLtE m c p e rest hmp]; exact frBelowHeadConsTrue q m c ((p, e) :: rest) hq
      | gt =>
          rw [frInsertTermGtE m c p e rest hmp]
          exact frBelowHeadConsTrue q p e (frInsertTerm (m, c) rest) (frBelowHeadConsLt q p e rest hB)
theorem frInsertPreservesSorted (m : List Nat) (c : Nat × Nat) (B : FrNF)
    (hB : frNFSorted B = true) : frNFSorted (frInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hbelow : frBelowHead p rest = true := csrAndTrueLeft _ _ hB
      have hrest : frNFSorted rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq => rw [frInsertTermEqE m c p e rest hmp]; exact hB
      | lt =>
          rw [frInsertTermLtE m c p e rest hmp, frNFSortedCons]
          exact csrAndIntro _ _ (frBelowHeadConsTrue m p e rest hmp) hB
      | gt =>
          rw [frInsertTermGtE m c p e rest hmp, frNFSortedCons]
          have hpm : csrCompare p m = CsrMonoOrd.lt := csrCompareSwapGt m p hmp
          exact csrAndIntro _ _
            (frBelowHeadInsert p m c rest hpm hbelow) (ih hrest)
theorem frInsertFront (m : List Nat) (c : Nat × Nat) (B : FrNF) (h : frBelowHead m B = true) :
    frInsertTerm (m, c) B = (m, c) :: B := by
  cases B with
  | nil => rfl
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      exact frInsertTermLtE m c p e rest (frBelowHeadConsLt m p e rest h)
theorem frMergeAddNilRight (A : FrNF) (hA : frNFSorted A = true) : frMergeAdd A [] = A := by
  induction A with
  | nil => rfl
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      have hbelow : frBelowHead m a' = true := csrAndTrueLeft _ _ hA
      have hrest : frNFSorted a' = true := csrAndTrueRight _ _ hA
      show frInsertTerm (m, c) (frMergeAdd a' []) = (m, c) :: a'
      rw [ih hrest, frInsertFront m c a' hbelow]
theorem frMergeAddComm (A B : FrNF) (hA : frNFSorted A = true) (hB : frNFSorted B = true) :
    frMergeAdd A B = frMergeAdd B A := by
  have h := frMergeAddSwap A B []
  rw [frMergeAddNilRight B hB, frMergeAddNilRight A hA] at h
  exact h
theorem frMergeAddPreservesSorted (A B : FrNF) (hB : frNFSorted B = true) :
    frNFSorted (frMergeAdd A B) = true := by
  induction A with
  | nil => exact hB
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      show frNFSorted (frInsertTerm (m, c) (frMergeAdd a' B)) = true
      exact frInsertPreservesSorted m c (frMergeAdd a' B) ih

/-! ## The multiplicative convolution (word CONCATENATION × coefficient product) -/

/-- A single term `(m, c)` times a polynomial (right multiply): word product is the cons-only `frWordCat`
(NON-commutative), coefficient product is `frCoeffMul`. -/
def frTermMul (m : List Nat) (c : Nat × Nat) : FrNF → FrNF
  | [] => []
  | (n, d) :: rest => frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c rest)
/-- The Cauchy convolution of two polynomials. -/
def frMulConvolve : FrNF → FrNF → FrNF
  | [], _ => []
  | (m, c) :: rest, b => frMergeAdd (frTermMul m c b) (frMulConvolve rest b)
theorem frTermMulNil (m : List Nat) (c : Nat × Nat) : frTermMul m c [] = [] := rfl
theorem frTermMulCons (m : List Nat) (c : Nat × Nat) (n : List Nat) (d : Nat × Nat) (rest : FrNF) :
    frTermMul m c ((n, d) :: rest) = frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c rest) :=
  rfl
theorem frMulConvolveNil (b : FrNF) : frMulConvolve [] b = [] := rfl
theorem frMulConvolveCons (m : List Nat) (c : Nat × Nat) (rest b : FrNF) :
    frMulConvolve ((m, c) :: rest) b = frMergeAdd (frTermMul m c b) (frMulConvolve rest b) := rfl

theorem frTermMulSorted (m : List Nat) (c : Nat × Nat) (B : FrNF) :
    frNFSorted (frTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show frNFSorted (frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c rest)) = true
      exact frInsertPreservesSorted (frWordCat m n) (frCoeffMul c d) (frTermMul m c rest) ih
theorem frMulConvolveSorted (A B : FrNF) : frNFSorted (frMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show frNFSorted (frMergeAdd (frTermMul m c B) (frMulConvolve rest B)) = true
      exact frMergeAddPreservesSorted (frTermMul m c B) (frMulConvolve rest B) ih

/-- ★ termMul commutes with a single insertion (coefficients distribute via `frCoeffMulAddRight`). -/
theorem frTermMul_insertTerm (m : List Nat) (c : Nat × Nat) (n : List Nat) (d : Nat × Nat) (B : FrNF) :
    frTermMul m c (frInsertTerm (n, d) B)
      = frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [frInsertTermEqE n d p e rest hnp, frTermMulCons m c p (frCoeffAdd e d) rest,
              frTermMulCons m c p e rest, hnp_eq,
              frInsertTermMergeSame (frWordCat m p) (frCoeffMul c d) (frCoeffMul c e)
                (frTermMul m c rest), frCoeffMulAddRight c e d]
      | lt =>
          rw [frInsertTermLtE n d p e rest hnp, frTermMulCons m c n d ((p, e) :: rest),
              frTermMulCons m c p e rest]
      | gt =>
          rw [frInsertTermGtE n d p e rest hnp, frTermMulCons m c p e (frInsertTerm (n, d) rest),
              ih, frTermMulCons m c p e rest,
              frInsertTermComm (frWordCat m p) (frCoeffMul c e) (frWordCat m n) (frCoeffMul c d)
                (frTermMul m c rest)]

theorem frTermMul_merge (m : List Nat) (c : Nat × Nat) (B C : FrNF) :
    frTermMul m c (frMergeAdd B C) = frMergeAdd (frTermMul m c B) (frTermMul m c C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show frTermMul m c (frInsertTerm (n, d) (frMergeAdd B' C))
        = frMergeAdd (frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c B')) (frTermMul m c C)
      rw [frTermMul_insertTerm m c n d (frMergeAdd B' C), ih,
          frMergeAddInsertTermLeft (frWordCat m n, frCoeffMul c d) (frTermMul m c B') (frTermMul m c C)]

/-- ★ RIGHT annihilation `a·0 = 0` (the left annihilation `0·a = 0` is `frMulConvolveNil`, rfl). -/
theorem frMulConvolveAnnihil (A : FrNF) : frMulConvolve A [] = [] := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show frMergeAdd (frTermMul m c []) (frMulConvolve rest []) = []
      rw [frTermMulNil m c, frMergeAddNilLeft, ih]

/-- Rearrange a merge of four sorted NFs, swapping the inner two. -/
theorem frMergeAdd4Swap (a b c d : FrNF)
    (hb : frNFSorted b = true) (hc : frNFSorted c = true) :
    frMergeAdd (frMergeAdd a b) (frMergeAdd c d)
      = frMergeAdd (frMergeAdd a c) (frMergeAdd b d) := by
  rw [frMergeAddAssoc a b (frMergeAdd c d), ← frMergeAddAssoc b c d,
      frMergeAddComm b c hb hc, frMergeAddAssoc c b d, ← frMergeAddAssoc a c (frMergeAdd b d)]

/-- ★ left distributivity: `A · (B + C) = A·B + A·C`. -/
theorem frMulConvolve_leftDistrib (A B C : FrNF) :
    frMulConvolve A (frMergeAdd B C)
      = frMergeAdd (frMulConvolve A B) (frMulConvolve A C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show frMergeAdd (frTermMul m c (frMergeAdd B C)) (frMulConvolve A' (frMergeAdd B C))
        = frMergeAdd (frMergeAdd (frTermMul m c B) (frMulConvolve A' B))
            (frMergeAdd (frTermMul m c C) (frMulConvolve A' C))
      rw [frTermMul_merge m c B C, ih]
      exact frMergeAdd4Swap (frTermMul m c B) (frTermMul m c C) (frMulConvolve A' B)
        (frMulConvolve A' C) (frTermMulSorted m c C) (frMulConvolveSorted A' B)

/-- termMul distributes over a coefficient sum. -/
theorem frTermMul_coeffAdd (m : List Nat) (c1 c2 : Nat × Nat) (Z : FrNF) :
    frTermMul m (frCoeffAdd c1 c2) Z = frMergeAdd (frTermMul m c1 Z) (frTermMul m c2 Z) := by
  induction Z with
  | nil => rfl
  | cons head Z' ih =>
      obtain ⟨n, d⟩ := head
      show frInsertTerm (frWordCat m n, frCoeffMul (frCoeffAdd c1 c2) d) (frTermMul m (frCoeffAdd c1 c2) Z')
        = frMergeAdd (frInsertTerm (frWordCat m n, frCoeffMul c1 d) (frTermMul m c1 Z'))
            (frInsertTerm (frWordCat m n, frCoeffMul c2 d) (frTermMul m c2 Z'))
      rw [frMergeAddInsertTermLeft (frWordCat m n, frCoeffMul c1 d) (frTermMul m c1 Z')
            (frInsertTerm (frWordCat m n, frCoeffMul c2 d) (frTermMul m c2 Z')),
          ← frInsertTerm_mergeAdd (frWordCat m n, frCoeffMul c2 d) (frTermMul m c1 Z') (frTermMul m c2 Z'),
          frInsertTermMergeSame (frWordCat m n) (frCoeffMul c1 d) (frCoeffMul c2 d)
            (frMergeAdd (frTermMul m c1 Z') (frTermMul m c2 Z')),
          ih, frCoeffAddMulRight c1 c2 d, frCoeffAddComm (frCoeffMul c1 d) (frCoeffMul c2 d)]

/-- convolving after one insertion into the first argument. -/
theorem frConvolve_insertTermLeft (m : List Nat) (c : Nat × Nat) (W Z : FrNF) :
    frMulConvolve (frInsertTerm (m, c) W) Z
      = frMergeAdd (frTermMul m c Z) (frMulConvolve W Z) := by
  induction W with
  | nil => rfl
  | cons head W' ih =>
      obtain ⟨p, g⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [frInsertTermEqE m c p g W' hmp, frMulConvolveCons p (frCoeffAdd g c) W' Z,
              frMulConvolveCons p g W' Z, hmeqp,
              frTermMul_coeffAdd p g c Z,
              frMergeAddAssoc (frTermMul p g Z) (frTermMul p c Z) (frMulConvolve W' Z),
              frMergeAddSwap (frTermMul p g Z) (frTermMul p c Z) (frMulConvolve W' Z)]
      | lt =>
          rw [frInsertTermLtE m c p g W' hmp, frMulConvolveCons m c ((p, g) :: W') Z]
      | gt =>
          rw [frInsertTermGtE m c p g W' hmp,
              frMulConvolveCons p g (frInsertTerm (m, c) W') Z, ih,
              frMulConvolveCons p g W' Z,
              frMergeAddSwap (frTermMul p g Z) (frTermMul m c Z) (frMulConvolve W' Z)]

/-- ★ right distributivity: `(X + Y) · Z = X·Z + Y·Z`. -/
theorem frMulConvolve_rightDistrib (X Y Z : FrNF) :
    frMulConvolve (frMergeAdd X Y) Z
      = frMergeAdd (frMulConvolve X Z) (frMulConvolve Y Z) := by
  induction X with
  | nil => rfl
  | cons head X' ih =>
      obtain ⟨m, c⟩ := head
      show frMulConvolve (frInsertTerm (m, c) (frMergeAdd X' Y)) Z
        = frMergeAdd (frMergeAdd (frTermMul m c Z) (frMulConvolve X' Z)) (frMulConvolve Y Z)
      rw [frConvolve_insertTermLeft m c (frMergeAdd X' Y) Z, ih,
          frMergeAddAssoc (frTermMul m c Z) (frMulConvolve X' Z) (frMulConvolve Y Z)]

/-- termMul composition: word CONCATENATION `frWordCat` replaces the multiset union of the commutative rung. -/
theorem frTermMul_compose (m : List Nat) (c : Nat × Nat) (n : List Nat) (d : Nat × Nat) (C : FrNF) :
    frTermMul (frWordCat m n) (frCoeffMul c d) C = frTermMul m c (frTermMul n d C) := by
  induction C with
  | nil => rfl
  | cons head C' ih =>
      obtain ⟨p, f⟩ := head
      show frInsertTerm (frWordCat (frWordCat m n) p, frCoeffMul (frCoeffMul c d) f)
            (frTermMul (frWordCat m n) (frCoeffMul c d) C')
        = frTermMul m c (frInsertTerm (frWordCat n p, frCoeffMul d f) (frTermMul n d C'))
      rw [frTermMul_insertTerm m c (frWordCat n p) (frCoeffMul d f) (frTermMul n d C'), ih,
          frWordCatAssoc m n p, frCoeffMulAssoc c d f]

/-- convolving a termMul equals termMul of a convolve. -/
theorem frTermMul_convolve (m : List Nat) (c : Nat × Nat) (B C : FrNF) :
    frMulConvolve (frTermMul m c B) C = frTermMul m c (frMulConvolve B C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show frMulConvolve (frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c B')) C
        = frTermMul m c (frMergeAdd (frTermMul n d C) (frMulConvolve B' C))
      rw [frConvolve_insertTermLeft (frWordCat m n) (frCoeffMul c d) (frTermMul m c B') C, ih,
          frTermMul_merge m c (frTermMul n d C) (frMulConvolve B' C),
          frTermMul_compose m c n d C]

/-- ★ associativity of the convolution: `(A·B)·C = A·(B·C)`. -/
theorem frMulConvolveAssoc (A B C : FrNF) :
    frMulConvolve (frMulConvolve A B) C = frMulConvolve A (frMulConvolve B C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show frMulConvolve (frMergeAdd (frTermMul m c B) (frMulConvolve A' B)) C
        = frMergeAdd (frTermMul m c (frMulConvolve B C)) (frMulConvolve A' (frMulConvolve B C))
      rw [frMulConvolve_rightDistrib (frTermMul m c B) (frMulConvolve A' B) C, ih,
          frTermMul_convolve m c B C]

/-- termMul by the empty word and coefficient `(1,0)` rebuilds a sorted NF unchanged (feeds the LEFT unit). -/
theorem frTermMulIdent : (A : FrNF) → frNFSorted A = true → frTermMul [] (1, 0) A = A
  | [], _ => rfl
  | (n, d) :: A', hA => by
      have hbelow : frBelowHead n A' = true := csrAndTrueLeft _ _ hA
      have hA' : frNFSorted A' = true := csrAndTrueRight _ _ hA
      have ih := frTermMulIdent A' hA'
      show frInsertTerm (frWordCat [] n, frCoeffMul (1, 0) d) (frTermMul [] (1, 0) A') = (n, d) :: A'
      rw [ih, frCoeffOneMul d]
      show frInsertTerm (n, d) A' = (n, d) :: A'
      exact frInsertFront n d A' hbelow

/-- ★ multiplicative LEFT unit: `[([], (1,0))] · A = A` for a sorted NF. -/
theorem frMulConvolveUnitLeft (A : FrNF) (hA : frNFSorted A = true) :
    frMulConvolve [([], (1, 0))] A = A := by
  show frMergeAdd (frTermMul [] (1, 0) A) [] = A
  rw [frTermMulIdent A hA, frMergeAddNilRight A hA]

/-- ★ multiplicative RIGHT unit: `A · [([], (1,0))] = A` for a sorted NF. -/
theorem frMulConvolveUnitRight : (A : FrNF) → frNFSorted A = true → frMulConvolve A [([], (1, 0))] = A
  | [], _ => rfl
  | (m, c) :: A', hAs => by
      have hbelow : frBelowHead m A' = true := csrAndTrueLeft _ _ hAs
      have hAs' : frNFSorted A' = true := csrAndTrueRight _ _ hAs
      have ih := frMulConvolveUnitRight A' hAs'
      show frMergeAdd (frTermMul m c [([], (1, 0))]) (frMulConvolve A' [([], (1, 0))]) = (m, c) :: A'
      rw [frTermMulCons m c [] (1, 0) [], frTermMulNil m c, frWordCatNilRight m, frCoeffMulOne c,
          frMergeAddInsertTermLeft (m, c) [] (frMulConvolve A' [([], (1, 0))]), frMergeAddNilLeft,
          ih, frInsertFront m c A' hbelow]

/-! ## Negation of a normal form (negate every coefficient) -/

def frNegate : FrNF → FrNF
  | [] => []
  | (m, c) :: rest => (m, frCoeffNeg c) :: frNegate rest
theorem frNegateCons (m : List Nat) (c : Nat × Nat) (rest : FrNF) :
    frNegate ((m, c) :: rest) = (m, frCoeffNeg c) :: frNegate rest := rfl
theorem frNegateBelowHead (m : List Nat) (A : FrNF) :
    frBelowHead m (frNegate A) = frBelowHead m A := by
  cases A with
  | nil => rfl
  | cons head rest => obtain ⟨p, e⟩ := head; rfl
theorem frNegateSorted (A : FrNF) (hA : frNFSorted A = true) : frNFSorted (frNegate A) = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      have hbelow : frBelowHead m rest = true := csrAndTrueLeft _ _ hA
      have hrest : frNFSorted rest = true := csrAndTrueRight _ _ hA
      rw [frNegateCons, frNFSortedCons]
      exact csrAndIntro _ _ (by rw [frNegateBelowHead m rest]; exact hbelow) (ih hrest)
theorem frNegateInvol (A : FrNF) : frNegate (frNegate A) = A := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      rw [frNegateCons, frNegateCons, frCoeffNegNeg c, ih]
theorem frNegate_insertTerm (m : List Nat) (c : Nat × Nat) (X : FrNF) :
    frNegate (frInsertTerm (m, c) X) = frInsertTerm (m, frCoeffNeg c) (frNegate X) := by
  induction X with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          rw [frInsertTermEqE m c p e rest hmp, frNegateCons, frNegateCons,
              frInsertTermEqE m (frCoeffNeg c) p (frCoeffNeg e) (frNegate rest) hmp,
              frCoeffNegAdd e c]
      | lt =>
          rw [frInsertTermLtE m c p e rest hmp, frNegateCons, frNegateCons,
              frInsertTermLtE m (frCoeffNeg c) p (frCoeffNeg e) (frNegate rest) hmp]
      | gt =>
          rw [frInsertTermGtE m c p e rest hmp, frNegateCons, frNegateCons, ih,
              frInsertTermGtE m (frCoeffNeg c) p (frCoeffNeg e) (frNegate rest) hmp]
theorem frNegate_mergeAdd (A B : FrNF) :
    frNegate (frMergeAdd A B) = frMergeAdd (frNegate A) (frNegate B) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show frNegate (frInsertTerm (m, c) (frMergeAdd A' B))
        = frInsertTerm (m, frCoeffNeg c) (frMergeAdd (frNegate A') (frNegate B))
      rw [frNegate_insertTerm m c (frMergeAdd A' B), ih]

/-! ## The all-zero-valued predicate and its closure lemmas -/

def frNFAllZero : FrNF → Bool
  | [] => true
  | (_, c) :: rest => frCoeffIsZero c && frNFAllZero rest
theorem frNFAllZeroCons (m : List Nat) (c : Nat × Nat) (rest : FrNF) :
    frNFAllZero ((m, c) :: rest) = (frCoeffIsZero c && frNFAllZero rest) := rfl
theorem frNegatePreservesAllZero (A : FrNF) : frNFAllZero (frNegate A) = frNFAllZero A := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      rw [frNegateCons, frNFAllZeroCons, frNFAllZeroCons, frCoeffNegIsZero c, ih]
theorem frInsertTermAllZero (m : List Nat) (c : Nat × Nat) (B : FrNF)
    (hc : frCoeffIsZero c = true) (hB : frNFAllZero B = true) :
    frNFAllZero (frInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rw [frInsertTermNil m c, frNFAllZeroCons]; exact csrAndIntro _ _ hc rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have he : frCoeffIsZero e = true := csrAndTrueLeft _ _ hB
      have hrest : frNFAllZero rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq =>
          rw [frInsertTermEqE m c p e rest hmp, frNFAllZeroCons]
          exact csrAndIntro _ _ (frCoeffAddZeroValued e c he hc) hrest
      | lt =>
          rw [frInsertTermLtE m c p e rest hmp, frNFAllZeroCons]
          exact csrAndIntro _ _ hc hB
      | gt =>
          rw [frInsertTermGtE m c p e rest hmp, frNFAllZeroCons]
          exact csrAndIntro _ _ he (ih hrest)
theorem frMergeAddAllZero (A B : FrNF) (hA : frNFAllZero A = true) (hB : frNFAllZero B = true) :
    frNFAllZero (frMergeAdd A B) = true := by
  induction A with
  | nil => exact hB
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hc : frCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hA' : frNFAllZero A' = true := csrAndTrueRight _ _ hA
      show frNFAllZero (frInsertTerm (m, c) (frMergeAdd A' B)) = true
      exact frInsertTermAllZero m c (frMergeAdd A' B) hc (ih hA')

/-! ## The `frEvalCross` semantic model: the per-word coefficient sum -/

def frCondCoeff : Bool → (Nat × Nat) → (Nat × Nat)
  | true, d => d
  | false, _ => (0, 0)
theorem frCondCoeffTrue (d : Nat × Nat) : frCondCoeff true d = d := rfl
theorem frCondCoeffFalse (d : Nat × Nat) : frCondCoeff false d = (0, 0) := rfl
theorem frCondCoeffZero (b : Bool) (c : Nat × Nat) (hc : frCoeffIsZero c = true) :
    frCoeffIsZero (frCondCoeff b c) = true := by
  cases b with
  | true => exact hc
  | false => rfl

theorem frCoeffAddSwap13 (x y z : Nat × Nat) :
    frCoeffAdd x (frCoeffAdd y z) = frCoeffAdd y (frCoeffAdd x z) := by
  rw [← frCoeffAddAssoc x y z, frCoeffAddComm x y, frCoeffAddAssoc y x z]

theorem frCoeffNegAddIsZero (c : Nat × Nat) : frCoeffIsZero (frCoeffAdd (frCoeffNeg c) c) = true := by
  obtain ⟨p, n⟩ := c
  show Nat.beq (n + p) (p + n) = true
  rw [Nat.add_comm n p]; exact csrNatBeqRefl (p + n)

/-- A word `m` distinct from `q` (witnessed by `csrCompare m q = lt`) has `csrNatListEq m q = false`. -/
theorem frNatListEqFalseOfLt (m q : List Nat) (h : csrCompare m q = CsrMonoOrd.lt) :
    csrNatListEq m q = false := by
  cases hb : csrNatListEq m q with
  | false => rfl
  | true =>
      have hmq : m = q := csrNatListEq_eq m q hb
      rw [csrCompareOfEq m q hmq] at h
      exact CsrMonoOrd.noConfusion h

/-- The per-word coefficient sum of a normal form. -/
def frEvalCross (m : List Nat) : FrNF → (Nat × Nat)
  | [] => (0, 0)
  | (p, c) :: rest => frCoeffAdd (frCondCoeff (csrNatListEq m p) c) (frEvalCross m rest)
theorem frEvalCrossNil (m : List Nat) : frEvalCross m [] = (0, 0) := rfl
theorem frEvalCrossCons (m p : List Nat) (c : Nat × Nat) (rest : FrNF) :
    frEvalCross m ((p, c) :: rest) = frCoeffAdd (frCondCoeff (csrNatListEq m p) c) (frEvalCross m rest) :=
  rfl

theorem frEvalCross_insertTerm (m n : List Nat) (d : Nat × Nat) (B : FrNF) :
    frEvalCross m (frInsertTerm (n, d) B)
      = frCoeffAdd (frCondCoeff (csrNatListEq m n) d) (frEvalCross m B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hn_eq : n = p := csrCompareEq_of n p hnp
          rw [frInsertTermEqE n d p e rest hnp, frEvalCrossCons, frEvalCrossCons, hn_eq]
          cases hmp : csrNatListEq m p with
          | true =>
              rw [frCondCoeffTrue, frCondCoeffTrue, frCondCoeffTrue,
                  frCoeffAddAssoc e d (frEvalCross m rest), frCoeffAddSwap13 e d (frEvalCross m rest)]
          | false =>
              rw [frCondCoeffFalse, frCondCoeffFalse, frCondCoeffFalse,
                  frCoeffAddZeroLeft, frCoeffAddZeroLeft]
      | lt =>
          rw [frInsertTermLtE n d p e rest hnp, frEvalCrossCons]
      | gt =>
          rw [frInsertTermGtE n d p e rest hnp, frEvalCrossCons, ih, frEvalCrossCons]
          exact frCoeffAddSwap13 (frCondCoeff (csrNatListEq m p) e)
            (frCondCoeff (csrNatListEq m n) d) (frEvalCross m rest)

theorem frEvalCross_mergeAdd (m : List Nat) (A B : FrNF) :
    frEvalCross m (frMergeAdd A B) = frCoeffAdd (frEvalCross m A) (frEvalCross m B) := by
  induction A with
  | nil => rw [frMergeAddNilLeft, frEvalCrossNil, frCoeffAddZeroLeft]
  | cons head A' ih =>
      obtain ⟨p, c⟩ := head
      show frEvalCross m (frInsertTerm (p, c) (frMergeAdd A' B))
        = frCoeffAdd (frCoeffAdd (frCondCoeff (csrNatListEq m p) c) (frEvalCross m A')) (frEvalCross m B)
      rw [frEvalCross_insertTerm m p c (frMergeAdd A' B), ih,
          frCoeffAddAssoc (frCondCoeff (csrNatListEq m p) c) (frEvalCross m A') (frEvalCross m B)]

theorem frAllZero_evalZero (m : List Nat) (W : FrNF) (hW : frNFAllZero W = true) :
    frCoeffIsZero (frEvalCross m W) = true := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      have hc : frCoeffIsZero c = true := csrAndTrueLeft _ _ hW
      have hrest : frNFAllZero rest = true := csrAndTrueRight _ _ hW
      rw [frEvalCrossCons]
      exact frCoeffAddZeroValued _ _ (frCondCoeffZero (csrNatListEq m p) c hc) (ih hrest)

theorem frEvalBelowZero (m : List Nat) (W : FrNF) (hbelow : frBelowHead m W = true)
    (hsorted : frNFSorted W = true) : frEvalCross m W = (0, 0) := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨q, e⟩ := head
      have hmq : csrCompare m q = CsrMonoOrd.lt := frBelowHeadConsLt m q e rest hbelow
      have hmqEq : csrNatListEq m q = false := frNatListEqFalseOfLt m q hmq
      have hqbelow : frBelowHead q rest = true := csrAndTrueLeft _ _ hsorted
      have hrest : frNFSorted rest = true := csrAndTrueRight _ _ hsorted
      have hmrest : frBelowHead m rest = true := by
        cases rest with
        | nil => rfl
        | cons head2 rest2 =>
            obtain ⟨r, f⟩ := head2
            have hqr : csrCompare q r = CsrMonoOrd.lt := frBelowHeadConsLt q r f rest2 hqbelow
            exact frBelowHeadConsTrue m r f rest2 (csrCompareTransLt m q r hmq hqr)
      rw [frEvalCrossCons, hmqEq, frCondCoeffFalse, frCoeffAddZeroLeft, ih hmrest hrest]

theorem frSortedEvalZero_allZero (W : FrNF) (hsorted : frNFSorted W = true)
    (hzero : ∀ m, frCoeffIsZero (frEvalCross m W) = true) : frNFAllZero W = true := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      have hbelow : frBelowHead p rest = true := csrAndTrueLeft _ _ hsorted
      have hrest : frNFSorted rest = true := csrAndTrueRight _ _ hsorted
      have hevalPrest : frEvalCross p rest = (0, 0) := frEvalBelowZero p rest hbelow hrest
      have hc : frCoeffIsZero c = true := by
        have h := hzero p
        rw [frEvalCrossCons, csrNatListEqRefl p, hevalPrest, frCoeffAddZeroRight, frCondCoeffTrue] at h
        exact h
      have hrestZero : ∀ mm, frCoeffIsZero (frEvalCross mm rest) = true := by
        intro mm
        cases hmp : csrNatListEq mm p with
        | true =>
            have hmeqp : mm = p := csrNatListEq_eq mm p hmp
            rw [hmeqp, hevalPrest]; rfl
        | false =>
            have h := hzero mm
            rw [frEvalCrossCons, hmp, frCondCoeffFalse, frCoeffAddZeroLeft] at h
            exact h
      rw [frNFAllZeroCons]
      exact csrAndIntro _ _ hc (ih hrest hrestZero)

/-- ★ The all-zero cancellation: if `mergeAdd X Z` and `Z` are both all-zero (with `X` sorted), so is `X`. -/
theorem frMergeAddAllZeroCancel (X Z : FrNF) (hX : frNFSorted X = true)
    (hXZ : frNFAllZero (frMergeAdd X Z) = true) (hZ : frNFAllZero Z = true) :
    frNFAllZero X = true := by
  apply frSortedEvalZero_allZero X hX
  intro m
  have hmerge : frCoeffIsZero (frEvalCross m (frMergeAdd X Z)) = true := frAllZero_evalZero m _ hXZ
  rw [frEvalCross_mergeAdd m X Z] at hmerge
  exact frCoeffAddCancelZero (frEvalCross m X) (frEvalCross m Z) hmerge (frAllZero_evalZero m Z hZ)

theorem frCondCoeffNeg (b : Bool) (c : Nat × Nat) :
    frCondCoeff b (frCoeffNeg c) = frCoeffNeg (frCondCoeff b c) := by
  cases b with | true => rfl | false => rfl

theorem frEvalCross_negate (m : List Nat) (A : FrNF) :
    frEvalCross m (frNegate A) = frCoeffNeg (frEvalCross m A) := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      rw [frNegateCons, frEvalCrossCons, frEvalCrossCons, ih, frCoeffNegAdd, frCondCoeffNeg]

/-- ★ a polynomial plus its own negation is all-zero-valued (the crux the additive inverse rests on). -/
theorem frMergeAddSelfNegAllZero (A : FrNF) (hA : frNFSorted A = true) :
    frNFAllZero (frMergeAdd A (frNegate A)) = true := by
  apply frSortedEvalZero_allZero _ (frMergeAddPreservesSorted A (frNegate A) (frNegateSorted A hA))
  intro m
  rw [frEvalCross_mergeAdd m A (frNegate A), frEvalCross_negate m A]
  exact frCoeffAddNegIsZero (frEvalCross m A)

/-! ## Multiplying by a zero-valued polynomial, and negation through multiplication -/

theorem frCoeffMulZeroValuedLeft (c d : Nat × Nat) (hc : frCoeffIsZero c = true) :
    frCoeffIsZero (frCoeffMul c d) = true := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
  have hk : c1 = c2 := csrNatEqOfBeq c1 c2 hc
  show Nat.beq (c1 * d1 + c2 * d2) (c1 * d2 + c2 * d1) = true
  rw [hk, Nat.add_comm (c2 * d1) (c2 * d2)]
  exact csrNatBeqRefl (c2 * d2 + c2 * d1)

theorem frCoeffMulZeroValuedRight (c d : Nat × Nat) (hd : frCoeffIsZero d = true) :
    frCoeffIsZero (frCoeffMul c d) = true := by
  rw [frCoeffMulComm c d]; exact frCoeffMulZeroValuedLeft d c hd

theorem frCoeffNegMulRight (c d : Nat × Nat) :
    frCoeffNeg (frCoeffMul c d) = frCoeffMul c (frCoeffNeg d) := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d; rfl

theorem frTermMulCoeffZeroAllZero (m : List Nat) (c : Nat × Nat) (hc : frCoeffIsZero c = true) (B : FrNF) :
    frNFAllZero (frTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show frNFAllZero (frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c rest)) = true
      exact frInsertTermAllZero _ _ _ (frCoeffMulZeroValuedLeft c d hc) ih

theorem frTermMulRightAllZero (m : List Nat) (c : Nat × Nat) (B : FrNF) (hB : frNFAllZero B = true) :
    frNFAllZero (frTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      have hd : frCoeffIsZero d = true := csrAndTrueLeft _ _ hB
      have hrest : frNFAllZero rest = true := csrAndTrueRight _ _ hB
      show frNFAllZero (frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c rest)) = true
      exact frInsertTermAllZero _ _ _ (frCoeffMulZeroValuedRight c d hd) (ih hrest)

theorem frMulConvolveLeftAllZero (A B : FrNF) (hA : frNFAllZero A = true) :
    frNFAllZero (frMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hc : frCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hA' : frNFAllZero A' = true := csrAndTrueRight _ _ hA
      show frNFAllZero (frMergeAdd (frTermMul m c B) (frMulConvolve A' B)) = true
      exact frMergeAddAllZero _ _ (frTermMulCoeffZeroAllZero m c hc B) (ih hA')

theorem frMulConvolveRightAllZero (A B : FrNF) (hB : frNFAllZero B = true) :
    frNFAllZero (frMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show frNFAllZero (frMergeAdd (frTermMul m c B) (frMulConvolve A' B)) = true
      exact frMergeAddAllZero _ _ (frTermMulRightAllZero m c B hB) ih

theorem frNegate_termMulLeft (m : List Nat) (c : Nat × Nat) (B : FrNF) :
    frNegate (frTermMul m c B) = frTermMul m (frCoeffNeg c) B := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show frNegate (frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c rest))
        = frInsertTerm (frWordCat m n, frCoeffMul (frCoeffNeg c) d) (frTermMul m (frCoeffNeg c) rest)
      rw [frNegate_insertTerm (frWordCat m n) (frCoeffMul c d) (frTermMul m c rest), ih,
          frCoeffNegMulLeft c d]

theorem frNegate_termMulRight (m : List Nat) (c : Nat × Nat) (B : FrNF) :
    frNegate (frTermMul m c B) = frTermMul m c (frNegate B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show frNegate (frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c rest))
        = frTermMul m c ((n, frCoeffNeg d) :: frNegate rest)
      rw [frNegate_insertTerm (frWordCat m n) (frCoeffMul c d) (frTermMul m c rest), ih,
          frTermMulCons m c n (frCoeffNeg d) (frNegate rest), frCoeffNegMulRight c d]

theorem frNegate_mulConvolveLeft (A B : FrNF) :
    frNegate (frMulConvolve A B) = frMulConvolve (frNegate A) B := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show frNegate (frMergeAdd (frTermMul m c B) (frMulConvolve A' B))
        = frMulConvolve ((m, frCoeffNeg c) :: frNegate A') B
      rw [frNegate_mergeAdd (frTermMul m c B) (frMulConvolve A' B), frNegate_termMulLeft m c B, ih,
          frMulConvolveCons m (frCoeffNeg c) (frNegate A') B]

theorem frNegate_mulConvolveRight (A B : FrNF) :
    frNegate (frMulConvolve A B) = frMulConvolve A (frNegate B) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show frNegate (frMergeAdd (frTermMul m c B) (frMulConvolve A' B))
        = frMergeAdd (frTermMul m c (frNegate B)) (frMulConvolve A' (frNegate B))
      rw [frNegate_mergeAdd (frTermMul m c B) (frMulConvolve A' B), frNegate_termMulRight m c B, ih]

/-! ## The decision equivalence `frNFEq` and its equivalence + congruence structure -/

/-- The SUBTRACTION-FREE polynomial equality: the difference has every coefficient zero-valued. -/
def frNFEq (A B : FrNF) : Bool := frNFAllZero (frMergeAdd A (frNegate B))

theorem frNFEqRefl (A : FrNF) (hA : frNFSorted A = true) : frNFEq A A = true :=
  frMergeAddSelfNegAllZero A hA

theorem frNFEqOfEq (A B : FrNF) (hB : frNFSorted B = true) (h : A = B) : frNFEq A B = true := by
  rw [h]; exact frNFEqRefl B hB

theorem frNFEqSymm (A B : FrNF) (hA : frNFSorted A = true) (hB : frNFSorted B = true)
    (h : frNFEq A B = true) : frNFEq B A = true := by
  show frNFAllZero (frMergeAdd B (frNegate A)) = true
  have hkey : frMergeAdd B (frNegate A) = frNegate (frMergeAdd A (frNegate B)) := by
    rw [frNegate_mergeAdd A (frNegate B), frNegateInvol B]
    exact frMergeAddComm B (frNegate A) hB (frNegateSorted A hA)
  rw [hkey, frNegatePreservesAllZero]
  exact h

theorem frNFEqTrans (A B C : FrNF) (hA : frNFSorted A = true) (hB : frNFSorted B = true)
    (hC : frNFSorted C = true) (hAB : frNFEq A B = true) (hBC : frNFEq B C = true) :
    frNFEq A C = true := by
  have hnegB : frNFSorted (frNegate B) = true := frNegateSorted B hB
  have hnegC : frNFSorted (frNegate C) = true := frNegateSorted C hC
  have hrearr : frMergeAdd (frMergeAdd A (frNegate B)) (frMergeAdd B (frNegate C))
              = frMergeAdd (frMergeAdd A (frNegate C)) (frMergeAdd B (frNegate B)) := by
    rw [frMergeAdd4Swap A (frNegate B) B (frNegate C) hnegB hB,
        frMergeAdd4Swap A (frNegate C) B (frNegate B) hnegC hB,
        frMergeAddComm (frNegate B) (frNegate C) hnegB hnegC]
  have hall : frNFAllZero (frMergeAdd (frMergeAdd A (frNegate C)) (frMergeAdd B (frNegate B))) = true := by
    rw [← hrearr]; exact frMergeAddAllZero _ _ hAB hBC
  exact frMergeAddAllZeroCancel (frMergeAdd A (frNegate C)) (frMergeAdd B (frNegate B))
    (frMergeAddPreservesSorted A (frNegate C) hnegC) hall (frMergeAddSelfNegAllZero B hB)

theorem frNFEqMergeCongr (A A' B B' : FrNF) (hA' : frNFSorted A' = true) (hB : frNFSorted B = true)
    (hAA' : frNFEq A A' = true) (hBB' : frNFEq B B' = true) :
    frNFEq (frMergeAdd A B) (frMergeAdd A' B') = true := by
  show frNFAllZero (frMergeAdd (frMergeAdd A B) (frNegate (frMergeAdd A' B'))) = true
  rw [frNegate_mergeAdd A' B', frMergeAdd4Swap A B (frNegate A') (frNegate B') hB (frNegateSorted A' hA')]
  exact frMergeAddAllZero _ _ hAA' hBB'

theorem frNFEqMulCongr (A A' B B' : FrNF) (hAA' : frNFEq A A' = true) (hBB' : frNFEq B B' = true) :
    frNFEq (frMulConvolve A B) (frMulConvolve A' B') = true := by
  have step1 : frNFEq (frMulConvolve A B) (frMulConvolve A' B) = true := by
    show frNFAllZero (frMergeAdd (frMulConvolve A B) (frNegate (frMulConvolve A' B))) = true
    rw [frNegate_mulConvolveLeft A' B, ← frMulConvolve_rightDistrib A (frNegate A') B]
    exact frMulConvolveLeftAllZero (frMergeAdd A (frNegate A')) B hAA'
  have step2 : frNFEq (frMulConvolve A' B) (frMulConvolve A' B') = true := by
    show frNFAllZero (frMergeAdd (frMulConvolve A' B) (frNegate (frMulConvolve A' B'))) = true
    rw [frNegate_mulConvolveRight A' B', ← frMulConvolve_leftDistrib A' B (frNegate B')]
    exact frMulConvolveRightAllZero A' (frMergeAdd B (frNegate B')) hBB'
  exact frNFEqTrans (frMulConvolve A B) (frMulConvolve A' B) (frMulConvolve A' B')
    (frMulConvolveSorted A B) (frMulConvolveSorted A' B) (frMulConvolveSorted A' B') step1 step2

theorem frNFEqNegCongr (A A' : FrNF) (h : frNFEq A A' = true) :
    frNFEq (frNegate A) (frNegate A') = true := by
  show frNFAllZero (frMergeAdd (frNegate A) (frNegate (frNegate A'))) = true
  rw [frNegateInvol A']
  have hkey : frMergeAdd (frNegate A) A' = frNegate (frMergeAdd A (frNegate A')) := by
    rw [frNegate_mergeAdd A (frNegate A'), frNegateInvol A']
  rw [hkey, frNegatePreservesAllZero]
  exact h

theorem frNFEqNil (X : FrNF) (hX : frNFSorted X = true) (hall : frNFAllZero X = true) :
    frNFEq X [] = true := by
  show frNFAllZero (frMergeAdd X (frNegate [])) = true
  rw [show frNegate ([] : FrNF) = [] from rfl, frMergeAddNilRight X hX]
  exact hall

/-! ## The free non-commutative-ring tree carrier and its normal form -/

/-- ★ The free non-commutative-ring tree carrier: colour-tagged generators plus the additive unit `0`, the
multiplicative unit `1`, binary addition and multiplication, and the unary additive inverse `negOp`. -/
inductive FrTree where
  /-- a colour-tagged generator (variable). -/
  | gen (colour : Nat)
  /-- the additive unit `0`. -/
  | zeroOp
  /-- the multiplicative unit `1`. -/
  | oneOp
  /-- binary addition. -/
  | addOp : FrTree → FrTree → FrTree
  /-- binary multiplication (NON-commutative). -/
  | mulOp : FrTree → FrTree → FrTree
  /-- the unary additive inverse (negation). -/
  | negOp : FrTree → FrTree

/-- ★ normalize a tree to its non-commutative polynomial normal form (sorted words, `(pos, neg)` coefficients). -/
def frNormalize : FrTree → FrNF
  | .gen colour => [([colour], (1, 0))]
  | .zeroOp => []
  | .oneOp => [([], (1, 0))]
  | .addOp l r => frMergeAdd (frNormalize l) (frNormalize r)
  | .mulOp l r => frMulConvolve (frNormalize l) (frNormalize r)
  | .negOp a => frNegate (frNormalize a)

theorem frNormalize_gen (c : Nat) : frNormalize (FrTree.gen c) = [([c], (1, 0))] := rfl
theorem frNormalizeSorted (t : FrTree) : frNFSorted (frNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | addOp l r _ ihr => exact frMergeAddPreservesSorted (frNormalize l) (frNormalize r) ihr
  | mulOp l r _ _ => exact frMulConvolveSorted (frNormalize l) (frNormalize r)
  | negOp a ih => exact frNegateSorted (frNormalize a) ih

/-- rfl smokes for the normal form. -/
theorem frNormalize_zero_smoke : frNormalize FrTree.zeroOp = [] := rfl
theorem frNormalize_one_smoke : frNormalize FrTree.oneOp = [([], (1, 0))] := rfl
theorem frNormalize_negGen_smoke :
    frNormalize (FrTree.negOp (FrTree.gen 0)) = [([0], (0, 1))] := rfl

/-! ## The non-commutative-ring tree convertibility -/

/-- ★ The free convertibility of the `{+, *, 0, 1, neg}` signature over colour-tagged generators, closed under
the non-commutative-ring laws: the additive ABELIAN GROUP (associativity, commutativity, right unit, and
`addNegInverse`), the NON-commutative multiplicative monoid (associativity, BOTH units, NO `mulComm`), BOTH
distributivities, BOTH annihilations, the full congruences `addCongr` / `mulCongr` / `negCongr`, and
`refl` / `symm` / `trans`. -/
inductive RingTreeConv : FrTree → FrTree → Prop where
  | addAssoc (a b c : FrTree) :
      RingTreeConv (FrTree.addOp (FrTree.addOp a b) c) (FrTree.addOp a (FrTree.addOp b c))
  | addComm (a b : FrTree) : RingTreeConv (FrTree.addOp a b) (FrTree.addOp b a)
  | addZero (a : FrTree) : RingTreeConv (FrTree.addOp a FrTree.zeroOp) a
  /-- ★ the additive inverse: `a + neg a ≈ 0`. -/
  | addNegInverse (a : FrTree) :
      RingTreeConv (FrTree.addOp a (FrTree.negOp a)) FrTree.zeroOp
  | mulAssoc (a b c : FrTree) :
      RingTreeConv (FrTree.mulOp (FrTree.mulOp a b) c) (FrTree.mulOp a (FrTree.mulOp b c))
  | mulOne (a : FrTree) : RingTreeConv (FrTree.mulOp a FrTree.oneOp) a
  | mulOneLeft (a : FrTree) : RingTreeConv (FrTree.mulOp FrTree.oneOp a) a
  | distribLeft (a b c : FrTree) :
      RingTreeConv (FrTree.mulOp a (FrTree.addOp b c))
        (FrTree.addOp (FrTree.mulOp a b) (FrTree.mulOp a c))
  | distribRight (a b c : FrTree) :
      RingTreeConv (FrTree.mulOp (FrTree.addOp a b) c)
        (FrTree.addOp (FrTree.mulOp a c) (FrTree.mulOp b c))
  | annihilRight (a : FrTree) : RingTreeConv (FrTree.mulOp a FrTree.zeroOp) FrTree.zeroOp
  | annihilLeft (a : FrTree) : RingTreeConv (FrTree.mulOp FrTree.zeroOp a) FrTree.zeroOp
  | addCongr {leftOld leftNew rightOld rightNew : FrTree} :
      RingTreeConv leftOld leftNew → RingTreeConv rightOld rightNew →
      RingTreeConv (FrTree.addOp leftOld rightOld) (FrTree.addOp leftNew rightNew)
  | mulCongr {leftOld leftNew rightOld rightNew : FrTree} :
      RingTreeConv leftOld leftNew → RingTreeConv rightOld rightNew →
      RingTreeConv (FrTree.mulOp leftOld rightOld) (FrTree.mulOp leftNew rightNew)
  | negCongr {innerOld innerNew : FrTree} :
      RingTreeConv innerOld innerNew →
      RingTreeConv (FrTree.negOp innerOld) (FrTree.negOp innerNew)
  | refl (t : FrTree) : RingTreeConv t t
  | symm {s t : FrTree} : RingTreeConv s t → RingTreeConv t s
  | trans {s t u : FrTree} : RingTreeConv s t → RingTreeConv t u → RingTreeConv s u

/-! ## Soundness: convertible ⟹ `frNFEq` normal forms -/

/-- ★ Soundness — convertible trees have `frNFEq` normal forms. -/
theorem frNormalize_respects {s t : FrTree} (conv : RingTreeConv s t) :
    frNFEq (frNormalize s) (frNormalize t) = true := by
  induction conv with
  | addAssoc a b c =>
      exact frNFEqOfEq _ _
        (frMergeAddPreservesSorted _ _ (frMergeAddPreservesSorted _ _ (frNormalizeSorted c)))
        (frMergeAddAssoc (frNormalize a) (frNormalize b) (frNormalize c))
  | addComm a b =>
      exact frNFEqOfEq _ _
        (frMergeAddPreservesSorted _ _ (frNormalizeSorted a))
        (frMergeAddComm (frNormalize a) (frNormalize b) (frNormalizeSorted a) (frNormalizeSorted b))
  | addZero a =>
      exact frNFEqOfEq _ _ (frNormalizeSorted a)
        (frMergeAddNilRight (frNormalize a) (frNormalizeSorted a))
  | addNegInverse a =>
      exact frNFEqNil _
        (frMergeAddPreservesSorted _ _ (frNegateSorted _ (frNormalizeSorted a)))
        (frMergeAddSelfNegAllZero (frNormalize a) (frNormalizeSorted a))
  | mulAssoc a b c =>
      exact frNFEqOfEq _ _
        (frMulConvolveSorted _ _)
        (frMulConvolveAssoc (frNormalize a) (frNormalize b) (frNormalize c))
  | mulOne a =>
      exact frNFEqOfEq _ _ (frNormalizeSorted a)
        (frMulConvolveUnitRight (frNormalize a) (frNormalizeSorted a))
  | mulOneLeft a =>
      exact frNFEqOfEq _ _ (frNormalizeSorted a)
        (frMulConvolveUnitLeft (frNormalize a) (frNormalizeSorted a))
  | distribLeft a b c =>
      exact frNFEqOfEq _ _
        (frMergeAddPreservesSorted _ _ (frMulConvolveSorted _ _))
        (frMulConvolve_leftDistrib (frNormalize a) (frNormalize b) (frNormalize c))
  | distribRight a b c =>
      exact frNFEqOfEq _ _
        (frMergeAddPreservesSorted _ _ (frMulConvolveSorted _ _))
        (frMulConvolve_rightDistrib (frNormalize a) (frNormalize b) (frNormalize c))
  | annihilRight a =>
      exact frNFEqOfEq _ _ rfl (frMulConvolveAnnihil (frNormalize a))
  | annihilLeft a =>
      exact frNFEqOfEq _ _ rfl (frMulConvolveNil (frNormalize a))
  | @addCongr lo ln ro rn _ _ ihl ihr =>
      exact frNFEqMergeCongr (frNormalize lo) (frNormalize ln) (frNormalize ro) (frNormalize rn)
        (frNormalizeSorted ln) (frNormalizeSorted ro) ihl ihr
  | @mulCongr lo ln ro rn _ _ ihl ihr =>
      exact frNFEqMulCongr (frNormalize lo) (frNormalize ln) (frNormalize ro) (frNormalize rn) ihl ihr
  | @negCongr ao an _ ih =>
      exact frNFEqNegCongr (frNormalize ao) (frNormalize an) ih
  | refl t => exact frNFEqRefl (frNormalize t) (frNormalizeSorted t)
  | @symm s t _ ih =>
      exact frNFEqSymm (frNormalize s) (frNormalize t)
        (frNormalizeSorted s) (frNormalizeSorted t) ih
  | @trans s t u _ _ ih1 ih2 =>
      exact frNFEqTrans (frNormalize s) (frNormalize t) (frNormalize u)
        (frNormalizeSorted s) (frNormalizeSorted t) (frNormalizeSorted u) ih1 ih2

/-! ## Derived ring-convertibility lemmas (for the rebuild reification) -/

theorem frConvAddZeroLeft (a : FrTree) : RingTreeConv (FrTree.addOp FrTree.zeroOp a) a :=
  (RingTreeConv.addComm FrTree.zeroOp a).trans (RingTreeConv.addZero a)
theorem frConvAddSwap13 (x y z : FrTree) :
    RingTreeConv (FrTree.addOp x (FrTree.addOp y z)) (FrTree.addOp y (FrTree.addOp x z)) :=
  (RingTreeConv.symm (RingTreeConv.addAssoc x y z)).trans
    ((RingTreeConv.addCongr (RingTreeConv.addComm x y) (RingTreeConv.refl z)).trans
      (RingTreeConv.addAssoc y x z))
theorem frConvAddMiddleFour (a b c d : FrTree) :
    RingTreeConv (FrTree.addOp (FrTree.addOp a b) (FrTree.addOp c d))
      (FrTree.addOp (FrTree.addOp a c) (FrTree.addOp b d)) :=
  (RingTreeConv.addAssoc a b (FrTree.addOp c d)).trans
    ((RingTreeConv.addCongr (RingTreeConv.refl a)
        (RingTreeConv.symm (RingTreeConv.addAssoc b c d))).trans
      ((RingTreeConv.addCongr (RingTreeConv.refl a)
          (RingTreeConv.addCongr (RingTreeConv.addComm b c) (RingTreeConv.refl d))).trans
        ((RingTreeConv.addCongr (RingTreeConv.refl a) (RingTreeConv.addAssoc c b d)).trans
          (RingTreeConv.symm (RingTreeConv.addAssoc a c (FrTree.addOp b d))))))
theorem frConvAddNegInverseLeft (a : FrTree) :
    RingTreeConv (FrTree.addOp (FrTree.negOp a) a) FrTree.zeroOp :=
  (RingTreeConv.addComm (FrTree.negOp a) a).trans (RingTreeConv.addNegInverse a)

/-- Uniqueness of additive inverses: if `z + x ≈ 0` and `z + y ≈ 0` then `x ≈ y`. -/
theorem frConvInvUnique (z x y : FrTree)
    (hx : RingTreeConv (FrTree.addOp z x) FrTree.zeroOp)
    (hy : RingTreeConv (FrTree.addOp z y) FrTree.zeroOp) : RingTreeConv x y :=
  (RingTreeConv.symm (RingTreeConv.addZero x)).trans
    ((RingTreeConv.addCongr (RingTreeConv.refl x) (RingTreeConv.symm hy)).trans
      ((RingTreeConv.symm (RingTreeConv.addAssoc x z y)).trans
        ((RingTreeConv.addCongr ((RingTreeConv.addComm x z).trans hx)
            (RingTreeConv.refl y)).trans
          (frConvAddZeroLeft y))))

/-- `neg 0 ≈ 0`. -/
theorem frConvNegZero : RingTreeConv (FrTree.negOp FrTree.zeroOp) FrTree.zeroOp :=
  (RingTreeConv.symm (frConvAddZeroLeft (FrTree.negOp FrTree.zeroOp))).trans
    (RingTreeConv.addNegInverse FrTree.zeroOp)

/-- `neg (neg a) ≈ a`. -/
theorem frConvNegNeg (a : FrTree) : RingTreeConv (FrTree.negOp (FrTree.negOp a)) a :=
  frConvInvUnique (FrTree.negOp a) (FrTree.negOp (FrTree.negOp a)) a
    (RingTreeConv.addNegInverse (FrTree.negOp a)) (frConvAddNegInverseLeft a)

/-- `a * neg b ≈ neg (a * b)` (via left distributivity + right annihilation — NO commutativity). -/
theorem frConvMulNegRight (a b : FrTree) :
    RingTreeConv (FrTree.mulOp a (FrTree.negOp b)) (FrTree.negOp (FrTree.mulOp a b)) :=
  frConvInvUnique (FrTree.mulOp a b) (FrTree.mulOp a (FrTree.negOp b))
    (FrTree.negOp (FrTree.mulOp a b))
    ((RingTreeConv.symm (RingTreeConv.distribLeft a b (FrTree.negOp b))).trans
      ((RingTreeConv.mulCongr (RingTreeConv.refl a) (RingTreeConv.addNegInverse b)).trans
        (RingTreeConv.annihilRight a)))
    (RingTreeConv.addNegInverse (FrTree.mulOp a b))

/-- `neg a * b ≈ neg (a * b)` (via RIGHT distributivity + LEFT annihilation — the commutative rung derived
this from `mulComm`; here it is re-proved without commutativity). -/
theorem frConvMulNegLeft (a b : FrTree) :
    RingTreeConv (FrTree.mulOp (FrTree.negOp a) b) (FrTree.negOp (FrTree.mulOp a b)) :=
  frConvInvUnique (FrTree.mulOp a b) (FrTree.mulOp (FrTree.negOp a) b)
    (FrTree.negOp (FrTree.mulOp a b))
    ((RingTreeConv.symm (RingTreeConv.distribRight a (FrTree.negOp a) b)).trans
      ((RingTreeConv.mulCongr (RingTreeConv.addNegInverse a) (RingTreeConv.refl b)).trans
        (RingTreeConv.annihilLeft b)))
    (RingTreeConv.addNegInverse (FrTree.mulOp a b))

/-- `neg a * neg b ≈ a * b`. -/
theorem frConvMulNegNeg (a b : FrTree) :
    RingTreeConv (FrTree.mulOp (FrTree.negOp a) (FrTree.negOp b)) (FrTree.mulOp a b) :=
  (frConvMulNegLeft a (FrTree.negOp b)).trans
    ((RingTreeConv.negCongr (frConvMulNegRight a b)).trans (frConvNegNeg (FrTree.mulOp a b)))

/-- `neg (a + b) ≈ neg a + neg b`. -/
theorem frConvNegAdd (a b : FrTree) :
    RingTreeConv (FrTree.negOp (FrTree.addOp a b))
      (FrTree.addOp (FrTree.negOp a) (FrTree.negOp b)) :=
  RingTreeConv.symm
    (frConvInvUnique (FrTree.addOp a b) (FrTree.addOp (FrTree.negOp a) (FrTree.negOp b))
      (FrTree.negOp (FrTree.addOp a b))
      ((frConvAddMiddleFour a b (FrTree.negOp a) (FrTree.negOp b)).trans
        ((RingTreeConv.addCongr (RingTreeConv.addNegInverse a)
            (RingTreeConv.addNegInverse b)).trans (RingTreeConv.addZero FrTree.zeroOp)))
      (RingTreeConv.addNegInverse (FrTree.addOp a b)))

/-- Product of two sums expands to four products (right distributivity is a primitive here). -/
theorem frConvMulAddAdd (a b c d : FrTree) :
    RingTreeConv (FrTree.mulOp (FrTree.addOp a b) (FrTree.addOp c d))
      (FrTree.addOp (FrTree.addOp (FrTree.mulOp a c) (FrTree.mulOp a d))
        (FrTree.addOp (FrTree.mulOp b c) (FrTree.mulOp b d))) :=
  (RingTreeConv.distribRight a b (FrTree.addOp c d)).trans
    (RingTreeConv.addCongr (RingTreeConv.distribLeft a c d) (RingTreeConv.distribLeft b c d))

/-! ## Scale trees (coefficient-many copies) -/

/-- `n` copies of a tree added together (`0 ↦ zeroOp`). -/
def frScaleTree (mono : FrTree) : Nat → FrTree
  | 0 => FrTree.zeroOp
  | Nat.succ k => FrTree.addOp mono (frScaleTree mono k)
theorem frScaleTreeCongr {mono1 mono2 : FrTree} (h : RingTreeConv mono1 mono2) (n : Nat) :
    RingTreeConv (frScaleTree mono1 n) (frScaleTree mono2 n) := by
  induction n with
  | zero => exact RingTreeConv.refl FrTree.zeroOp
  | succ k ih => exact RingTreeConv.addCongr h ih
theorem frScaleAdd (mono : FrTree) (a b : Nat) :
    RingTreeConv (frScaleTree mono (a + b))
      (FrTree.addOp (frScaleTree mono a) (frScaleTree mono b)) := by
  induction b with
  | zero => exact (RingTreeConv.addZero (frScaleTree mono a)).symm
  | succ k ih =>
      exact (RingTreeConv.addCongr (RingTreeConv.refl mono) ih).trans
        (frConvAddSwap13 mono (frScaleTree mono a) (frScaleTree mono k))
theorem frScaleTreeMulLeft (p q : FrTree) (c : Nat) :
    RingTreeConv (frScaleTree (FrTree.mulOp p q) c) (FrTree.mulOp (frScaleTree p c) q) := by
  induction c with
  | zero => exact (RingTreeConv.annihilLeft q).symm
  | succ k ih =>
      exact (RingTreeConv.addCongr (RingTreeConv.refl (FrTree.mulOp p q)) ih).trans
        (RingTreeConv.distribRight p (frScaleTree p k) q).symm
theorem frScaleTreeMulRight (p q : FrTree) (d : Nat) :
    RingTreeConv (frScaleTree (FrTree.mulOp p q) d) (FrTree.mulOp p (frScaleTree q d)) := by
  induction d with
  | zero => exact (RingTreeConv.annihilRight p).symm
  | succ k ih =>
      exact (RingTreeConv.addCongr (RingTreeConv.refl (FrTree.mulOp p q)) ih).trans
        (RingTreeConv.distribLeft p q (frScaleTree q k)).symm
theorem frScaleTreeMulCoeff (X : FrTree) (c d : Nat) :
    RingTreeConv (frScaleTree X (c * d)) (frScaleTree (frScaleTree X d) c) := by
  induction c with
  | zero => rw [Nat.zero_mul d]; exact RingTreeConv.refl FrTree.zeroOp
  | succ k ih =>
      rw [Nat.succ_mul k d]
      exact (frScaleAdd X (k * d) d).trans
        ((RingTreeConv.addCongr ih (RingTreeConv.refl (frScaleTree X d))).trans
          (RingTreeConv.addComm (frScaleTree (frScaleTree X d) k) (frScaleTree X d)))
/-- Product of two scaled trees: `(a·X) * (b·Y) ≈ (a*b)·(X*Y)`. -/
theorem frScaleTreeMulBoth (X Y : FrTree) (a b : Nat) :
    RingTreeConv (frScaleTree (FrTree.mulOp X Y) (a * b))
      (FrTree.mulOp (frScaleTree X a) (frScaleTree Y b)) :=
  ((frScaleTreeMulCoeff (FrTree.mulOp X Y) a b).trans
    ((frScaleTreeCongr (frScaleTreeMulRight X Y b) a).trans
      (frScaleTreeMulLeft X (frScaleTree Y b) a)))

/-! ## The word-monomial tree and its multiplicative reification (concatenation, NO commutativity) -/

def frMonoToTree : List Nat → FrTree
  | [] => FrTree.oneOp
  | c :: rest => FrTree.mulOp (FrTree.gen c) (frMonoToTree rest)
/-- Word concatenation reifies to `mulOp` — via `mulAssoc` and the LEFT unit, NO commutativity. -/
theorem frMonoToTreeWordCat : (m n : List Nat) →
    RingTreeConv (frMonoToTree (frWordCat m n))
      (FrTree.mulOp (frMonoToTree m) (frMonoToTree n))
  | [], n => (RingTreeConv.mulOneLeft (frMonoToTree n)).symm
  | a :: as, n => by
      show RingTreeConv (FrTree.mulOp (FrTree.gen a) (frMonoToTree (frWordCat as n)))
        (FrTree.mulOp (FrTree.mulOp (FrTree.gen a) (frMonoToTree as)) (frMonoToTree n))
      exact (RingTreeConv.mulCongr (RingTreeConv.refl (FrTree.gen a))
          (frMonoToTreeWordCat as n)).trans
        (RingTreeConv.symm
          (RingTreeConv.mulAssoc (FrTree.gen a) (frMonoToTree as) (frMonoToTree n)))

/-! ## The term tree (a `(pos, neg)` coefficient applied to a word) and its reification -/

/-- The tree of a single term `(word, (p, n))`: `p` copies of the word tree added, minus `n` copies. -/
def frTermToTree (mono : List Nat) : (Nat × Nat) → FrTree
  | (p, n) => FrTree.addOp (frScaleTree (frMonoToTree mono) p)
                (frScaleTree (FrTree.negOp (frMonoToTree mono)) n)
theorem frTermToTreeEq (mono : List Nat) (p n : Nat) :
    frTermToTree mono (p, n) = FrTree.addOp (frScaleTree (frMonoToTree mono) p)
      (frScaleTree (FrTree.negOp (frMonoToTree mono)) n) := rfl

/-- The term tree distributes over coefficient addition. -/
theorem frTermToTreeAdd (mono : List Nat) (e c : Nat × Nat) :
    RingTreeConv (frTermToTree mono (frCoeffAdd e c))
      (FrTree.addOp (frTermToTree mono e) (frTermToTree mono c)) := by
  obtain ⟨e1, e2⟩ := e; obtain ⟨c1, c2⟩ := c
  exact (RingTreeConv.addCongr (frScaleAdd (frMonoToTree mono) e1 c1)
      (frScaleAdd (FrTree.negOp (frMonoToTree mono)) e2 c2)).trans
    (frConvAddMiddleFour (frScaleTree (frMonoToTree mono) e1) (frScaleTree (frMonoToTree mono) c1)
      (frScaleTree (FrTree.negOp (frMonoToTree mono)) e2)
      (frScaleTree (FrTree.negOp (frMonoToTree mono)) c2))

/-- ★ The term-product reification — the crux of completeness, where word concatenation reifies (no
commutativity) and negation passes through multiplication on both sides. -/
theorem frTermToTreeMul (m : List Nat) (c1 : Nat × Nat) (n' : List Nat) (c2 : Nat × Nat) :
    RingTreeConv (frTermToTree (frWordCat m n') (frCoeffMul c1 c2))
      (FrTree.mulOp (frTermToTree m c1) (frTermToTree n' c2)) := by
  obtain ⟨p1, q1⟩ := c1; obtain ⟨p2, q2⟩ := c2
  have hm1 : RingTreeConv
      (FrTree.mulOp (frScaleTree (frMonoToTree m) p1) (frScaleTree (frMonoToTree n') p2))
      (frScaleTree (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (p1 * p2)) :=
    (frScaleTreeMulBoth (frMonoToTree m) (frMonoToTree n') p1 p2).symm
  have hm2 : RingTreeConv
      (FrTree.mulOp (frScaleTree (frMonoToTree m) p1)
        (frScaleTree (FrTree.negOp (frMonoToTree n')) q2))
      (frScaleTree (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (p1 * q2)) :=
    (frScaleTreeMulBoth (frMonoToTree m) (FrTree.negOp (frMonoToTree n')) p1 q2).symm.trans
      (frScaleTreeCongr (frConvMulNegRight (frMonoToTree m) (frMonoToTree n')) (p1 * q2))
  have hm3 : RingTreeConv
      (FrTree.mulOp (frScaleTree (FrTree.negOp (frMonoToTree m)) q1) (frScaleTree (frMonoToTree n') p2))
      (frScaleTree (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (q1 * p2)) :=
    (frScaleTreeMulBoth (FrTree.negOp (frMonoToTree m)) (frMonoToTree n') q1 p2).symm.trans
      (frScaleTreeCongr (frConvMulNegLeft (frMonoToTree m) (frMonoToTree n')) (q1 * p2))
  have hm4 : RingTreeConv
      (FrTree.mulOp (frScaleTree (FrTree.negOp (frMonoToTree m)) q1)
        (frScaleTree (FrTree.negOp (frMonoToTree n')) q2))
      (frScaleTree (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (q1 * q2)) :=
    (frScaleTreeMulBoth (FrTree.negOp (frMonoToTree m)) (FrTree.negOp (frMonoToTree n')) q1 q2).symm.trans
      (frScaleTreeCongr (frConvMulNegNeg (frMonoToTree m) (frMonoToTree n')) (q1 * q2))
  have hRHStoC : RingTreeConv
      (FrTree.mulOp (frTermToTree m (p1, q1)) (frTermToTree n' (p2, q2)))
      (FrTree.addOp
        (FrTree.addOp (frScaleTree (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (p1 * p2))
          (frScaleTree (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (p1 * q2)))
        (FrTree.addOp (frScaleTree (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (q1 * p2))
          (frScaleTree (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (q1 * q2)))) :=
    (frConvMulAddAdd (frScaleTree (frMonoToTree m) p1) (frScaleTree (FrTree.negOp (frMonoToTree m)) q1)
        (frScaleTree (frMonoToTree n') p2) (frScaleTree (FrTree.negOp (frMonoToTree n')) q2)).trans
      (RingTreeConv.addCongr (RingTreeConv.addCongr hm1 hm2) (RingTreeConv.addCongr hm3 hm4))
  have hLHStoC : RingTreeConv
      (frTermToTree (frWordCat m n') (p1 * p2 + q1 * q2, p1 * q2 + q1 * p2))
      (FrTree.addOp
        (FrTree.addOp (frScaleTree (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (p1 * p2))
          (frScaleTree (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (p1 * q2)))
        (FrTree.addOp (frScaleTree (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (q1 * p2))
          (frScaleTree (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (q1 * q2)))) :=
    (RingTreeConv.addCongr
        (frScaleTreeCongr (frMonoToTreeWordCat m n') (p1 * p2 + q1 * q2))
        (frScaleTreeCongr (RingTreeConv.negCongr (frMonoToTreeWordCat m n')) (p1 * q2 + q1 * p2))).trans
      ((RingTreeConv.addCongr
          (frScaleAdd (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (p1 * p2) (q1 * q2))
          (frScaleAdd (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (p1 * q2) (q1 * p2))).trans
        ((frConvAddMiddleFour
            (frScaleTree (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (p1 * p2))
            (frScaleTree (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (q1 * q2))
            (frScaleTree (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (p1 * q2))
            (frScaleTree (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (q1 * p2))).trans
          (RingTreeConv.addCongr (RingTreeConv.refl _)
            (RingTreeConv.addComm
              (frScaleTree (FrTree.mulOp (frMonoToTree m) (frMonoToTree n')) (q1 * q2))
              (frScaleTree (FrTree.negOp (FrTree.mulOp (frMonoToTree m) (frMonoToTree n'))) (q1 * p2))))))
  exact hLHStoC.trans hRHStoC.symm

/-! ## The normal-form rebuild `frCombOfNF` and its convertibility algebra -/

/-- Rebuild a canonical tree from a normal form. -/
def frCombOfNF : FrNF → FrTree
  | [] => FrTree.zeroOp
  | (m, c) :: rest => FrTree.addOp (frTermToTree m c) (frCombOfNF rest)
theorem frCombOfNFCons (m : List Nat) (c : Nat × Nat) (rest : FrNF) :
    frCombOfNF ((m, c) :: rest) = FrTree.addOp (frTermToTree m c) (frCombOfNF rest) := rfl

theorem frCombInsertTerm (m : List Nat) (c : Nat × Nat) (A : FrNF) :
    RingTreeConv (frCombOfNF (frInsertTerm (m, c) A))
      (FrTree.addOp (frTermToTree m c) (frCombOfNF A)) := by
  induction A with
  | nil => exact RingTreeConv.refl _
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [frInsertTermEqE m c p e rest hmp, frCombOfNFCons p (frCoeffAdd e c) rest,
              frCombOfNFCons p e rest, hmeqp]
          exact (RingTreeConv.addCongr (frTermToTreeAdd p e c)
              (RingTreeConv.refl (frCombOfNF rest))).trans
            ((RingTreeConv.addAssoc (frTermToTree p e) (frTermToTree p c) (frCombOfNF rest)).trans
              (frConvAddSwap13 (frTermToTree p e) (frTermToTree p c) (frCombOfNF rest)))
      | lt =>
          rw [frInsertTermLtE m c p e rest hmp, frCombOfNFCons m c ((p, e) :: rest)]
          exact RingTreeConv.refl _
      | gt =>
          rw [frInsertTermGtE m c p e rest hmp, frCombOfNFCons p e (frInsertTerm (m, c) rest),
              frCombOfNFCons p e rest]
          exact (RingTreeConv.addCongr (RingTreeConv.refl (frTermToTree p e)) ih).trans
            (frConvAddSwap13 (frTermToTree p e) (frTermToTree m c) (frCombOfNF rest))

theorem frCombMergeAdd (A B : FrNF) :
    RingTreeConv (frCombOfNF (frMergeAdd A B))
      (FrTree.addOp (frCombOfNF A) (frCombOfNF B)) := by
  induction A with
  | nil => exact (frConvAddZeroLeft (frCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show RingTreeConv (frCombOfNF (frInsertTerm (m, c) (frMergeAdd A' B)))
        (FrTree.addOp (FrTree.addOp (frTermToTree m c) (frCombOfNF A')) (frCombOfNF B))
      exact ((frCombInsertTerm m c (frMergeAdd A' B)).trans
          (RingTreeConv.addCongr (RingTreeConv.refl (frTermToTree m c)) ih)).trans
        (RingTreeConv.symm
          (RingTreeConv.addAssoc (frTermToTree m c) (frCombOfNF A') (frCombOfNF B)))

theorem frCombTermMul (m : List Nat) (c : Nat × Nat) (B : FrNF) :
    RingTreeConv (frCombOfNF (frTermMul m c B))
      (FrTree.mulOp (frTermToTree m c) (frCombOfNF B)) := by
  induction B with
  | nil => exact (RingTreeConv.annihilRight (frTermToTree m c)).symm
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show RingTreeConv (frCombOfNF (frInsertTerm (frWordCat m n, frCoeffMul c d) (frTermMul m c B')))
        (FrTree.mulOp (frTermToTree m c) (FrTree.addOp (frTermToTree n d) (frCombOfNF B')))
      exact ((frCombInsertTerm (frWordCat m n) (frCoeffMul c d) (frTermMul m c B')).trans
          (RingTreeConv.addCongr (frTermToTreeMul m c n d) ih)).trans
        (RingTreeConv.symm
          (RingTreeConv.distribLeft (frTermToTree m c) (frTermToTree n d) (frCombOfNF B')))

theorem frCombMulConvolve (A B : FrNF) :
    RingTreeConv (frCombOfNF (frMulConvolve A B))
      (FrTree.mulOp (frCombOfNF A) (frCombOfNF B)) := by
  induction A with
  | nil => exact (RingTreeConv.annihilLeft (frCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show RingTreeConv (frCombOfNF (frMergeAdd (frTermMul m c B) (frMulConvolve A' B)))
        (FrTree.mulOp (FrTree.addOp (frTermToTree m c) (frCombOfNF A')) (frCombOfNF B))
      exact ((frCombMergeAdd (frTermMul m c B) (frMulConvolve A' B)).trans
          (RingTreeConv.addCongr (frCombTermMul m c B) ih)).trans
        (RingTreeConv.symm (RingTreeConv.distribRight (frTermToTree m c) (frCombOfNF A') (frCombOfNF B)))

/-! ## Negation through the rebuild -/

/-- Negation passes through a scale tree: `neg (k·X) ≈ k·(neg X)`. -/
theorem frScaleTreeNeg (X : FrTree) (k : Nat) :
    RingTreeConv (FrTree.negOp (frScaleTree X k)) (frScaleTree (FrTree.negOp X) k) := by
  induction k with
  | zero => exact frConvNegZero
  | succ j ih =>
      exact (frConvNegAdd X (frScaleTree X j)).trans
        (RingTreeConv.addCongr (RingTreeConv.refl (FrTree.negOp X)) ih)

/-- Negating a term tree negates its coefficient: `termToTree m (neg c) ≈ neg (termToTree m c)`. -/
theorem frTermToTreeNeg (m : List Nat) (c : Nat × Nat) :
    RingTreeConv (frTermToTree m (frCoeffNeg c)) (FrTree.negOp (frTermToTree m c)) := by
  obtain ⟨p, n⟩ := c
  have hswap : RingTreeConv (frTermToTree m (n, p))
      (FrTree.addOp (frScaleTree (FrTree.negOp (frMonoToTree m)) p) (frScaleTree (frMonoToTree m) n)) :=
    RingTreeConv.addComm (frScaleTree (frMonoToTree m) n)
      (frScaleTree (FrTree.negOp (frMonoToTree m)) p)
  have hback : RingTreeConv (FrTree.negOp (frTermToTree m (p, n)))
      (FrTree.addOp (frScaleTree (FrTree.negOp (frMonoToTree m)) p) (frScaleTree (frMonoToTree m) n)) :=
    (frConvNegAdd (frScaleTree (frMonoToTree m) p)
        (frScaleTree (FrTree.negOp (frMonoToTree m)) n)).trans
      (RingTreeConv.addCongr (frScaleTreeNeg (frMonoToTree m) p)
        ((frScaleTreeNeg (FrTree.negOp (frMonoToTree m)) n).trans
          (frScaleTreeCongr (frConvNegNeg (frMonoToTree m)) n)))
  exact hswap.trans hback.symm

theorem frCombNegate (A : FrNF) :
    RingTreeConv (frCombOfNF (frNegate A)) (FrTree.negOp (frCombOfNF A)) := by
  induction A with
  | nil => exact frConvNegZero.symm
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show RingTreeConv (FrTree.addOp (frTermToTree m (frCoeffNeg c)) (frCombOfNF (frNegate rest)))
        (FrTree.negOp (FrTree.addOp (frTermToTree m c) (frCombOfNF rest)))
      exact (RingTreeConv.addCongr (frTermToTreeNeg m c) ih).trans
        (frConvNegAdd (frTermToTree m c) (frCombOfNF rest)).symm

/-! ## The all-zero rebuild is convertible to `0` -/

/-- `k·X + k·(neg X) ≈ 0`. -/
theorem frScaleTreeNegCancel (X : FrTree) (k : Nat) :
    RingTreeConv (FrTree.addOp (frScaleTree X k) (frScaleTree (FrTree.negOp X) k)) FrTree.zeroOp := by
  induction k with
  | zero => exact RingTreeConv.addZero FrTree.zeroOp
  | succ j ih =>
      exact (frConvAddMiddleFour X (frScaleTree X j) (FrTree.negOp X) (frScaleTree (FrTree.negOp X) j)).trans
        ((RingTreeConv.addCongr (RingTreeConv.addNegInverse X) ih).trans
          (RingTreeConv.addZero FrTree.zeroOp))

/-- A zero-valued term tree is convertible to `0`. -/
theorem frTermToTreeZero (m : List Nat) (c : Nat × Nat) (hc : frCoeffIsZero c = true) :
    RingTreeConv (frTermToTree m c) FrTree.zeroOp := by
  obtain ⟨p, n⟩ := c
  have hpn : p = n := csrNatEqOfBeq p n hc
  rw [frTermToTreeEq m p n, hpn]
  exact frScaleTreeNegCancel (frMonoToTree m) n

/-- An all-zero rebuild reduces to `0`. -/
theorem frCombAllZero (A : FrNF) (hA : frNFAllZero A = true) :
    RingTreeConv (frCombOfNF A) FrTree.zeroOp := by
  induction A with
  | nil => exact RingTreeConv.refl FrTree.zeroOp
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      have hc : frCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hrest : frNFAllZero rest = true := csrAndTrueRight _ _ hA
      show RingTreeConv (FrTree.addOp (frTermToTree m c) (frCombOfNF rest)) FrTree.zeroOp
      exact (RingTreeConv.addCongr (frTermToTreeZero m c hc) (ih hrest)).trans
        (RingTreeConv.addZero FrTree.zeroOp)

/-! ## Reification: every tree is convertible to the rebuild of its own normal form -/

/-- `monoToTree m ≈ termToTree m (1,0)`. -/
theorem frMonoToTreeTermOne (m : List Nat) :
    RingTreeConv (frMonoToTree m) (frTermToTree m (1, 0)) :=
  (RingTreeConv.addZero (frMonoToTree m)).symm.trans
    (RingTreeConv.addZero (FrTree.addOp (frMonoToTree m) FrTree.zeroOp)).symm

/-- ★ Every tree is convertible to the rebuild of its own normal form. -/
theorem frTreeReifies (t : FrTree) : RingTreeConv t (frCombOfNF (frNormalize t)) := by
  induction t with
  | gen c =>
      show RingTreeConv (FrTree.gen c)
        (FrTree.addOp (frTermToTree [c] (1, 0)) FrTree.zeroOp)
      have hgen : RingTreeConv (FrTree.gen c) (frMonoToTree [c]) :=
        (RingTreeConv.mulOne (FrTree.gen c)).symm
      exact (hgen.trans (frMonoToTreeTermOne [c])).trans
        (RingTreeConv.addZero (frTermToTree [c] (1, 0))).symm
  | zeroOp => exact RingTreeConv.refl FrTree.zeroOp
  | oneOp =>
      show RingTreeConv FrTree.oneOp (FrTree.addOp (frTermToTree [] (1, 0)) FrTree.zeroOp)
      exact (frMonoToTreeTermOne []).trans (RingTreeConv.addZero (frTermToTree [] (1, 0))).symm
  | addOp l r ihl ihr =>
      show RingTreeConv (FrTree.addOp l r)
        (frCombOfNF (frMergeAdd (frNormalize l) (frNormalize r)))
      exact (RingTreeConv.addCongr ihl ihr).trans
        (RingTreeConv.symm (frCombMergeAdd (frNormalize l) (frNormalize r)))
  | mulOp l r ihl ihr =>
      show RingTreeConv (FrTree.mulOp l r)
        (frCombOfNF (frMulConvolve (frNormalize l) (frNormalize r)))
      exact (RingTreeConv.mulCongr ihl ihr).trans
        (RingTreeConv.symm (frCombMulConvolve (frNormalize l) (frNormalize r)))
  | negOp a ih =>
      show RingTreeConv (FrTree.negOp a) (frCombOfNF (frNegate (frNormalize a)))
      exact (RingTreeConv.negCongr ih).trans
        (RingTreeConv.symm (frCombNegate (frNormalize a)))

/-! ## Completeness: `frNFEq` normal forms give convertible trees -/

/-- If `x + neg y ≈ 0` then `x ≈ y`. -/
theorem frConvOfSubZero (x y : FrTree)
    (h : RingTreeConv (FrTree.addOp x (FrTree.negOp y)) FrTree.zeroOp) : RingTreeConv x y :=
  (RingTreeConv.addZero x).symm.trans
    ((RingTreeConv.addCongr (RingTreeConv.refl x) (frConvAddNegInverseLeft y).symm).trans
      ((RingTreeConv.addAssoc x (FrTree.negOp y) y).symm.trans
        ((RingTreeConv.addCongr h (RingTreeConv.refl y)).trans (frConvAddZeroLeft y))))

/-- The rebuilds of `frNFEq` normal forms are convertible. -/
theorem frCombOfNFEqConv (A B : FrNF) (h : frNFEq A B = true) :
    RingTreeConv (frCombOfNF A) (frCombOfNF B) := by
  apply frConvOfSubZero (frCombOfNF A) (frCombOfNF B)
  have hall : RingTreeConv (frCombOfNF (frMergeAdd A (frNegate B))) FrTree.zeroOp :=
    frCombAllZero (frMergeAdd A (frNegate B)) h
  exact (RingTreeConv.symm ((frCombMergeAdd A (frNegate B)).trans
      (RingTreeConv.addCongr (RingTreeConv.refl (frCombOfNF A)) (frCombNegate B)))).trans hall

/-- ★ Completeness — `frNFEq` normal forms give convertible trees. -/
theorem frConv_of_normalizeEq {s t : FrTree} (h : frNFEq (frNormalize s) (frNormalize t) = true) :
    RingTreeConv s t :=
  (frTreeReifies s).trans
    ((frCombOfNFEqConv (frNormalize s) (frNormalize t) h).trans (RingTreeConv.symm (frTreeReifies t)))

/-! ## The decision -/

/-- ★★ the decision procedure: convertible iff the polynomial difference has every coefficient zero-valued. -/
def frDecideConv (s t : FrTree) : Bool := frNFEq (frNormalize s) (frNormalize t)

/-- ★★ THE DECISION: convertibility ⟺ equal non-commutative polynomial (ℤ⟨X⟩) normal form. -/
theorem ringTreeConv_iff_normalForm (s t : FrTree) :
    RingTreeConv s t ↔ frDecideConv s t = true := by
  constructor
  · intro conv
    exact frNormalize_respects conv
  · intro hdec
    exact frConv_of_normalizeEq hdec

/-- ★ decidability, via the biconditional (no `propext`). -/
instance frDecidableConv (s t : FrTree) : Decidable (RingTreeConv s t) :=
  if h : frDecideConv s t = true then
    isTrue ((ringTreeConv_iff_normalForm s t).mpr h)
  else
    isFalse (fun conv => h ((ringTreeConv_iff_normalForm s t).mp conv))

/-- ★★ the walking free non-commutative ring on ℕ (the polynomial ring `ℤ⟨X⟩`) is DECIDED. -/
def fxWalkingRing_hasNormalFormDecision : Bool := true

-- genuineness smokes
-- THE HEADLINE — the additive inverse: x + neg x is 0 (true)
#eval frDecideConv (FrTree.addOp (FrTree.gen 0) (FrTree.negOp (FrTree.gen 0))) FrTree.zeroOp
-- associativity (x*y)*z is x*(y*z) (true)
#eval frDecideConv
  (FrTree.mulOp (FrTree.mulOp (FrTree.gen 0) (FrTree.gen 1)) (FrTree.gen 2))
  (FrTree.mulOp (FrTree.gen 0) (FrTree.mulOp (FrTree.gen 1) (FrTree.gen 2)))
-- left distributivity x*(y+z) is x*y + x*z (true)
#eval frDecideConv (FrTree.mulOp (FrTree.gen 0) (FrTree.addOp (FrTree.gen 1) (FrTree.gen 2)))
  (FrTree.addOp (FrTree.mulOp (FrTree.gen 0) (FrTree.gen 1))
    (FrTree.mulOp (FrTree.gen 0) (FrTree.gen 2)))
-- THE HEADLINE — non-commutativity: x*y is NOT y*x (false)
#eval frDecideConv (FrTree.mulOp (FrTree.gen 0) (FrTree.gen 1))
  (FrTree.mulOp (FrTree.gen 1) (FrTree.gen 0))
-- inverse + reorder: x + neg y + y is x (true)
#eval frDecideConv
  (FrTree.addOp (FrTree.addOp (FrTree.gen 0) (FrTree.negOp (FrTree.gen 1))) (FrTree.gen 1))
  (FrTree.gen 0)
-- double negation neg(neg x) is x (true)
#eval frDecideConv (FrTree.negOp (FrTree.negOp (FrTree.gen 0))) (FrTree.gen 0)
-- separation x is NOT neg x (false)
#eval frDecideConv (FrTree.gen 0) (FrTree.negOp (FrTree.gen 0))

end FX1Poly.Polygraph
