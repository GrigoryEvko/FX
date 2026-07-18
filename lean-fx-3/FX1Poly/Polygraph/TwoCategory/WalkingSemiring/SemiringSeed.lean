import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeMonoid.MultisetCommutativeMonoidSeed
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # WalkingSemiring/SemiringSeed — the walking free NON-COMMUTATIVE SEMIRING on ℕ: the polynomial ℕ⟨X⟩ decision

The direct non-commutative sibling of the free commutative semiring rung
(`WalkingCommutativeSemiring/CommutativeSemiringSeed`).  The commutative walker's free algebra was `ℕ[X]`,
polynomials in COMMUTING variables — a monomial there is a finite MULTISET of colours, so monomial product is
multiset union.  Dropping the multiplicative commutativity law turns that walker into the free
**non-commutative semiring** on the colour set `ℕ`, which is exactly the semiring of polynomials `ℕ⟨X_c⟩` in
NON-commuting variables: a monomial becomes an ORDER-SIGNIFICANT WORD (a plain `List Nat`), and monomial
product becomes WORD CONCATENATION (not multiset union).  A tree's class is determined by its non-commutative
polynomial — the finite formal `ℕ`-linear combination of words.  Because that polynomial is a COMPLETE
invariant with a canonical sorted representative, the word problem is DECIDED by plain structural equality of
normal forms; there is no crux (word concatenation is trivially associative, and there is no multiplicative
commutativity to establish).

## ★ Why this walker is FULLY DECIDED — non-commutative polynomials as the complete invariant

The normal form `NcsrNF := List (List Nat × Nat)` is a list of `(word, coefficient)` pairs, sorted strictly by
a total word order `ncsrWordBle` (length-first, then lexicographic via the imported structural `natBle`), every
coefficient `> 0`, no duplicate words.  A word is a plain `List Nat` of variable-occurrences carrying its own
order — no sortedness invariant, unlike the commutative sibling's monomials.  The two operations are
`ncsrMergeAdd` (sorted merge, coefficients added on equal words) and `ncsrMulConvolve` (the Cauchy convolution:
word product = concatenation via the cons-only `ncsrWordCat`, coefficient product = `Nat.mul`).  `ncsrNormalize`
sends `gen c ↦ [([c],1)]`, `zeroOp ↦ []`, `oneOp ↦ [([],1)]` (the empty word is the multiplicative unit),
`addOp ↦ ncsrMergeAdd`, `mulOp ↦ ncsrMulConvolve`.

This file ships, all zero-axiom:

* **the term-insertion commutation** `ncsrInsertTermComm` — two term-insertions commute (permutation-invariance
  of the additive merge; the coefficient-aware analogue of the multiset seed's `insertSortedComm`);
* **the additive commutative monoid** — `ncsrMergeAdd` associative / commutative with `[]` a unit
  (`ncsrMergeAddAssoc` / `ncsrMergeAddComm` / `ncsrMergeAddNilRight`), on the strict-sortedness invariant
  `ncsrNFSorted` (addition stays commutative — this is a semiring);
* **the multiplicative MONOID (no commutativity)** — `ncsrMulConvolve` BOTH ANNIHILATIONS (`ncsrMulConvolveNil`
  the left `0·a`, rfl; `ncsrMulConvolveAnnihil` the right `a·0`), LEFT and RIGHT DISTRIBUTIVITY
  (`ncsrMulConvolve_leftDistrib` / `ncsrMulConvolve_rightDistrib` — neither derivable from the other absent
  commutativity), ASSOCIATIVITY (`ncsrMulConvolveAssoc`, via the `ncsrTermMul_compose`/`ncsrTermMul_convolve`
  chain — reducing to the free word-monoid associativity `ncsrWordCatAssoc` and a hand-proved clean
  `ncsrNatMulAssoc`), and BOTH UNITS (`ncsrMulConvolveUnitLeft` `1·a` and `ncsrMulConvolveUnitRight` `a·1`).
  There is deliberately NO convolution-commutativity lemma — that is the whole point of this walker;
* **soundness** — convertible trees have equal normal form (`ncsrNormalize_respects`): every non-commutative
  semiring law is an equation between normal forms discharged by the algebra above;
* **completeness** — equal normal forms give convertible trees (`ncsrConv_of_normalizeEq`), via the rebuild
  `ncsrCombOfNF` and the reification `ncsrTreeReifies` (every tree is convertible to the rebuild of its own
  normal form), whose engine is the tree-level `ncsrCombInsertTerm` / `ncsrCombMergeAdd` / `ncsrCombTermMul` /
  `ncsrCombMulConvolve` plus the scale-tree algebra (`ncsrScaleTree`, coefficient-many copies) and the word
  reification (`ncsrMonoToTreeWordCat`, the structural counterpart of the sibling's multiset `insertMany`
  reification — concatenation reifies by `mulAssoc` and the left-unit law, no commutativity);
* **THE DECISION** — the biconditional `noncommSemiringTreeConv_iff_normalForm`
  (`s ≈ t ↔ ncsrDecideConv s t = true`, where `ncsrDecideConv s t := ncsrNFEq (ncsrNormalize s)
  (ncsrNormalize t)`), plus a genuine `Decidable` instance (`ncsrDecidableConv`, via `Iff.mp`/`Iff.mpr`, no
  `propext`), and `#eval` groundings pinning the right bools — including the non-commutativity HEADLINE
  `x·y` vs `y·x` → FALSE (words `[0,1]` ≠ `[1,0]`).

Note on the coefficient arithmetic: the standard-library `Nat.mul_assoc` and `Nat.add_mul` LEAK `propext`, so
this file uses the hand-proved clean structural replacements `ncsrNatMulAssoc` / `ncsrNatAddMul`, built from the
clean primitives `Nat.mul_comm` / `Nat.mul_add` / `Nat.mul_succ` / `Nat.mul_one`, plus the clean
`ncsrNatOneMul` (`1·d = d`) for the multiplicative left unit.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`
— the ordering is the imported structural `natBle`, no `Nat.le`/`Nat.ble` lemma appears, WORD CONCATENATION is
the cons-only `ncsrWordCat` (never `List.append`/`++`), and coefficient arithmetic uses only
`Nat.add_comm`/`Nat.add_assoc`/`Nat.add_zero` and the clean multiplication kit. -/

namespace FX1Poly.Polygraph

def ncsrLen : List Nat → Nat
  | [] => 0
  | _ :: tail => Nat.succ (ncsrLen tail)
def ncsrLexBle : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      match natBle a b with
      | false => false
      | true => match natBle b a with
                | false => true
                | true => ncsrLexBle as bs
def ncsrWordBle (m n : List Nat) : Bool :=
  match natBle (ncsrLen m) (ncsrLen n) with
  | false => false
  | true => match natBle (ncsrLen n) (ncsrLen m) with
            | false => true
            | true => ncsrLexBle m n
def ncsrWordEq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => Nat.beq a b && ncsrWordEq as bs
theorem ncsrWordBleFF (m n : List Nat) (h : natBle (ncsrLen m) (ncsrLen n) = false) :
    ncsrWordBle m n = false := by
  show (match natBle (ncsrLen m) (ncsrLen n) with
        | false => false
        | true => match natBle (ncsrLen n) (ncsrLen m) with
                  | false => true
                  | true => ncsrLexBle m n) = false
  rw [h]
theorem ncsrWordBleTF (m n : List Nat) (h1 : natBle (ncsrLen m) (ncsrLen n) = true)
    (h2 : natBle (ncsrLen n) (ncsrLen m) = false) : ncsrWordBle m n = true := by
  show (match natBle (ncsrLen m) (ncsrLen n) with
        | false => false
        | true => match natBle (ncsrLen n) (ncsrLen m) with
                  | false => true
                  | true => ncsrLexBle m n) = true
  rw [h1, h2]
theorem ncsrWordBleTT (m n : List Nat) (h1 : natBle (ncsrLen m) (ncsrLen n) = true)
    (h2 : natBle (ncsrLen n) (ncsrLen m) = true) : ncsrWordBle m n = ncsrLexBle m n := by
  show (match natBle (ncsrLen m) (ncsrLen n) with
        | false => false
        | true => match natBle (ncsrLen n) (ncsrLen m) with
                  | false => true
                  | true => ncsrLexBle m n) = ncsrLexBle m n
  rw [h1, h2]
theorem ncsrLexConsTF (a b : Nat) (as bs : List Nat) (h1 : natBle a b = true) (h2 : natBle b a = false) :
    ncsrLexBle (a :: as) (b :: bs) = true := by
  show (match natBle a b with
        | false => false
        | true => match natBle b a with
                  | false => true
                  | true => ncsrLexBle as bs) = true
  rw [h1, h2]
theorem ncsrLexConsTT (a b : Nat) (as bs : List Nat) (h1 : natBle a b = true) (h2 : natBle b a = true) :
    ncsrLexBle (a :: as) (b :: bs) = ncsrLexBle as bs := by
  show (match natBle a b with
        | false => false
        | true => match natBle b a with
                  | false => true
                  | true => ncsrLexBle as bs) = ncsrLexBle as bs
  rw [h1, h2]
theorem ncsrLexConsFF (a b : Nat) (as bs : List Nat) (h : natBle a b = false) :
    ncsrLexBle (a :: as) (b :: bs) = false := by
  show (match natBle a b with
        | false => false
        | true => match natBle b a with
                  | false => true
                  | true => ncsrLexBle as bs) = false
  rw [h]
theorem ncsrLexBleTotalEqLen : (m n : List Nat) → ncsrLen m = ncsrLen n →
    ncsrLexBle m n = false → ncsrLexBle n m = true
  | [], [], _, hfalse => Bool.noConfusion hfalse
  | [], _ :: _, hlen, _ => Nat.noConfusion hlen
  | _ :: _, [], hlen, _ => Nat.noConfusion hlen
  | a :: as, b :: bs, hlen, hfalse => by
      have hlen' : ncsrLen as = ncsrLen bs := Nat.succ.inj hlen
      cases hab : natBle a b with
      | false => exact ncsrLexConsTF b a bs as (natBleTotal a b hab) hab
      | true =>
          cases hba : natBle b a with
          | false => exact Bool.noConfusion ((ncsrLexConsTF a b as bs hab hba).symm.trans hfalse)
          | true =>
              have hastail : ncsrLexBle as bs = false := by
                rw [ncsrLexConsTT a b as bs hab hba] at hfalse; exact hfalse
              rw [ncsrLexConsTT b a bs as hba hab]
              exact ncsrLexBleTotalEqLen as bs hlen' hastail
theorem ncsrLexBleAntisymmEqLen : (m n : List Nat) → ncsrLen m = ncsrLen n →
    ncsrLexBle m n = true → ncsrLexBle n m = true → m = n
  | [], [], _, _, _ => rfl
  | [], _ :: _, hlen, _, _ => Nat.noConfusion hlen
  | _ :: _, [], hlen, _, _ => Nat.noConfusion hlen
  | a :: as, b :: bs, hlen, hmn, hnm => by
      have hlen' : ncsrLen as = ncsrLen bs := Nat.succ.inj hlen
      cases hab : natBle a b with
      | false => exact Bool.noConfusion ((ncsrLexConsFF a b as bs hab).symm.trans hmn)
      | true =>
          cases hba : natBle b a with
          | false => exact Bool.noConfusion ((ncsrLexConsFF b a bs as hba).symm.trans hnm)
          | true =>
              have haeqb : a = b := natBleAntisymm a b hab hba
              have hmn' : ncsrLexBle as bs = true := by
                rw [ncsrLexConsTT a b as bs hab hba] at hmn; exact hmn
              have hnm' : ncsrLexBle bs as = true := by
                rw [ncsrLexConsTT b a bs as hba hab] at hnm; exact hnm
              rw [haeqb, ncsrLexBleAntisymmEqLen as bs hlen' hmn' hnm']
theorem ncsrLexBleTransEqLen : (m n p : List Nat) → ncsrLen m = ncsrLen n → ncsrLen n = ncsrLen p →
    ncsrLexBle m n = true → ncsrLexBle n p = true → ncsrLexBle m p = true
  | [], [], [], _, _, _, _ => rfl
  | [], [], _ :: _, _, hlen2, _, _ => Nat.noConfusion hlen2
  | [], _ :: _, _, hlen1, _, _, _ => Nat.noConfusion hlen1
  | _ :: _, [], _, hlen1, _, _, _ => Nat.noConfusion hlen1
  | _ :: _, _ :: _, [], _, hlen2, _, _ => Nat.noConfusion hlen2
  | a :: as, b :: bs, c :: cs, hlen1, hlen2, hmn, hnp => by
      have hlen1' : ncsrLen as = ncsrLen bs := Nat.succ.inj hlen1
      have hlen2' : ncsrLen bs = ncsrLen cs := Nat.succ.inj hlen2
      cases hab : natBle a b with
      | false => exact Bool.noConfusion ((ncsrLexConsFF a b as bs hab).symm.trans hmn)
      | true =>
        cases hbc : natBle b c with
        | false => exact Bool.noConfusion ((ncsrLexConsFF b c bs cs hbc).symm.trans hnp)
        | true =>
          have hac : natBle a c = true := natBleTrans a b c hab hbc
          cases hca : natBle c a with
          | false => exact ncsrLexConsTF a c as cs hac hca
          | true =>
            have hba : natBle b a = true := natBleTrans b c a hbc hca
            have hcb : natBle c b = true := natBleTrans c a b hca hab
            have hmn' : ncsrLexBle as bs = true := by
              rw [ncsrLexConsTT a b as bs hab hba] at hmn; exact hmn
            have hnp' : ncsrLexBle bs cs = true := by
              rw [ncsrLexConsTT b c bs cs hbc hcb] at hnp; exact hnp
            rw [ncsrLexConsTT a c as cs hac hca]
            exact ncsrLexBleTransEqLen as bs cs hlen1' hlen2' hmn' hnp'
theorem ncsrWordBleTotal (m n : List Nat) : ncsrWordBle m n = false → ncsrWordBle n m = true := by
  intro hfalse
  cases hmn : natBle (ncsrLen m) (ncsrLen n) with
  | false => exact ncsrWordBleTF n m (natBleTotal (ncsrLen m) (ncsrLen n) hmn) hmn
  | true =>
      cases hnm : natBle (ncsrLen n) (ncsrLen m) with
      | false => exact Bool.noConfusion ((ncsrWordBleTF m n hmn hnm).symm.trans hfalse)
      | true =>
          have hlex : ncsrLexBle m n = false := by
            rw [ncsrWordBleTT m n hmn hnm] at hfalse; exact hfalse
          have hlen : ncsrLen m = ncsrLen n := natBleAntisymm _ _ hmn hnm
          rw [ncsrWordBleTT n m hnm hmn]
          exact ncsrLexBleTotalEqLen m n hlen hlex
theorem ncsrWordBleAntisymm (m n : List Nat) :
    ncsrWordBle m n = true → ncsrWordBle n m = true → m = n := by
  intro hmn hnm
  cases hlmn : natBle (ncsrLen m) (ncsrLen n) with
  | false => exact absurd hmn (by rw [ncsrWordBleFF m n hlmn]; exact Bool.noConfusion)
  | true =>
      cases hlnm : natBle (ncsrLen n) (ncsrLen m) with
      | false => exact absurd hnm (by rw [ncsrWordBleFF n m hlnm]; exact Bool.noConfusion)
      | true =>
          have hlen : ncsrLen m = ncsrLen n := natBleAntisymm _ _ hlmn hlnm
          have h1 : ncsrLexBle m n = true := by rw [ncsrWordBleTT m n hlmn hlnm] at hmn; exact hmn
          have h2 : ncsrLexBle n m = true := by rw [ncsrWordBleTT n m hlnm hlmn] at hnm; exact hnm
          exact ncsrLexBleAntisymmEqLen m n hlen h1 h2
theorem ncsrWordBleTrans (m n p : List Nat) :
    ncsrWordBle m n = true → ncsrWordBle n p = true → ncsrWordBle m p = true := by
  intro hmn hnp
  cases hlmn : natBle (ncsrLen m) (ncsrLen n) with
  | false => exact absurd hmn (by rw [ncsrWordBleFF m n hlmn]; exact Bool.noConfusion)
  | true =>
      cases hlnp : natBle (ncsrLen n) (ncsrLen p) with
      | false => exact absurd hnp (by rw [ncsrWordBleFF n p hlnp]; exact Bool.noConfusion)
      | true =>
          have hlmp : natBle (ncsrLen m) (ncsrLen p) = true := natBleTrans _ _ _ hlmn hlnp
          cases hlpm : natBle (ncsrLen p) (ncsrLen m) with
          | false => exact ncsrWordBleTF m p hlmp hlpm
          | true =>
              have hlpn : natBle (ncsrLen p) (ncsrLen n) = true := natBleTrans _ _ _ hlpm hlmn
              have hlnm : natBle (ncsrLen n) (ncsrLen m) = true := natBleTrans _ _ _ hlnp hlpm
              have hlen1 : ncsrLen m = ncsrLen n := natBleAntisymm _ _ hlmn hlnm
              have hlen2 : ncsrLen n = ncsrLen p := natBleAntisymm _ _ hlnp hlpn
              have h1 : ncsrLexBle m n = true := by rw [ncsrWordBleTT m n hlmn hlnm] at hmn; exact hmn
              have h2 : ncsrLexBle n p = true := by rw [ncsrWordBleTT n p hlnp hlpn] at hnp; exact hnp
              rw [ncsrWordBleTT m p hlmp hlpm]
              exact ncsrLexBleTransEqLen m n p hlen1 hlen2 h1 h2
theorem ncsrNatBeqRefl : (a : Nat) → Nat.beq a a = true
  | 0 => rfl
  | Nat.succ k => ncsrNatBeqRefl k
theorem ncsrNatBeqSymm : (a b : Nat) → Nat.beq a b = Nat.beq b a
  | 0, 0 => rfl
  | 0, Nat.succ _ => rfl
  | Nat.succ _, 0 => rfl
  | Nat.succ x, Nat.succ y => ncsrNatBeqSymm x y
theorem ncsrNatEqOfBeq : (a b : Nat) → Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, Nat.succ _, h => Bool.noConfusion h
  | Nat.succ _, 0, h => Bool.noConfusion h
  | Nat.succ x, Nat.succ y, h => congrArg Nat.succ (ncsrNatEqOfBeq x y h)
theorem ncsrWordEqRefl : (m : List Nat) → ncsrWordEq m m = true
  | [] => rfl
  | a :: as => by
      show (Nat.beq a a && ncsrWordEq as as) = true
      rw [ncsrNatBeqRefl a, ncsrWordEqRefl as]; rfl
theorem ncsrWordEqSymm : (m n : List Nat) → ncsrWordEq m n = ncsrWordEq n m
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
      show (Nat.beq a b && ncsrWordEq as bs) = (Nat.beq b a && ncsrWordEq bs as)
      rw [ncsrNatBeqSymm a b, ncsrWordEqSymm as bs]
theorem ncsrWordEq_eq : (m n : List Nat) → ncsrWordEq m n = true → m = n
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | a :: as, b :: bs, h => by
      have hand : (Nat.beq a b && ncsrWordEq as bs) = true := h
      cases hab : Nat.beq a b with
      | false => rw [hab] at hand; exact Bool.noConfusion hand
      | true =>
          rw [hab] at hand
          rw [ncsrNatEqOfBeq a b hab, ncsrWordEq_eq as bs hand]
theorem ncsrWordEqOfEq (m n : List Nat) (h : m = n) : ncsrWordEq m n = true := by
  rw [h]; exact ncsrWordEqRefl n
theorem ncsrNatMulAssoc : (a b c : Nat) → a * b * c = a * (b * c)
  | a, b, 0 => by rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | a, b, Nat.succ c => by
      rw [Nat.mul_succ, ncsrNatMulAssoc a b c, Nat.mul_succ, Nat.mul_add]
theorem ncsrNatAddMul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]
theorem ncsrNatOneMul (d : Nat) : 1 * d = d := by
  rw [Nat.mul_comm 1 d, Nat.mul_one d]

/-- 3-way word comparison. -/
inductive NcsrWordOrd where
  | lt
  | eq
  | gt
def ncsrCompare (m n : List Nat) : NcsrWordOrd :=
  match ncsrWordEq m n with
  | true => NcsrWordOrd.eq
  | false => match ncsrWordBle m n with
             | true => NcsrWordOrd.lt
             | false => NcsrWordOrd.gt
theorem ncsrCompareEqExpand (m n : List Nat) (h : ncsrWordEq m n = true) :
    ncsrCompare m n = NcsrWordOrd.eq := by
  show (match ncsrWordEq m n with
        | true => NcsrWordOrd.eq
        | false => match ncsrWordBle m n with
                   | true => NcsrWordOrd.lt
                   | false => NcsrWordOrd.gt) = NcsrWordOrd.eq
  rw [h]
theorem ncsrCompareLtExpand (m n : List Nat) (h1 : ncsrWordEq m n = false) (h2 : ncsrWordBle m n = true) :
    ncsrCompare m n = NcsrWordOrd.lt := by
  show (match ncsrWordEq m n with
        | true => NcsrWordOrd.eq
        | false => match ncsrWordBle m n with
                   | true => NcsrWordOrd.lt
                   | false => NcsrWordOrd.gt) = NcsrWordOrd.lt
  rw [h1, h2]
theorem ncsrCompareGtExpand (m n : List Nat) (h1 : ncsrWordEq m n = false) (h2 : ncsrWordBle m n = false) :
    ncsrCompare m n = NcsrWordOrd.gt := by
  show (match ncsrWordEq m n with
        | true => NcsrWordOrd.eq
        | false => match ncsrWordBle m n with
                   | true => NcsrWordOrd.lt
                   | false => NcsrWordOrd.gt) = NcsrWordOrd.gt
  rw [h1, h2]
theorem ncsrCompareRefl (m : List Nat) : ncsrCompare m m = NcsrWordOrd.eq :=
  ncsrCompareEqExpand m m (ncsrWordEqRefl m)
theorem ncsrCompareOfEq (m n : List Nat) (h : m = n) : ncsrCompare m n = NcsrWordOrd.eq :=
  ncsrCompareEqExpand m n (ncsrWordEqOfEq m n h)
theorem ncsrCompareEq_of (m n : List Nat) (h : ncsrCompare m n = NcsrWordOrd.eq) : m = n := by
  cases hb : ncsrWordEq m n with
  | true => exact ncsrWordEq_eq m n hb
  | false =>
      cases hle : ncsrWordBle m n with
      | true => exact absurd h (by rw [ncsrCompareLtExpand m n hb hle]; exact fun hh => NcsrWordOrd.noConfusion hh)
      | false => exact absurd h (by rw [ncsrCompareGtExpand m n hb hle]; exact fun hh => NcsrWordOrd.noConfusion hh)
theorem ncsrCompareSwapLt (m n : List Nat) (h : ncsrCompare m n = NcsrWordOrd.lt) :
    ncsrCompare n m = NcsrWordOrd.gt := by
  cases hb : ncsrWordEq m n with
  | true => exact absurd h (by rw [ncsrCompareEqExpand m n hb]; exact fun hh => NcsrWordOrd.noConfusion hh)
  | false =>
      cases hle : ncsrWordBle m n with
      | false => exact absurd h (by rw [ncsrCompareGtExpand m n hb hle]; exact fun hh => NcsrWordOrd.noConfusion hh)
      | true =>
          have hnmEq : ncsrWordEq n m = false := by rw [ncsrWordEqSymm n m]; exact hb
          have hnmBle : ncsrWordBle n m = false := by
            cases hnm : ncsrWordBle n m with
            | false => rfl
            | true => exact absurd (ncsrWordBleAntisymm m n hle hnm) (fun heq => by
                rw [ncsrWordEqOfEq m n heq] at hb; exact Bool.noConfusion hb)
          exact ncsrCompareGtExpand n m hnmEq hnmBle
theorem ncsrCompareSwapGt (m n : List Nat) (h : ncsrCompare m n = NcsrWordOrd.gt) :
    ncsrCompare n m = NcsrWordOrd.lt := by
  cases hb : ncsrWordEq m n with
  | true => exact absurd h (by rw [ncsrCompareEqExpand m n hb]; exact fun hh => NcsrWordOrd.noConfusion hh)
  | false =>
      cases hle : ncsrWordBle m n with
      | true => exact absurd h (by rw [ncsrCompareLtExpand m n hb hle]; exact fun hh => NcsrWordOrd.noConfusion hh)
      | false =>
          have hnmEq : ncsrWordEq n m = false := by rw [ncsrWordEqSymm n m]; exact hb
          have hnmBle : ncsrWordBle n m = true := ncsrWordBleTotal m n hle
          exact ncsrCompareLtExpand n m hnmEq hnmBle
theorem ncsrCompareTransLt (m n p : List Nat)
    (h1 : ncsrCompare m n = NcsrWordOrd.lt) (h2 : ncsrCompare n p = NcsrWordOrd.lt) :
    ncsrCompare m p = NcsrWordOrd.lt := by
  have hmnEq : ncsrWordEq m n = false := by
    cases hb : ncsrWordEq m n with
    | false => rfl
    | true => exact absurd h1 (by rw [ncsrCompareEqExpand m n hb]; exact fun hh => NcsrWordOrd.noConfusion hh)
  have hmnBle : ncsrWordBle m n = true := by
    cases hle : ncsrWordBle m n with
    | true => rfl
    | false => exact absurd h1 (by rw [ncsrCompareGtExpand m n hmnEq hle]; exact fun hh => NcsrWordOrd.noConfusion hh)
  have hnpEq : ncsrWordEq n p = false := by
    cases hb : ncsrWordEq n p with
    | false => rfl
    | true => exact absurd h2 (by rw [ncsrCompareEqExpand n p hb]; exact fun hh => NcsrWordOrd.noConfusion hh)
  have hnpBle : ncsrWordBle n p = true := by
    cases hle : ncsrWordBle n p with
    | true => rfl
    | false => exact absurd h2 (by rw [ncsrCompareGtExpand n p hnpEq hle]; exact fun hh => NcsrWordOrd.noConfusion hh)
  have hmpBle : ncsrWordBle m p = true := ncsrWordBleTrans m n p hmnBle hnpBle
  have hmpEq : ncsrWordEq m p = false := by
    cases hb : ncsrWordEq m p with
    | false => rfl
    | true =>
        have hmeqp : m = p := ncsrWordEq_eq m p hb
        have hpn : ncsrWordBle p n = true := by rw [← hmeqp]; exact hmnBle
        have hneqp : n = p := ncsrWordBleAntisymm n p hnpBle hpn
        rw [ncsrWordEqOfEq n p hneqp] at hnpEq
        exact Bool.noConfusion hnpEq
  exact ncsrCompareLtExpand m p hmpEq hmpBle


abbrev NcsrNF := List (List Nat × Nat)

def ncsrInsertTerm : (List Nat × Nat) → NcsrNF → NcsrNF
  | term, [] => [term]
  | (m, c), (p, e) :: rest =>
      match ncsrCompare m p with
      | NcsrWordOrd.eq => (p, e + c) :: rest
      | NcsrWordOrd.lt => (m, c) :: (p, e) :: rest
      | NcsrWordOrd.gt => (p, e) :: ncsrInsertTerm (m, c) rest
theorem ncsrInsertTermNil (m : List Nat) (c : Nat) : ncsrInsertTerm (m, c) [] = [(m, c)] := rfl
theorem ncsrInsertTermEqE (m : List Nat) (c : Nat) (p : List Nat) (e : Nat) (rest : NcsrNF)
    (h : ncsrCompare m p = NcsrWordOrd.eq) :
    ncsrInsertTerm (m, c) ((p, e) :: rest) = (p, e + c) :: rest := by
  show (match ncsrCompare m p with
        | NcsrWordOrd.eq => (p, e + c) :: rest
        | NcsrWordOrd.lt => (m, c) :: (p, e) :: rest
        | NcsrWordOrd.gt => (p, e) :: ncsrInsertTerm (m, c) rest) = (p, e + c) :: rest
  rw [h]
theorem ncsrInsertTermLtE (m : List Nat) (c : Nat) (p : List Nat) (e : Nat) (rest : NcsrNF)
    (h : ncsrCompare m p = NcsrWordOrd.lt) :
    ncsrInsertTerm (m, c) ((p, e) :: rest) = (m, c) :: (p, e) :: rest := by
  show (match ncsrCompare m p with
        | NcsrWordOrd.eq => (p, e + c) :: rest
        | NcsrWordOrd.lt => (m, c) :: (p, e) :: rest
        | NcsrWordOrd.gt => (p, e) :: ncsrInsertTerm (m, c) rest) = (m, c) :: (p, e) :: rest
  rw [h]
theorem ncsrInsertTermGtE (m : List Nat) (c : Nat) (p : List Nat) (e : Nat) (rest : NcsrNF)
    (h : ncsrCompare m p = NcsrWordOrd.gt) :
    ncsrInsertTerm (m, c) ((p, e) :: rest) = (p, e) :: ncsrInsertTerm (m, c) rest := by
  show (match ncsrCompare m p with
        | NcsrWordOrd.eq => (p, e + c) :: rest
        | NcsrWordOrd.lt => (m, c) :: (p, e) :: rest
        | NcsrWordOrd.gt => (p, e) :: ncsrInsertTerm (m, c) rest) = (p, e) :: ncsrInsertTerm (m, c) rest
  rw [h]
theorem ncsrAddRightComm (e d c : Nat) : e + d + c = e + c + d := by
  rw [Nat.add_assoc e d c, Nat.add_comm d c, ← Nat.add_assoc e c d]
theorem ncsrInsertTermComm (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) (P : NcsrNF) :
    ncsrInsertTerm (m, c) (ncsrInsertTerm (n, d) P)
      = ncsrInsertTerm (n, d) (ncsrInsertTerm (m, c) P) := by
  induction P with
  | nil =>
      cases hmn : ncsrCompare m n with
      | eq =>
          have hmeqn : m = n := ncsrCompareEq_of m n hmn
          have hnm : ncsrCompare n m = NcsrWordOrd.eq := ncsrCompareOfEq n m hmeqn.symm
          rw [ncsrInsertTermNil n d, ncsrInsertTermNil m c,
              ncsrInsertTermEqE m c n d [] hmn, ncsrInsertTermEqE n d m c [] hnm, hmeqn,
              Nat.add_comm d c]
      | lt =>
          have hnm : ncsrCompare n m = NcsrWordOrd.gt := ncsrCompareSwapLt m n hmn
          rw [ncsrInsertTermNil n d, ncsrInsertTermNil m c,
              ncsrInsertTermLtE m c n d [] hmn, ncsrInsertTermGtE n d m c [] hnm, ncsrInsertTermNil n d]
      | gt =>
          have hnm : ncsrCompare n m = NcsrWordOrd.lt := ncsrCompareSwapGt m n hmn
          rw [ncsrInsertTermNil n d, ncsrInsertTermNil m c,
              ncsrInsertTermGtE m c n d [] hmn, ncsrInsertTermNil m c, ncsrInsertTermLtE n d m c [] hnm]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : ncsrCompare n p with
      | eq =>
          have hnp_eq : n = p := ncsrCompareEq_of n p hnp
          rw [ncsrInsertTermEqE n d p e rest hnp]
          cases hmp : ncsrCompare m p with
          | eq =>
              rw [ncsrInsertTermEqE m c p (e + d) rest hmp, ncsrInsertTermEqE m c p e rest hmp,
                  ncsrInsertTermEqE n d p (e + c) rest hnp, ncsrAddRightComm e d c]
          | lt =>
              have hpm : ncsrCompare p m = NcsrWordOrd.gt := ncsrCompareSwapLt m p hmp
              have hnm : ncsrCompare n m = NcsrWordOrd.gt := by rw [hnp_eq]; exact hpm
              rw [ncsrInsertTermLtE m c p (e + d) rest hmp, ncsrInsertTermLtE m c p e rest hmp,
                  ncsrInsertTermGtE n d m c ((p, e) :: rest) hnm, ncsrInsertTermEqE n d p e rest hnp]
          | gt =>
              rw [ncsrInsertTermGtE m c p (e + d) rest hmp, ncsrInsertTermGtE m c p e rest hmp,
                  ncsrInsertTermEqE n d p e (ncsrInsertTerm (m, c) rest) hnp]
      | lt =>
          rw [ncsrInsertTermLtE n d p e rest hnp]
          cases hmn : ncsrCompare m n with
          | eq =>
              have hmeqn : m = n := ncsrCompareEq_of m n hmn
              have hnm : ncsrCompare n m = NcsrWordOrd.eq := ncsrCompareOfEq n m hmeqn.symm
              have hmp : ncsrCompare m p = NcsrWordOrd.lt := by rw [hmeqn]; exact hnp
              rw [ncsrInsertTermEqE m c n d ((p, e) :: rest) hmn, ncsrInsertTermLtE m c p e rest hmp,
                  ncsrInsertTermEqE n d m c ((p, e) :: rest) hnm, hmeqn, Nat.add_comm d c]
          | lt =>
              have hmp : ncsrCompare m p = NcsrWordOrd.lt := ncsrCompareTransLt m n p hmn hnp
              have hnm : ncsrCompare n m = NcsrWordOrd.gt := ncsrCompareSwapLt m n hmn
              rw [ncsrInsertTermLtE m c n d ((p, e) :: rest) hmn, ncsrInsertTermLtE m c p e rest hmp,
                  ncsrInsertTermGtE n d m c ((p, e) :: rest) hnm, ncsrInsertTermLtE n d p e rest hnp]
          | gt =>
              have hmn_gt : ncsrCompare m n = NcsrWordOrd.gt := hmn
              rw [ncsrInsertTermGtE m c n d ((p, e) :: rest) hmn]
              cases hmp : ncsrCompare m p with
              | eq =>
                  rw [ncsrInsertTermEqE m c p e rest hmp,
                      ncsrInsertTermLtE n d p (e + c) rest hnp]
              | lt =>
                  have hnm : ncsrCompare n m = NcsrWordOrd.lt := ncsrCompareSwapGt m n hmn_gt
                  rw [ncsrInsertTermLtE m c p e rest hmp,
                      ncsrInsertTermLtE n d m c ((p, e) :: rest) hnm]
              | gt =>
                  rw [ncsrInsertTermGtE m c p e rest hmp,
                      ncsrInsertTermLtE n d p e (ncsrInsertTerm (m, c) rest) hnp]
      | gt =>
          rw [ncsrInsertTermGtE n d p e rest hnp]
          cases hmp : ncsrCompare m p with
          | eq =>
              rw [ncsrInsertTermEqE m c p e (ncsrInsertTerm (n, d) rest) hmp,
                  ncsrInsertTermEqE m c p e rest hmp,
                  ncsrInsertTermGtE n d p (e + c) rest hnp]
          | lt =>
              have hpn : ncsrCompare p n = NcsrWordOrd.lt := ncsrCompareSwapGt n p hnp
              have hmn : ncsrCompare m n = NcsrWordOrd.lt := ncsrCompareTransLt m p n hmp hpn
              have hnm : ncsrCompare n m = NcsrWordOrd.gt := ncsrCompareSwapLt m n hmn
              rw [ncsrInsertTermLtE m c p e (ncsrInsertTerm (n, d) rest) hmp,
                  ncsrInsertTermLtE m c p e rest hmp,
                  ncsrInsertTermGtE n d m c ((p, e) :: rest) hnm,
                  ncsrInsertTermGtE n d p e rest hnp]
          | gt =>
              rw [ncsrInsertTermGtE m c p e (ncsrInsertTerm (n, d) rest) hmp,
                  ncsrInsertTermGtE m c p e rest hmp,
                  ncsrInsertTermGtE n d p e (ncsrInsertTerm (m, c) rest) hnp, ih]

-- boolean helpers
theorem ncsrAndTrueLeft (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a with | true => rfl | false => exact Bool.noConfusion h
theorem ncsrAndTrueRight (a b : Bool) (h : (a && b) = true) : b = true := by
  cases a with | true => exact h | false => exact Bool.noConfusion h
theorem ncsrAndIntro (a b : Bool) (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]; rfl

-- additive engine
def ncsrMergeAdd : NcsrNF → NcsrNF → NcsrNF
  | [], b => b
  | t :: a', b => ncsrInsertTerm t (ncsrMergeAdd a' b)
theorem ncsrMergeAddNilLeft (b : NcsrNF) : ncsrMergeAdd [] b = b := rfl
theorem ncsrMergeAddCons (t : List Nat × Nat) (a' b : NcsrNF) :
    ncsrMergeAdd (t :: a') b = ncsrInsertTerm t (ncsrMergeAdd a' b) := rfl
theorem ncsrInsertTerm_mergeAdd (t : List Nat × Nat) (a b : NcsrNF) :
    ncsrInsertTerm t (ncsrMergeAdd a b) = ncsrMergeAdd a (ncsrInsertTerm t b) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      obtain ⟨um, uc⟩ := u
      obtain ⟨tm, tc⟩ := t
      show ncsrInsertTerm (tm, tc) (ncsrInsertTerm (um, uc) (ncsrMergeAdd a' b))
        = ncsrMergeAdd ((um, uc) :: a') (ncsrInsertTerm (tm, tc) b)
      rw [ncsrMergeAddCons, ncsrInsertTermComm tm tc um uc (ncsrMergeAdd a' b), ih]
/-- inserting the same word twice collapses (coefficients add). -/
theorem ncsrInsertTermMergeSame (m : List Nat) (c1 c2 : Nat) (Z : NcsrNF) :
    ncsrInsertTerm (m, c1) (ncsrInsertTerm (m, c2) Z) = ncsrInsertTerm (m, c2 + c1) Z := by
  induction Z with
  | nil =>
      rw [ncsrInsertTermNil m c2, ncsrInsertTermEqE m c1 m c2 [] (ncsrCompareRefl m),
          ncsrInsertTermNil m (c2 + c1)]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : ncsrCompare m p with
      | eq =>
          rw [ncsrInsertTermEqE m c2 p e rest hmp, ncsrInsertTermEqE m c1 p (e + c2) rest hmp,
              ncsrInsertTermEqE m (c2 + c1) p e rest hmp, Nat.add_assoc e c2 c1]
      | lt =>
          rw [ncsrInsertTermLtE m c2 p e rest hmp, ncsrInsertTermEqE m c1 m c2 ((p, e) :: rest)
                (ncsrCompareRefl m), ncsrInsertTermLtE m (c2 + c1) p e rest hmp]
      | gt =>
          rw [ncsrInsertTermGtE m c2 p e rest hmp, ncsrInsertTermGtE m c1 p e
                (ncsrInsertTerm (m, c2) rest) hmp, ncsrInsertTermGtE m (c2 + c1) p e rest hmp, ih]
/-- pulling an insertion out of the left list of a merge. -/
theorem ncsrMergeAddInsertTermLeft (u : List Nat × Nat) (Y c : NcsrNF) :
    ncsrMergeAdd (ncsrInsertTerm u Y) c = ncsrInsertTerm u (ncsrMergeAdd Y c) := by
  obtain ⟨um, uc⟩ := u
  induction Y with
  | nil => rfl
  | cons head Y' ih =>
      obtain ⟨v, ve⟩ := head
      cases huv : ncsrCompare um v with
      | eq =>
          have hum_eq : um = v := ncsrCompareEq_of um v huv
          rw [ncsrInsertTermEqE um uc v ve Y' huv, ncsrMergeAddCons,
              ncsrMergeAddCons (v, ve) Y' c, hum_eq,
              ncsrInsertTermMergeSame v uc ve (ncsrMergeAdd Y' c)]
      | lt =>
          rw [ncsrInsertTermLtE um uc v ve Y' huv, ncsrMergeAddCons, ncsrMergeAddCons (v, ve) Y' c]
      | gt =>
          rw [ncsrInsertTermGtE um uc v ve Y' huv, ncsrMergeAddCons (v, ve) (ncsrInsertTerm (um, uc) Y') c,
              ncsrMergeAddCons (v, ve) Y' c, ih,
              ncsrInsertTermComm v ve um uc (ncsrMergeAdd Y' c)]
theorem ncsrMergeAddAssoc (a b c : NcsrNF) :
    ncsrMergeAdd (ncsrMergeAdd a b) c = ncsrMergeAdd a (ncsrMergeAdd b c) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show ncsrMergeAdd (ncsrInsertTerm u (ncsrMergeAdd a' b)) c
        = ncsrInsertTerm u (ncsrMergeAdd a' (ncsrMergeAdd b c))
      rw [ncsrMergeAddInsertTermLeft u (ncsrMergeAdd a' b) c, ih]
theorem ncsrMergeAddSwap (a b acc : NcsrNF) :
    ncsrMergeAdd a (ncsrMergeAdd b acc) = ncsrMergeAdd b (ncsrMergeAdd a acc) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show ncsrInsertTerm u (ncsrMergeAdd a' (ncsrMergeAdd b acc))
        = ncsrMergeAdd b (ncsrInsertTerm u (ncsrMergeAdd a' acc))
      rw [ih, ncsrInsertTerm_mergeAdd u b (ncsrMergeAdd a' acc)]

-- sortedness invariant
def ncsrBelowHead (m : List Nat) : NcsrNF → Bool
  | [] => true
  | (p, _) :: _ =>
      match ncsrCompare m p with
      | NcsrWordOrd.lt => true
      | NcsrWordOrd.eq => false
      | NcsrWordOrd.gt => false
def ncsrNFSorted : NcsrNF → Bool
  | [] => true
  | (m, _) :: rest => ncsrBelowHead m rest && ncsrNFSorted rest
theorem ncsrBelowHeadNil (m : List Nat) : ncsrBelowHead m [] = true := rfl
theorem ncsrBelowHeadConsTrue (m p : List Nat) (e : Nat) (rest : NcsrNF)
    (h : ncsrCompare m p = NcsrWordOrd.lt) : ncsrBelowHead m ((p, e) :: rest) = true := by
  show (match ncsrCompare m p with
        | NcsrWordOrd.lt => true
        | NcsrWordOrd.eq => false
        | NcsrWordOrd.gt => false) = true
  rw [h]
theorem ncsrBelowHeadConsLt (m p : List Nat) (e : Nat) (rest : NcsrNF)
    (h : ncsrBelowHead m ((p, e) :: rest) = true) : ncsrCompare m p = NcsrWordOrd.lt := by
  cases hc : ncsrCompare m p with
  | lt => rfl
  | eq => exact absurd h (by
      show (match ncsrCompare m p with
            | NcsrWordOrd.lt => true | NcsrWordOrd.eq => false | NcsrWordOrd.gt => false) ≠ true
      rw [hc]; exact fun hh => Bool.noConfusion hh)
  | gt => exact absurd h (by
      show (match ncsrCompare m p with
            | NcsrWordOrd.lt => true | NcsrWordOrd.eq => false | NcsrWordOrd.gt => false) ≠ true
      rw [hc]; exact fun hh => Bool.noConfusion hh)
theorem ncsrNFSortedCons (m : List Nat) (c : Nat) (rest : NcsrNF) :
    ncsrNFSorted ((m, c) :: rest) = (ncsrBelowHead m rest && ncsrNFSorted rest) := rfl
theorem ncsrBelowHeadInsert (q m : List Nat) (c : Nat) (B : NcsrNF)
    (hq : ncsrCompare q m = NcsrWordOrd.lt) (hB : ncsrBelowHead q B = true) :
    ncsrBelowHead q (ncsrInsertTerm (m, c) B) = true := by
  cases B with
  | nil => exact ncsrBelowHeadConsTrue q m c [] hq
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      cases hmp : ncsrCompare m p with
      | eq => rw [ncsrInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [ncsrInsertTermLtE m c p e rest hmp]; exact ncsrBelowHeadConsTrue q m c ((p, e) :: rest) hq
      | gt =>
          rw [ncsrInsertTermGtE m c p e rest hmp]
          exact ncsrBelowHeadConsTrue q p e (ncsrInsertTerm (m, c) rest) (ncsrBelowHeadConsLt q p e rest hB)
theorem ncsrInsertPreservesSorted (m : List Nat) (c : Nat) (B : NcsrNF)
    (hB : ncsrNFSorted B = true) : ncsrNFSorted (ncsrInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hbelow : ncsrBelowHead p rest = true := ncsrAndTrueLeft _ _ hB
      have hrest : ncsrNFSorted rest = true := ncsrAndTrueRight _ _ hB
      cases hmp : ncsrCompare m p with
      | eq => rw [ncsrInsertTermEqE m c p e rest hmp]; exact hB
      | lt =>
          rw [ncsrInsertTermLtE m c p e rest hmp, ncsrNFSortedCons]
          exact ncsrAndIntro _ _ (ncsrBelowHeadConsTrue m p e rest hmp) hB
      | gt =>
          rw [ncsrInsertTermGtE m c p e rest hmp, ncsrNFSortedCons]
          have hpm : ncsrCompare p m = NcsrWordOrd.lt := ncsrCompareSwapGt m p hmp
          exact ncsrAndIntro _ _
            (ncsrBelowHeadInsert p m c rest hpm hbelow) (ih hrest)
theorem ncsrInsertFront (m : List Nat) (c : Nat) (B : NcsrNF) (h : ncsrBelowHead m B = true) :
    ncsrInsertTerm (m, c) B = (m, c) :: B := by
  cases B with
  | nil => rfl
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      exact ncsrInsertTermLtE m c p e rest (ncsrBelowHeadConsLt m p e rest h)
theorem ncsrMergeAddNilRight (A : NcsrNF) (hA : ncsrNFSorted A = true) : ncsrMergeAdd A [] = A := by
  induction A with
  | nil => rfl
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      have hbelow : ncsrBelowHead m a' = true := ncsrAndTrueLeft _ _ hA
      have hrest : ncsrNFSorted a' = true := ncsrAndTrueRight _ _ hA
      show ncsrInsertTerm (m, c) (ncsrMergeAdd a' []) = (m, c) :: a'
      rw [ih hrest, ncsrInsertFront m c a' hbelow]
theorem ncsrMergeAddComm (A B : NcsrNF) (hA : ncsrNFSorted A = true) (hB : ncsrNFSorted B = true) :
    ncsrMergeAdd A B = ncsrMergeAdd B A := by
  have h := ncsrMergeAddSwap A B []
  rw [ncsrMergeAddNilRight B hB, ncsrMergeAddNilRight A hA] at h
  exact h
theorem ncsrMergeAddPreservesSorted (A B : NcsrNF) (hB : ncsrNFSorted B = true) :
    ncsrNFSorted (ncsrMergeAdd A B) = true := by
  induction A with
  | nil => exact hB
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      show ncsrNFSorted (ncsrInsertTerm (m, c) (ncsrMergeAdd a' B)) = true
      exact ncsrInsertPreservesSorted m c (ncsrMergeAdd a' B) ih


-- word multiplication = CONCATENATION (order-significant, cons-only recursion on the first word)
def ncsrWordCat : List Nat → List Nat → List Nat
  | [], n => n
  | a :: as, n => a :: ncsrWordCat as n
theorem ncsrWordCatNilLeft (n : List Nat) : ncsrWordCat [] n = n := rfl
theorem ncsrWordCatNilRight : (m : List Nat) → ncsrWordCat m [] = m
  | [] => rfl
  | a :: as => by
      show a :: ncsrWordCat as [] = a :: as
      rw [ncsrWordCatNilRight as]
theorem ncsrWordCatAssoc : (m n p : List Nat) →
    ncsrWordCat (ncsrWordCat m n) p = ncsrWordCat m (ncsrWordCat n p)
  | [], _, _ => rfl
  | a :: as, n, p => by
      show a :: ncsrWordCat (ncsrWordCat as n) p = a :: ncsrWordCat as (ncsrWordCat n p)
      rw [ncsrWordCatAssoc as n p]


-- single word times a poly (right multiply), and the convolution
def ncsrTermMul (m : List Nat) (c : Nat) : NcsrNF → NcsrNF
  | [] => []
  | (n, d) :: rest => ncsrInsertTerm (ncsrWordCat m n, c * d) (ncsrTermMul m c rest)
def ncsrMulConvolve : NcsrNF → NcsrNF → NcsrNF
  | [], _ => []
  | (m, c) :: rest, b => ncsrMergeAdd (ncsrTermMul m c b) (ncsrMulConvolve rest b)
theorem ncsrTermMulNil (m : List Nat) (c : Nat) : ncsrTermMul m c [] = [] := rfl
theorem ncsrTermMulCons (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) (rest : NcsrNF) :
    ncsrTermMul m c ((n, d) :: rest) = ncsrInsertTerm (ncsrWordCat m n, c * d) (ncsrTermMul m c rest) := rfl
theorem ncsrMulConvolveNil (b : NcsrNF) : ncsrMulConvolve [] b = [] := rfl
theorem ncsrMulConvolveCons (m : List Nat) (c : Nat) (rest b : NcsrNF) :
    ncsrMulConvolve ((m, c) :: rest) b = ncsrMergeAdd (ncsrTermMul m c b) (ncsrMulConvolve rest b) := rfl

theorem ncsrTermMulSorted (m : List Nat) (c : Nat) (B : NcsrNF) :
    ncsrNFSorted (ncsrTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show ncsrNFSorted (ncsrInsertTerm (ncsrWordCat m n, c * d) (ncsrTermMul m c rest)) = true
      exact ncsrInsertPreservesSorted (ncsrWordCat m n) (c * d) (ncsrTermMul m c rest) ih
theorem ncsrMulConvolveSorted (A B : NcsrNF) : ncsrNFSorted (ncsrMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show ncsrNFSorted (ncsrMergeAdd (ncsrTermMul m c B) (ncsrMulConvolve rest B)) = true
      exact ncsrMergeAddPreservesSorted (ncsrTermMul m c B) (ncsrMulConvolve rest B) ih

/-- ★ termMul commutes with a single insertion (coefficients distribute via `Nat.mul_add`). -/
theorem ncsrTermMul_insertTerm (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) (B : NcsrNF) :
    ncsrTermMul m c (ncsrInsertTerm (n, d) B)
      = ncsrInsertTerm (ncsrWordCat m n, c * d) (ncsrTermMul m c B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : ncsrCompare n p with
      | eq =>
          have hnp_eq : n = p := ncsrCompareEq_of n p hnp
          rw [ncsrInsertTermEqE n d p e rest hnp, ncsrTermMulCons m c p (e + d) rest,
              ncsrTermMulCons m c p e rest, hnp_eq,
              ncsrInsertTermMergeSame (ncsrWordCat m p) (c * d) (c * e) (ncsrTermMul m c rest),
              Nat.mul_add c e d]
      | lt =>
          rw [ncsrInsertTermLtE n d p e rest hnp, ncsrTermMulCons m c n d ((p, e) :: rest),
              ncsrTermMulCons m c p e rest]
      | gt =>
          rw [ncsrInsertTermGtE n d p e rest hnp, ncsrTermMulCons m c p e (ncsrInsertTerm (n, d) rest),
              ih, ncsrTermMulCons m c p e rest,
              ncsrInsertTermComm (ncsrWordCat m p) (c * e) (ncsrWordCat m n) (c * d) (ncsrTermMul m c rest)]

theorem ncsrTermMul_merge (m : List Nat) (c : Nat) (B C : NcsrNF) :
    ncsrTermMul m c (ncsrMergeAdd B C) = ncsrMergeAdd (ncsrTermMul m c B) (ncsrTermMul m c C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show ncsrTermMul m c (ncsrInsertTerm (n, d) (ncsrMergeAdd B' C))
        = ncsrMergeAdd (ncsrInsertTerm (ncsrWordCat m n, c * d) (ncsrTermMul m c B')) (ncsrTermMul m c C)
      rw [ncsrTermMul_insertTerm m c n d (ncsrMergeAdd B' C), ih,
          ncsrMergeAddInsertTermLeft (ncsrWordCat m n, c * d) (ncsrTermMul m c B') (ncsrTermMul m c C)]

/-- ★ RIGHT annihilation `a·0 = 0` (the left annihilation `0·a = 0` is `ncsrMulConvolveNil`, rfl). -/
theorem ncsrMulConvolveAnnihil (A : NcsrNF) : ncsrMulConvolve A [] = [] := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show ncsrMergeAdd (ncsrTermMul m c []) (ncsrMulConvolve rest []) = []
      rw [ncsrTermMulNil m c, ncsrMergeAddNilLeft, ih]

/-- rearrange a merge of four sorted NFs, swapping the inner two. -/
theorem ncsrMergeAdd4Swap (a b c d : NcsrNF)
    (hb : ncsrNFSorted b = true) (hc : ncsrNFSorted c = true) :
    ncsrMergeAdd (ncsrMergeAdd a b) (ncsrMergeAdd c d)
      = ncsrMergeAdd (ncsrMergeAdd a c) (ncsrMergeAdd b d) := by
  rw [ncsrMergeAddAssoc a b (ncsrMergeAdd c d), ← ncsrMergeAddAssoc b c d,
      ncsrMergeAddComm b c hb hc, ncsrMergeAddAssoc c b d, ← ncsrMergeAddAssoc a c (ncsrMergeAdd b d)]

/-- ★ left distributivity: `A · (B + C) = A·B + A·C`. -/
theorem ncsrMulConvolve_leftDistrib (A B C : NcsrNF) :
    ncsrMulConvolve A (ncsrMergeAdd B C)
      = ncsrMergeAdd (ncsrMulConvolve A B) (ncsrMulConvolve A C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show ncsrMergeAdd (ncsrTermMul m c (ncsrMergeAdd B C)) (ncsrMulConvolve A' (ncsrMergeAdd B C))
        = ncsrMergeAdd (ncsrMergeAdd (ncsrTermMul m c B) (ncsrMulConvolve A' B))
            (ncsrMergeAdd (ncsrTermMul m c C) (ncsrMulConvolve A' C))
      rw [ncsrTermMul_merge m c B C, ih]
      exact ncsrMergeAdd4Swap (ncsrTermMul m c B) (ncsrTermMul m c C) (ncsrMulConvolve A' B)
        (ncsrMulConvolve A' C) (ncsrTermMulSorted m c C) (ncsrMulConvolveSorted A' B)


/-- termMul distributes over a coefficient sum. -/
theorem ncsrTermMul_coeffAdd (m : List Nat) (c1 c2 : Nat) (Z : NcsrNF) :
    ncsrTermMul m (c1 + c2) Z = ncsrMergeAdd (ncsrTermMul m c1 Z) (ncsrTermMul m c2 Z) := by
  induction Z with
  | nil => rfl
  | cons head Z' ih =>
      obtain ⟨n, d⟩ := head
      show ncsrInsertTerm (ncsrWordCat m n, (c1 + c2) * d) (ncsrTermMul m (c1 + c2) Z')
        = ncsrMergeAdd (ncsrInsertTerm (ncsrWordCat m n, c1 * d) (ncsrTermMul m c1 Z'))
            (ncsrInsertTerm (ncsrWordCat m n, c2 * d) (ncsrTermMul m c2 Z'))
      rw [ncsrMergeAddInsertTermLeft (ncsrWordCat m n, c1 * d) (ncsrTermMul m c1 Z')
            (ncsrInsertTerm (ncsrWordCat m n, c2 * d) (ncsrTermMul m c2 Z')),
          ← ncsrInsertTerm_mergeAdd (ncsrWordCat m n, c2 * d) (ncsrTermMul m c1 Z') (ncsrTermMul m c2 Z'),
          ncsrInsertTermMergeSame (ncsrWordCat m n) (c1 * d) (c2 * d)
            (ncsrMergeAdd (ncsrTermMul m c1 Z') (ncsrTermMul m c2 Z')),
          ih, ncsrNatAddMul c1 c2 d, Nat.add_comm (c1 * d) (c2 * d)]

/-- convolving after one insertion into the first argument. -/
theorem ncsrConvolve_insertTermLeft (m : List Nat) (c : Nat) (W Z : NcsrNF) :
    ncsrMulConvolve (ncsrInsertTerm (m, c) W) Z
      = ncsrMergeAdd (ncsrTermMul m c Z) (ncsrMulConvolve W Z) := by
  induction W with
  | nil => rfl
  | cons head W' ih =>
      obtain ⟨p, g⟩ := head
      cases hmp : ncsrCompare m p with
      | eq =>
          have hmeqp : m = p := ncsrCompareEq_of m p hmp
          rw [ncsrInsertTermEqE m c p g W' hmp, ncsrMulConvolveCons p (g + c) W' Z,
              ncsrMulConvolveCons p g W' Z, hmeqp,
              ncsrTermMul_coeffAdd p g c Z,
              ncsrMergeAddAssoc (ncsrTermMul p g Z) (ncsrTermMul p c Z) (ncsrMulConvolve W' Z),
              ncsrMergeAddSwap (ncsrTermMul p g Z) (ncsrTermMul p c Z) (ncsrMulConvolve W' Z)]
      | lt =>
          rw [ncsrInsertTermLtE m c p g W' hmp, ncsrMulConvolveCons m c ((p, g) :: W') Z]
      | gt =>
          rw [ncsrInsertTermGtE m c p g W' hmp,
              ncsrMulConvolveCons p g (ncsrInsertTerm (m, c) W') Z, ih,
              ncsrMulConvolveCons p g W' Z,
              ncsrMergeAddSwap (ncsrTermMul p g Z) (ncsrTermMul m c Z) (ncsrMulConvolve W' Z)]

/-- ★ right distributivity: `(X + Y) · Z = X·Z + Y·Z`. -/
theorem ncsrMulConvolve_rightDistrib (X Y Z : NcsrNF) :
    ncsrMulConvolve (ncsrMergeAdd X Y) Z
      = ncsrMergeAdd (ncsrMulConvolve X Z) (ncsrMulConvolve Y Z) := by
  induction X with
  | nil => rfl
  | cons head X' ih =>
      obtain ⟨m, c⟩ := head
      show ncsrMulConvolve (ncsrInsertTerm (m, c) (ncsrMergeAdd X' Y)) Z
        = ncsrMergeAdd (ncsrMergeAdd (ncsrTermMul m c Z) (ncsrMulConvolve X' Z)) (ncsrMulConvolve Y Z)
      rw [ncsrConvolve_insertTermLeft m c (ncsrMergeAdd X' Y) Z, ih,
          ncsrMergeAddAssoc (ncsrTermMul m c Z) (ncsrMulConvolve X' Z) (ncsrMulConvolve Y Z)]

/-- termMul composition: `(m++n)·(c*d)` applied to `C` equals scaling by `(m,c)` then `(n,d)`
    — word CONCATENATION replaces the sibling's multiset union. -/
theorem ncsrTermMul_compose (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) (C : NcsrNF) :
    ncsrTermMul (ncsrWordCat m n) (c * d) C = ncsrTermMul m c (ncsrTermMul n d C) := by
  induction C with
  | nil => rfl
  | cons head C' ih =>
      obtain ⟨p, f⟩ := head
      show ncsrInsertTerm (ncsrWordCat (ncsrWordCat m n) p, c * d * f)
            (ncsrTermMul (ncsrWordCat m n) (c * d) C')
        = ncsrTermMul m c (ncsrInsertTerm (ncsrWordCat n p, d * f) (ncsrTermMul n d C'))
      rw [ncsrTermMul_insertTerm m c (ncsrWordCat n p) (d * f) (ncsrTermMul n d C'), ih,
          ncsrWordCatAssoc m n p, ncsrNatMulAssoc c d f]

/-- convolving a termMul equals termMul of a convolve. -/
theorem ncsrTermMul_convolve (m : List Nat) (c : Nat) (B C : NcsrNF) :
    ncsrMulConvolve (ncsrTermMul m c B) C = ncsrTermMul m c (ncsrMulConvolve B C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show ncsrMulConvolve (ncsrInsertTerm (ncsrWordCat m n, c * d) (ncsrTermMul m c B')) C
        = ncsrTermMul m c (ncsrMergeAdd (ncsrTermMul n d C) (ncsrMulConvolve B' C))
      rw [ncsrConvolve_insertTermLeft (ncsrWordCat m n) (c * d) (ncsrTermMul m c B') C, ih,
          ncsrTermMul_merge m c (ncsrTermMul n d C) (ncsrMulConvolve B' C),
          ncsrTermMul_compose m c n d C]

/-- ★ associativity of the convolution: `(A·B)·C = A·(B·C)`. -/
theorem ncsrMulConvolveAssoc (A B C : NcsrNF) :
    ncsrMulConvolve (ncsrMulConvolve A B) C = ncsrMulConvolve A (ncsrMulConvolve B C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show ncsrMulConvolve (ncsrMergeAdd (ncsrTermMul m c B) (ncsrMulConvolve A' B)) C
        = ncsrMergeAdd (ncsrTermMul m c (ncsrMulConvolve B C)) (ncsrMulConvolve A' (ncsrMulConvolve B C))
      rw [ncsrMulConvolve_rightDistrib (ncsrTermMul m c B) (ncsrMulConvolve A' B) C, ih,
          ncsrTermMul_convolve m c B C]


/-- termMul by the empty word and coefficient `1` rebuilds a sorted NF unchanged
    (feeds the multiplicative LEFT unit `1·a = a`). -/
theorem ncsrTermMulIdent : (A : NcsrNF) → ncsrNFSorted A = true → ncsrTermMul [] 1 A = A
  | [], _ => rfl
  | (n, d) :: A', hA => by
      have hbelow : ncsrBelowHead n A' = true := ncsrAndTrueLeft _ _ hA
      have hA' : ncsrNFSorted A' = true := ncsrAndTrueRight _ _ hA
      have ih := ncsrTermMulIdent A' hA'
      show ncsrInsertTerm (ncsrWordCat [] n, 1 * d) (ncsrTermMul [] 1 A') = (n, d) :: A'
      rw [ih, ncsrNatOneMul d]
      show ncsrInsertTerm (n, d) A' = (n, d) :: A'
      exact ncsrInsertFront n d A' hbelow

/-- ★ multiplicative LEFT unit: `[([],1)] · A = A` for a sorted NF. -/
theorem ncsrMulConvolveUnitLeft (A : NcsrNF) (hA : ncsrNFSorted A = true) :
    ncsrMulConvolve [([], 1)] A = A := by
  show ncsrMergeAdd (ncsrTermMul [] 1 A) [] = A
  rw [ncsrTermMulIdent A hA, ncsrMergeAddNilRight A hA]

/-- ★ multiplicative RIGHT unit: `A · [([],1)] = A` for a sorted NF. -/
theorem ncsrMulConvolveUnitRight : (A : NcsrNF) → ncsrNFSorted A = true → ncsrMulConvolve A [([], 1)] = A
  | [], _ => rfl
  | (m, c) :: A', hAs => by
      have hbelow : ncsrBelowHead m A' = true := ncsrAndTrueLeft _ _ hAs
      have hAs' : ncsrNFSorted A' = true := ncsrAndTrueRight _ _ hAs
      have ih := ncsrMulConvolveUnitRight A' hAs'
      show ncsrMergeAdd (ncsrTermMul m c [([], 1)]) (ncsrMulConvolve A' [([], 1)]) = (m, c) :: A'
      rw [ncsrTermMulCons m c [] 1 [], ncsrTermMulNil m c, ncsrWordCatNilRight m, Nat.mul_one c,
          ncsrMergeAddInsertTermLeft (m, c) [] (ncsrMulConvolve A' [([], 1)]), ncsrMergeAddNilLeft,
          ih, ncsrInsertFront m c A' hbelow]


/-- ★ the free non-commutative-semiring tree carrier. -/
inductive NcsrTree where
  /-- a colour-tagged generator (variable). -/
  | gen (colour : Nat)
  /-- the additive unit `0`. -/
  | zeroOp
  /-- the multiplicative unit `1`. -/
  | oneOp
  /-- binary addition. -/
  | addOp : NcsrTree → NcsrTree → NcsrTree
  /-- binary multiplication (NON-commutative). -/
  | mulOp : NcsrTree → NcsrTree → NcsrTree

/-- ★ normalize a tree to its non-commutative polynomial normal form (sorted terms, positive coefficients). -/
def ncsrNormalize : NcsrTree → NcsrNF
  | .gen colour => [([colour], 1)]
  | .zeroOp => []
  | .oneOp => [([], 1)]
  | .addOp l r => ncsrMergeAdd (ncsrNormalize l) (ncsrNormalize r)
  | .mulOp l r => ncsrMulConvolve (ncsrNormalize l) (ncsrNormalize r)

theorem ncsrNormalize_gen (c : Nat) : ncsrNormalize (NcsrTree.gen c) = [([c], 1)] := rfl
theorem ncsrNormalizeSorted (t : NcsrTree) : ncsrNFSorted (ncsrNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | addOp l r ihl ihr =>
      show ncsrNFSorted (ncsrMergeAdd (ncsrNormalize l) (ncsrNormalize r)) = true
      exact ncsrMergeAddPreservesSorted (ncsrNormalize l) (ncsrNormalize r) ihr
  | mulOp l r _ _ =>
      show ncsrNFSorted (ncsrMulConvolve (ncsrNormalize l) (ncsrNormalize r)) = true
      exact ncsrMulConvolveSorted (ncsrNormalize l) (ncsrNormalize r)

/-- rfl smokes for the normal form. -/
theorem ncsrNormalize_zero_smoke : ncsrNormalize NcsrTree.zeroOp = [] := rfl
theorem ncsrNormalize_one_smoke : ncsrNormalize NcsrTree.oneOp = [([], 1)] := rfl
theorem ncsrNormalize_distribRight_smoke :
    ncsrNormalize (NcsrTree.mulOp (NcsrTree.addOp (NcsrTree.gen 0) (NcsrTree.gen 1)) (NcsrTree.gen 2))
      = ncsrNormalize (NcsrTree.addOp (NcsrTree.mulOp (NcsrTree.gen 0) (NcsrTree.gen 2))
          (NcsrTree.mulOp (NcsrTree.gen 1) (NcsrTree.gen 2))) := rfl

/-- ★ non-commutative-semiring convertibility (a multiplicative MONOID: both units, both distributivities,
    both annihilations — and deliberately NO `mulComm`). -/
inductive NoncommSemiringTreeConv : NcsrTree → NcsrTree → Prop where
  | addAssoc (a b c : NcsrTree) :
      NoncommSemiringTreeConv (NcsrTree.addOp (NcsrTree.addOp a b) c) (NcsrTree.addOp a (NcsrTree.addOp b c))
  | addComm (a b : NcsrTree) : NoncommSemiringTreeConv (NcsrTree.addOp a b) (NcsrTree.addOp b a)
  | addZero (a : NcsrTree) : NoncommSemiringTreeConv (NcsrTree.addOp a NcsrTree.zeroOp) a
  | mulAssoc (a b c : NcsrTree) :
      NoncommSemiringTreeConv (NcsrTree.mulOp (NcsrTree.mulOp a b) c) (NcsrTree.mulOp a (NcsrTree.mulOp b c))
  | mulOne (a : NcsrTree) : NoncommSemiringTreeConv (NcsrTree.mulOp a NcsrTree.oneOp) a
  | mulOneLeft (a : NcsrTree) : NoncommSemiringTreeConv (NcsrTree.mulOp NcsrTree.oneOp a) a
  | distribLeft (a b c : NcsrTree) :
      NoncommSemiringTreeConv (NcsrTree.mulOp a (NcsrTree.addOp b c))
        (NcsrTree.addOp (NcsrTree.mulOp a b) (NcsrTree.mulOp a c))
  | distribRight (a b c : NcsrTree) :
      NoncommSemiringTreeConv (NcsrTree.mulOp (NcsrTree.addOp a b) c)
        (NcsrTree.addOp (NcsrTree.mulOp a c) (NcsrTree.mulOp b c))
  | annihilRight (a : NcsrTree) : NoncommSemiringTreeConv (NcsrTree.mulOp a NcsrTree.zeroOp) NcsrTree.zeroOp
  | annihilLeft (a : NcsrTree) : NoncommSemiringTreeConv (NcsrTree.mulOp NcsrTree.zeroOp a) NcsrTree.zeroOp
  | addCongr {leftOld leftNew rightOld rightNew : NcsrTree} :
      NoncommSemiringTreeConv leftOld leftNew → NoncommSemiringTreeConv rightOld rightNew →
      NoncommSemiringTreeConv (NcsrTree.addOp leftOld rightOld) (NcsrTree.addOp leftNew rightNew)
  | mulCongr {leftOld leftNew rightOld rightNew : NcsrTree} :
      NoncommSemiringTreeConv leftOld leftNew → NoncommSemiringTreeConv rightOld rightNew →
      NoncommSemiringTreeConv (NcsrTree.mulOp leftOld rightOld) (NcsrTree.mulOp leftNew rightNew)
  | refl (t : NcsrTree) : NoncommSemiringTreeConv t t
  | symm {s t : NcsrTree} : NoncommSemiringTreeConv s t → NoncommSemiringTreeConv t s
  | trans {s t u : NcsrTree} : NoncommSemiringTreeConv s t → NoncommSemiringTreeConv t u → NoncommSemiringTreeConv s u

/-- ★ soundness: convertible trees have equal normal form. -/
theorem ncsrNormalize_respects {s t : NcsrTree} (conv : NoncommSemiringTreeConv s t) :
    ncsrNormalize s = ncsrNormalize t := by
  induction conv with
  | addAssoc a b c => exact ncsrMergeAddAssoc (ncsrNormalize a) (ncsrNormalize b) (ncsrNormalize c)
  | addComm a b =>
      exact ncsrMergeAddComm (ncsrNormalize a) (ncsrNormalize b)
        (ncsrNormalizeSorted a) (ncsrNormalizeSorted b)
  | addZero a =>
      show ncsrMergeAdd (ncsrNormalize a) [] = ncsrNormalize a
      exact ncsrMergeAddNilRight (ncsrNormalize a) (ncsrNormalizeSorted a)
  | mulAssoc a b c => exact ncsrMulConvolveAssoc (ncsrNormalize a) (ncsrNormalize b) (ncsrNormalize c)
  | mulOne a =>
      show ncsrMulConvolve (ncsrNormalize a) [([], 1)] = ncsrNormalize a
      exact ncsrMulConvolveUnitRight (ncsrNormalize a) (ncsrNormalizeSorted a)
  | mulOneLeft a =>
      show ncsrMulConvolve [([], 1)] (ncsrNormalize a) = ncsrNormalize a
      exact ncsrMulConvolveUnitLeft (ncsrNormalize a) (ncsrNormalizeSorted a)
  | distribLeft a b c =>
      exact ncsrMulConvolve_leftDistrib (ncsrNormalize a) (ncsrNormalize b) (ncsrNormalize c)
  | distribRight a b c =>
      exact ncsrMulConvolve_rightDistrib (ncsrNormalize a) (ncsrNormalize b) (ncsrNormalize c)
  | annihilRight a =>
      show ncsrMulConvolve (ncsrNormalize a) [] = []
      exact ncsrMulConvolveAnnihil (ncsrNormalize a)
  | annihilLeft a =>
      show ncsrMulConvolve [] (ncsrNormalize a) = []
      rfl
  | addCongr _ _ ihl ihr =>
      show ncsrMergeAdd (ncsrNormalize _) (ncsrNormalize _) = ncsrMergeAdd (ncsrNormalize _) (ncsrNormalize _)
      rw [ihl, ihr]
  | mulCongr _ _ ihl ihr =>
      show ncsrMulConvolve (ncsrNormalize _) (ncsrNormalize _) = ncsrMulConvolve (ncsrNormalize _) (ncsrNormalize _)
      rw [ihl, ihr]
  | refl t => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2


-- derived Conv helpers (additive only — the multiplicative unit/annihil/distrib on each side are primitives)
theorem ncsrConvAddZeroLeft (a : NcsrTree) : NoncommSemiringTreeConv (NcsrTree.addOp NcsrTree.zeroOp a) a :=
  (NoncommSemiringTreeConv.addComm NcsrTree.zeroOp a).trans (NoncommSemiringTreeConv.addZero a)
theorem ncsrConvAddSwap13 (x y z : NcsrTree) :
    NoncommSemiringTreeConv (NcsrTree.addOp x (NcsrTree.addOp y z)) (NcsrTree.addOp y (NcsrTree.addOp x z)) :=
  (NoncommSemiringTreeConv.symm (NoncommSemiringTreeConv.addAssoc x y z)).trans
    ((NoncommSemiringTreeConv.addCongr (NoncommSemiringTreeConv.addComm x y) (NoncommSemiringTreeConv.refl z)).trans
      (NoncommSemiringTreeConv.addAssoc y x z))

-- coefficient-many copies of a monomial tree
def ncsrScaleTree (mono : NcsrTree) : Nat → NcsrTree
  | 0 => NcsrTree.zeroOp
  | Nat.succ k => NcsrTree.addOp mono (ncsrScaleTree mono k)
theorem ncsrScaleTreeCongr {mono1 mono2 : NcsrTree} (h : NoncommSemiringTreeConv mono1 mono2) (n : Nat) :
    NoncommSemiringTreeConv (ncsrScaleTree mono1 n) (ncsrScaleTree mono2 n) := by
  induction n with
  | zero => exact NoncommSemiringTreeConv.refl NcsrTree.zeroOp
  | succ k ih => exact NoncommSemiringTreeConv.addCongr h ih
theorem ncsrScaleAdd (mono : NcsrTree) (a b : Nat) :
    NoncommSemiringTreeConv (ncsrScaleTree mono (a + b))
      (NcsrTree.addOp (ncsrScaleTree mono a) (ncsrScaleTree mono b)) := by
  induction b with
  | zero => exact (NoncommSemiringTreeConv.addZero (ncsrScaleTree mono a)).symm
  | succ k ih =>
      exact (NoncommSemiringTreeConv.addCongr (NoncommSemiringTreeConv.refl mono) ih).trans
        (ncsrConvAddSwap13 mono (ncsrScaleTree mono a) (ncsrScaleTree mono k))
theorem ncsrScaleTreeMulLeft (p q : NcsrTree) (c : Nat) :
    NoncommSemiringTreeConv (ncsrScaleTree (NcsrTree.mulOp p q) c) (NcsrTree.mulOp (ncsrScaleTree p c) q) := by
  induction c with
  | zero => exact (NoncommSemiringTreeConv.annihilLeft q).symm
  | succ k ih =>
      exact (NoncommSemiringTreeConv.addCongr (NoncommSemiringTreeConv.refl (NcsrTree.mulOp p q)) ih).trans
        (NoncommSemiringTreeConv.distribRight p (ncsrScaleTree p k) q).symm
theorem ncsrScaleTreeMulRight (p q : NcsrTree) (d : Nat) :
    NoncommSemiringTreeConv (ncsrScaleTree (NcsrTree.mulOp p q) d) (NcsrTree.mulOp p (ncsrScaleTree q d)) := by
  induction d with
  | zero => exact (NoncommSemiringTreeConv.annihilRight p).symm
  | succ k ih =>
      exact (NoncommSemiringTreeConv.addCongr (NoncommSemiringTreeConv.refl (NcsrTree.mulOp p q)) ih).trans
        (NoncommSemiringTreeConv.distribLeft p q (ncsrScaleTree q k)).symm
theorem ncsrScaleTreeMulCoeff (X : NcsrTree) (c d : Nat) :
    NoncommSemiringTreeConv (ncsrScaleTree X (c * d)) (ncsrScaleTree (ncsrScaleTree X d) c) := by
  induction c with
  | zero => rw [Nat.zero_mul d]; exact NoncommSemiringTreeConv.refl NcsrTree.zeroOp
  | succ k ih =>
      rw [Nat.succ_mul k d]
      exact (ncsrScaleAdd X (k * d) d).trans
        ((NoncommSemiringTreeConv.addCongr ih (NoncommSemiringTreeConv.refl (ncsrScaleTree X d))).trans
          (NoncommSemiringTreeConv.addComm (ncsrScaleTree (ncsrScaleTree X d) k) (ncsrScaleTree X d)))

-- word → tree, and its reification via CONCATENATION (structural: mulAssoc + left-unit, no commutativity)
def ncsrMonoToTree : List Nat → NcsrTree
  | [] => NcsrTree.oneOp
  | c :: rest => NcsrTree.mulOp (NcsrTree.gen c) (ncsrMonoToTree rest)
theorem ncsrMonoToTreeWordCat : (m n : List Nat) →
    NoncommSemiringTreeConv (ncsrMonoToTree (ncsrWordCat m n))
      (NcsrTree.mulOp (ncsrMonoToTree m) (ncsrMonoToTree n))
  | [], n => (NoncommSemiringTreeConv.mulOneLeft (ncsrMonoToTree n)).symm
  | a :: as, n => by
      show NoncommSemiringTreeConv (NcsrTree.mulOp (NcsrTree.gen a) (ncsrMonoToTree (ncsrWordCat as n)))
        (NcsrTree.mulOp (NcsrTree.mulOp (NcsrTree.gen a) (ncsrMonoToTree as)) (ncsrMonoToTree n))
      exact (NoncommSemiringTreeConv.mulCongr (NoncommSemiringTreeConv.refl (NcsrTree.gen a))
          (ncsrMonoToTreeWordCat as n)).trans
        (NoncommSemiringTreeConv.symm
          (NoncommSemiringTreeConv.mulAssoc (NcsrTree.gen a) (ncsrMonoToTree as) (ncsrMonoToTree n)))

-- term → tree, and the term-product reification
def ncsrTermToTree (mono : List Nat) (coeff : Nat) : NcsrTree := ncsrScaleTree (ncsrMonoToTree mono) coeff
theorem ncsrTermToTreeMul (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) :
    NoncommSemiringTreeConv (ncsrTermToTree (ncsrWordCat m n) (c * d))
      (NcsrTree.mulOp (ncsrTermToTree m c) (ncsrTermToTree n d)) := by
  show NoncommSemiringTreeConv (ncsrScaleTree (ncsrMonoToTree (ncsrWordCat m n)) (c * d))
    (NcsrTree.mulOp (ncsrScaleTree (ncsrMonoToTree m) c) (ncsrScaleTree (ncsrMonoToTree n) d))
  exact (ncsrScaleTreeCongr (ncsrMonoToTreeWordCat m n) (c * d)).trans
    ((ncsrScaleTreeMulCoeff (NcsrTree.mulOp (ncsrMonoToTree m) (ncsrMonoToTree n)) c d).trans
      ((ncsrScaleTreeCongr
          (ncsrScaleTreeMulRight (ncsrMonoToTree m) (ncsrMonoToTree n) d) c).trans
        (ncsrScaleTreeMulLeft (ncsrMonoToTree m) (ncsrScaleTree (ncsrMonoToTree n) d) c)))


/-- rebuild a canonical tree from a normal form. -/
def ncsrCombOfNF : NcsrNF → NcsrTree
  | [] => NcsrTree.zeroOp
  | (m, c) :: rest => NcsrTree.addOp (ncsrTermToTree m c) (ncsrCombOfNF rest)
theorem ncsrCombOfNFCons (m : List Nat) (c : Nat) (rest : NcsrNF) :
    ncsrCombOfNF ((m, c) :: rest) = NcsrTree.addOp (ncsrTermToTree m c) (ncsrCombOfNF rest) := rfl

theorem ncsrCombInsertTerm (m : List Nat) (c : Nat) (A : NcsrNF) :
    NoncommSemiringTreeConv (ncsrCombOfNF (ncsrInsertTerm (m, c) A))
      (NcsrTree.addOp (ncsrTermToTree m c) (ncsrCombOfNF A)) := by
  induction A with
  | nil => exact NoncommSemiringTreeConv.refl _
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : ncsrCompare m p with
      | eq =>
          have hmeqp : m = p := ncsrCompareEq_of m p hmp
          rw [ncsrInsertTermEqE m c p e rest hmp, ncsrCombOfNFCons p (e + c) rest,
              ncsrCombOfNFCons p e rest, hmeqp]
          exact (NoncommSemiringTreeConv.addCongr (ncsrScaleAdd (ncsrMonoToTree p) e c)
              (NoncommSemiringTreeConv.refl (ncsrCombOfNF rest))).trans
            ((NoncommSemiringTreeConv.addAssoc (ncsrTermToTree p e) (ncsrTermToTree p c) (ncsrCombOfNF rest)).trans
              (ncsrConvAddSwap13 (ncsrTermToTree p e) (ncsrTermToTree p c) (ncsrCombOfNF rest)))
      | lt =>
          rw [ncsrInsertTermLtE m c p e rest hmp, ncsrCombOfNFCons m c ((p, e) :: rest)]
          exact NoncommSemiringTreeConv.refl _
      | gt =>
          rw [ncsrInsertTermGtE m c p e rest hmp, ncsrCombOfNFCons p e (ncsrInsertTerm (m, c) rest),
              ncsrCombOfNFCons p e rest]
          exact (NoncommSemiringTreeConv.addCongr (NoncommSemiringTreeConv.refl (ncsrTermToTree p e)) ih).trans
            (ncsrConvAddSwap13 (ncsrTermToTree p e) (ncsrTermToTree m c) (ncsrCombOfNF rest))

theorem ncsrCombMergeAdd (A B : NcsrNF) :
    NoncommSemiringTreeConv (ncsrCombOfNF (ncsrMergeAdd A B))
      (NcsrTree.addOp (ncsrCombOfNF A) (ncsrCombOfNF B)) := by
  induction A with
  | nil => exact (ncsrConvAddZeroLeft (ncsrCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show NoncommSemiringTreeConv (ncsrCombOfNF (ncsrInsertTerm (m, c) (ncsrMergeAdd A' B)))
        (NcsrTree.addOp (NcsrTree.addOp (ncsrTermToTree m c) (ncsrCombOfNF A')) (ncsrCombOfNF B))
      exact ((ncsrCombInsertTerm m c (ncsrMergeAdd A' B)).trans
          (NoncommSemiringTreeConv.addCongr (NoncommSemiringTreeConv.refl (ncsrTermToTree m c)) ih)).trans
        (NoncommSemiringTreeConv.symm
          (NoncommSemiringTreeConv.addAssoc (ncsrTermToTree m c) (ncsrCombOfNF A') (ncsrCombOfNF B)))

theorem ncsrCombTermMul (m : List Nat) (c : Nat) (B : NcsrNF) :
    NoncommSemiringTreeConv (ncsrCombOfNF (ncsrTermMul m c B))
      (NcsrTree.mulOp (ncsrTermToTree m c) (ncsrCombOfNF B)) := by
  induction B with
  | nil => exact (NoncommSemiringTreeConv.annihilRight (ncsrTermToTree m c)).symm
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show NoncommSemiringTreeConv (ncsrCombOfNF (ncsrInsertTerm (ncsrWordCat m n, c * d) (ncsrTermMul m c B')))
        (NcsrTree.mulOp (ncsrTermToTree m c) (NcsrTree.addOp (ncsrTermToTree n d) (ncsrCombOfNF B')))
      exact ((ncsrCombInsertTerm (ncsrWordCat m n) (c * d) (ncsrTermMul m c B')).trans
          (NoncommSemiringTreeConv.addCongr (ncsrTermToTreeMul m c n d) ih)).trans
        (NoncommSemiringTreeConv.symm
          (NoncommSemiringTreeConv.distribLeft (ncsrTermToTree m c) (ncsrTermToTree n d) (ncsrCombOfNF B')))

theorem ncsrCombMulConvolve (A B : NcsrNF) :
    NoncommSemiringTreeConv (ncsrCombOfNF (ncsrMulConvolve A B))
      (NcsrTree.mulOp (ncsrCombOfNF A) (ncsrCombOfNF B)) := by
  induction A with
  | nil => exact (NoncommSemiringTreeConv.annihilLeft (ncsrCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show NoncommSemiringTreeConv (ncsrCombOfNF (ncsrMergeAdd (ncsrTermMul m c B) (ncsrMulConvolve A' B)))
        (NcsrTree.mulOp (NcsrTree.addOp (ncsrTermToTree m c) (ncsrCombOfNF A')) (ncsrCombOfNF B))
      exact ((ncsrCombMergeAdd (ncsrTermMul m c B) (ncsrMulConvolve A' B)).trans
          (NoncommSemiringTreeConv.addCongr (ncsrCombTermMul m c B) ih)).trans
        (NoncommSemiringTreeConv.symm
          (NoncommSemiringTreeConv.distribRight (ncsrTermToTree m c) (ncsrCombOfNF A') (ncsrCombOfNF B)))

/-- ★ every tree is convertible to the rebuild of its own normal form. -/
theorem ncsrTreeReifies (t : NcsrTree) : NoncommSemiringTreeConv t (ncsrCombOfNF (ncsrNormalize t)) := by
  induction t with
  | gen c =>
      show NoncommSemiringTreeConv (NcsrTree.gen c)
        (NcsrTree.addOp (ncsrTermToTree [c] 1) NcsrTree.zeroOp)
      have hgen : NoncommSemiringTreeConv (NcsrTree.gen c) (ncsrTermToTree [c] 1) :=
        (NoncommSemiringTreeConv.symm (NoncommSemiringTreeConv.mulOne (NcsrTree.gen c))).trans
          (NoncommSemiringTreeConv.symm
            (NoncommSemiringTreeConv.addZero (NcsrTree.mulOp (NcsrTree.gen c) NcsrTree.oneOp)))
      exact hgen.trans (NoncommSemiringTreeConv.symm (NoncommSemiringTreeConv.addZero (ncsrTermToTree [c] 1)))
  | zeroOp => exact NoncommSemiringTreeConv.refl NcsrTree.zeroOp
  | oneOp =>
      show NoncommSemiringTreeConv NcsrTree.oneOp (NcsrTree.addOp (ncsrTermToTree [] 1) NcsrTree.zeroOp)
      exact (NoncommSemiringTreeConv.symm (NoncommSemiringTreeConv.addZero NcsrTree.oneOp)).trans
        (NoncommSemiringTreeConv.symm (NoncommSemiringTreeConv.addZero (ncsrTermToTree [] 1)))
  | addOp l r ihl ihr =>
      show NoncommSemiringTreeConv (NcsrTree.addOp l r)
        (ncsrCombOfNF (ncsrMergeAdd (ncsrNormalize l) (ncsrNormalize r)))
      exact (NoncommSemiringTreeConv.addCongr ihl ihr).trans
        (NoncommSemiringTreeConv.symm (ncsrCombMergeAdd (ncsrNormalize l) (ncsrNormalize r)))
  | mulOp l r ihl ihr =>
      show NoncommSemiringTreeConv (NcsrTree.mulOp l r)
        (ncsrCombOfNF (ncsrMulConvolve (ncsrNormalize l) (ncsrNormalize r)))
      exact (NoncommSemiringTreeConv.mulCongr ihl ihr).trans
        (NoncommSemiringTreeConv.symm (ncsrCombMulConvolve (ncsrNormalize l) (ncsrNormalize r)))

/-- ★ completeness: equal normal forms give convertible trees. -/
theorem ncsrConv_of_normalizeEq {s t : NcsrTree} (h : ncsrNormalize s = ncsrNormalize t) :
    NoncommSemiringTreeConv s t := by
  have hcomb : ncsrCombOfNF (ncsrNormalize s) = ncsrCombOfNF (ncsrNormalize t) := congrArg ncsrCombOfNF h
  exact (ncsrTreeReifies s).trans (hcomb ▸ (ncsrTreeReifies t).symm)

-- structural NF equality
def ncsrNFEq : NcsrNF → NcsrNF → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | (m1, c1) :: r1, (m2, c2) :: r2 => (ncsrWordEq m1 m2 && Nat.beq c1 c2) && ncsrNFEq r1 r2
theorem ncsrNFEqRefl (A : NcsrNF) : ncsrNFEq A A = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show ((ncsrWordEq m m && Nat.beq c c) && ncsrNFEq rest rest) = true
      exact ncsrAndIntro _ _ (ncsrAndIntro _ _ (ncsrWordEqRefl m) (ncsrNatBeqRefl c)) ih
theorem ncsrNFEq_eq (A B : NcsrNF) : ncsrNFEq A B = true → A = B := by
  induction A generalizing B with
  | nil =>
      cases B with
      | nil => intro _; rfl
      | cons head rest => intro h; exact Bool.noConfusion h
  | cons head A' ih =>
      obtain ⟨m1, c1⟩ := head
      cases B with
      | nil => intro h; exact Bool.noConfusion h
      | cons head2 B' =>
          obtain ⟨m2, c2⟩ := head2
          intro h
          have hpair : (ncsrWordEq m1 m2 && Nat.beq c1 c2) = true := ncsrAndTrueLeft _ _ h
          have hrest : ncsrNFEq A' B' = true := ncsrAndTrueRight _ _ h
          have hm : m1 = m2 := ncsrWordEq_eq m1 m2 (ncsrAndTrueLeft _ _ hpair)
          have hc : c1 = c2 := ncsrNatEqOfBeq c1 c2 (ncsrAndTrueRight _ _ hpair)
          rw [hm, hc, ih B' hrest]

/-- ★★ the decision procedure. -/
def ncsrDecideConv (s t : NcsrTree) : Bool := ncsrNFEq (ncsrNormalize s) (ncsrNormalize t)

/-- ★★ THE DECISION: convertibility ⟺ equal non-commutative polynomial normal form. -/
theorem noncommSemiringTreeConv_iff_normalForm (s t : NcsrTree) :
    NoncommSemiringTreeConv s t ↔ ncsrDecideConv s t = true := by
  constructor
  · intro conv
    show ncsrNFEq (ncsrNormalize s) (ncsrNormalize t) = true
    rw [ncsrNormalize_respects conv]; exact ncsrNFEqRefl (ncsrNormalize t)
  · intro hdec
    exact ncsrConv_of_normalizeEq (ncsrNFEq_eq (ncsrNormalize s) (ncsrNormalize t) hdec)

/-- ★ decidability, via the biconditional (no `propext`). -/
instance ncsrDecidableConv (s t : NcsrTree) : Decidable (NoncommSemiringTreeConv s t) :=
  if h : ncsrDecideConv s t = true then
    isTrue ((noncommSemiringTreeConv_iff_normalForm s t).mpr h)
  else
    isFalse (fun conv => h ((noncommSemiringTreeConv_iff_normalForm s t).mp conv))

/-- ★★ the walking free non-commutative semiring on ℕ is DECIDED. -/
def fxWalkingSemiring_hasNormalFormDecision : Bool := true

-- genuineness smokes
#eval ncsrDecideConv
  (NcsrTree.mulOp (NcsrTree.mulOp (NcsrTree.gen 0) (NcsrTree.gen 1)) (NcsrTree.gen 2))
  (NcsrTree.mulOp (NcsrTree.gen 0) (NcsrTree.mulOp (NcsrTree.gen 1) (NcsrTree.gen 2)))
#eval ncsrDecideConv (NcsrTree.mulOp (NcsrTree.gen 0) (NcsrTree.addOp (NcsrTree.gen 1) (NcsrTree.gen 2)))
  (NcsrTree.addOp (NcsrTree.mulOp (NcsrTree.gen 0) (NcsrTree.gen 1))
    (NcsrTree.mulOp (NcsrTree.gen 0) (NcsrTree.gen 2)))
#eval ncsrDecideConv (NcsrTree.mulOp (NcsrTree.addOp (NcsrTree.gen 0) (NcsrTree.gen 1)) (NcsrTree.gen 2))
  (NcsrTree.addOp (NcsrTree.mulOp (NcsrTree.gen 0) (NcsrTree.gen 2))
    (NcsrTree.mulOp (NcsrTree.gen 1) (NcsrTree.gen 2)))
#eval ncsrDecideConv (NcsrTree.mulOp (NcsrTree.gen 0) (NcsrTree.gen 1))
  (NcsrTree.mulOp (NcsrTree.gen 1) (NcsrTree.gen 0))
#eval ncsrDecideConv (NcsrTree.mulOp (NcsrTree.gen 0) NcsrTree.zeroOp) NcsrTree.zeroOp
#eval ncsrDecideConv (NcsrTree.mulOp NcsrTree.oneOp (NcsrTree.gen 0)) (NcsrTree.gen 0)
#eval ncsrDecideConv (NcsrTree.addOp (NcsrTree.gen 0) (NcsrTree.gen 0)) (NcsrTree.gen 0)

end FX1Poly.Polygraph
