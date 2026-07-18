import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeMonoid.MultisetCommutativeMonoidSeed
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # WalkingCommutativeSemiring/CommutativeSemiringSeed — the walking free COMMUTATIVE SEMIRING on ℕ: the polynomial ℕ[X] decision

The multiplicative successor of the multiset commutative-monoid rung
(`MultisetCommutativeMonoidSeed`, whose free commutative monoid on `ℕ` is the finite MULTISETS of colours,
decided by sorted-list normal form).  Adding a second binary operation with unit and both distributivities
turns that walker into the free **commutative semiring** on the colour set `ℕ` — which is exactly the semiring
of polynomials `ℕ[X_c : c ∈ ℕ]` with natural-number coefficients in commuting variables.  A tree's class is
determined by its polynomial: the finite formal `ℕ`-linear combination of monomials, where a monomial is a
finite multiset of variables (an element of the free commutative monoid on `ℕ`).  Because that polynomial is a
COMPLETE invariant with a canonical sorted representative, the word problem is DECIDED by plain structural
equality of normal forms.

## ★ Why this walker is FULLY DECIDED — polynomials as the complete invariant

The normal form `CsrNF := List (List Nat × Nat)` is a list of `(monomial, coefficient)` pairs, sorted strictly
by a total monomial order `csrMonoBle` (length-first, then lexicographic via the imported structural `natBle`),
every coefficient `> 0`, no duplicate monomials.  A monomial reuses the imported sorted-multiset kit
(`insertSorted` / `insertMany`, so a monomial is a sorted `List Nat` of variable-occurrences).  The two
operations are `csrMergeAdd` (sorted merge, coefficients added on equal monomials) and `csrMulConvolve`
(the Cauchy convolution: monomial product = multiset union via `insertMany`, coefficient product = `Nat.mul`).
`csrNormalize` sends `gen c ↦ [([c],1)]`, `zeroOp ↦ []`, `oneOp ↦ [([],1)]`, `addOp ↦ csrMergeAdd`,
`mulOp ↦ csrMulConvolve`.

This file ships, all zero-axiom:

* **the crux commutation** `csrInsertTermComm` — two term-insertions commute (permutation-invariance of the
  merge; the coefficient-aware analogue of the multiset seed's `insertSortedComm`);
* **the additive commutative monoid** — `csrMergeAdd` associative / commutative with `[]` a unit
  (`csrMergeAddAssoc` / `csrMergeAddComm` / `csrMergeAddNilRight`), on the strict-sortedness invariant
  `csrNFSorted`;
* **the multiplicative structure** — `csrMulConvolve` ANNIHILATION (`csrMulConvolveAnnihil`), LEFT and RIGHT
  DISTRIBUTIVITY (`csrMulConvolve_leftDistrib` / `csrMulConvolve_rightDistrib`), ASSOCIATIVITY
  (`csrMulConvolveAssoc`, via the `csrTermMul_compose`/`csrTermMul_convolve` chain — reducing to the free
  monomial-monoid associativity `csrMonoMulAssoc` and a hand-proved clean `csrNatMulAssoc`), COMMUTATIVITY
  (`csrMulConvolveComm`, via the sorted-monomial invariant `csrNFMonoSorted` and `csrMonoMulComm`), and the
  UNIT (`csrMulConvolveUnit`);
* **soundness** — convertible trees have equal normal form (`csrNormalize_respects`): every commutative-semiring
  law is an equation between normal forms discharged by the algebra above;
* **completeness** — equal normal forms give convertible trees (`csrConv_of_normalizeEq`), via the rebuild
  `csrCombOfNF` and the reification `csrTreeReifies` (every tree is convertible to the rebuild of its own normal
  form), whose engine is the tree-level `csrCombInsertTerm` / `csrCombMergeAdd` / `csrCombTermMul` /
  `csrCombMulConvolve` plus the scale-tree algebra (`csrScaleTree`, coefficient-many copies) and the monomial
  reification (`csrMonoToTreeMonoMul`);
* **THE DECISION** — the biconditional `semiringTreeConv_iff_normalForm` (`s ≈ t ↔ csrDecideConv s t = true`,
  where `csrDecideConv s t := csrNFEq (csrNormalize s) (csrNormalize t)`), plus a genuine `Decidable` instance
  (`csrDecidableConv`, via `Iff.mp`/`Iff.mpr`, no `propext`), and `#eval` groundings pinning the right bools.

Note on the coefficient arithmetic: the standard-library `Nat.mul_assoc` and `Nat.add_mul` LEAK `propext`, so
this file uses the hand-proved clean structural replacements `csrNatMulAssoc` / `csrNatAddMul`, built from the
clean primitives `Nat.mul_comm` / `Nat.mul_add` / `Nat.mul_succ`.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`
— the ordering is the imported structural `natBle`, no `Nat.le`/`Nat.ble` lemma and no `List.append` (`++`)
appears anywhere, and coefficient arithmetic uses only `Nat.add_comm`/`Nat.add_assoc`/`Nat.add_zero` and the
clean multiplication kit. -/

namespace FX1Poly.Polygraph

def csrLen : List Nat → Nat
  | [] => 0
  | _ :: tail => Nat.succ (csrLen tail)
def csrLexBle : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      match natBle a b with
      | false => false
      | true => match natBle b a with
                | false => true
                | true => csrLexBle as bs
def csrMonoBle (m n : List Nat) : Bool :=
  match natBle (csrLen m) (csrLen n) with
  | false => false
  | true => match natBle (csrLen n) (csrLen m) with
            | false => true
            | true => csrLexBle m n
def csrNatListEq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => Nat.beq a b && csrNatListEq as bs
theorem csrMonoBleFF (m n : List Nat) (h : natBle (csrLen m) (csrLen n) = false) :
    csrMonoBle m n = false := by
  show (match natBle (csrLen m) (csrLen n) with
        | false => false
        | true => match natBle (csrLen n) (csrLen m) with
                  | false => true
                  | true => csrLexBle m n) = false
  rw [h]
theorem csrMonoBleTF (m n : List Nat) (h1 : natBle (csrLen m) (csrLen n) = true)
    (h2 : natBle (csrLen n) (csrLen m) = false) : csrMonoBle m n = true := by
  show (match natBle (csrLen m) (csrLen n) with
        | false => false
        | true => match natBle (csrLen n) (csrLen m) with
                  | false => true
                  | true => csrLexBle m n) = true
  rw [h1, h2]
theorem csrMonoBleTT (m n : List Nat) (h1 : natBle (csrLen m) (csrLen n) = true)
    (h2 : natBle (csrLen n) (csrLen m) = true) : csrMonoBle m n = csrLexBle m n := by
  show (match natBle (csrLen m) (csrLen n) with
        | false => false
        | true => match natBle (csrLen n) (csrLen m) with
                  | false => true
                  | true => csrLexBle m n) = csrLexBle m n
  rw [h1, h2]
theorem csrLexConsTF (a b : Nat) (as bs : List Nat) (h1 : natBle a b = true) (h2 : natBle b a = false) :
    csrLexBle (a :: as) (b :: bs) = true := by
  show (match natBle a b with
        | false => false
        | true => match natBle b a with
                  | false => true
                  | true => csrLexBle as bs) = true
  rw [h1, h2]
theorem csrLexConsTT (a b : Nat) (as bs : List Nat) (h1 : natBle a b = true) (h2 : natBle b a = true) :
    csrLexBle (a :: as) (b :: bs) = csrLexBle as bs := by
  show (match natBle a b with
        | false => false
        | true => match natBle b a with
                  | false => true
                  | true => csrLexBle as bs) = csrLexBle as bs
  rw [h1, h2]
theorem csrLexConsFF (a b : Nat) (as bs : List Nat) (h : natBle a b = false) :
    csrLexBle (a :: as) (b :: bs) = false := by
  show (match natBle a b with
        | false => false
        | true => match natBle b a with
                  | false => true
                  | true => csrLexBle as bs) = false
  rw [h]
theorem csrLexBleTotalEqLen : (m n : List Nat) → csrLen m = csrLen n →
    csrLexBle m n = false → csrLexBle n m = true
  | [], [], _, hfalse => Bool.noConfusion hfalse
  | [], _ :: _, hlen, _ => Nat.noConfusion hlen
  | _ :: _, [], hlen, _ => Nat.noConfusion hlen
  | a :: as, b :: bs, hlen, hfalse => by
      have hlen' : csrLen as = csrLen bs := Nat.succ.inj hlen
      cases hab : natBle a b with
      | false => exact csrLexConsTF b a bs as (natBleTotal a b hab) hab
      | true =>
          cases hba : natBle b a with
          | false => exact Bool.noConfusion ((csrLexConsTF a b as bs hab hba).symm.trans hfalse)
          | true =>
              have hastail : csrLexBle as bs = false := by
                rw [csrLexConsTT a b as bs hab hba] at hfalse; exact hfalse
              rw [csrLexConsTT b a bs as hba hab]
              exact csrLexBleTotalEqLen as bs hlen' hastail
theorem csrLexBleAntisymmEqLen : (m n : List Nat) → csrLen m = csrLen n →
    csrLexBle m n = true → csrLexBle n m = true → m = n
  | [], [], _, _, _ => rfl
  | [], _ :: _, hlen, _, _ => Nat.noConfusion hlen
  | _ :: _, [], hlen, _, _ => Nat.noConfusion hlen
  | a :: as, b :: bs, hlen, hmn, hnm => by
      have hlen' : csrLen as = csrLen bs := Nat.succ.inj hlen
      cases hab : natBle a b with
      | false => exact Bool.noConfusion ((csrLexConsFF a b as bs hab).symm.trans hmn)
      | true =>
          cases hba : natBle b a with
          | false => exact Bool.noConfusion ((csrLexConsFF b a bs as hba).symm.trans hnm)
          | true =>
              have haeqb : a = b := natBleAntisymm a b hab hba
              have hmn' : csrLexBle as bs = true := by
                rw [csrLexConsTT a b as bs hab hba] at hmn; exact hmn
              have hnm' : csrLexBle bs as = true := by
                rw [csrLexConsTT b a bs as hba hab] at hnm; exact hnm
              rw [haeqb, csrLexBleAntisymmEqLen as bs hlen' hmn' hnm']
theorem csrLexBleTransEqLen : (m n p : List Nat) → csrLen m = csrLen n → csrLen n = csrLen p →
    csrLexBle m n = true → csrLexBle n p = true → csrLexBle m p = true
  | [], [], [], _, _, _, _ => rfl
  | [], [], _ :: _, _, hlen2, _, _ => Nat.noConfusion hlen2
  | [], _ :: _, _, hlen1, _, _, _ => Nat.noConfusion hlen1
  | _ :: _, [], _, hlen1, _, _, _ => Nat.noConfusion hlen1
  | _ :: _, _ :: _, [], _, hlen2, _, _ => Nat.noConfusion hlen2
  | a :: as, b :: bs, c :: cs, hlen1, hlen2, hmn, hnp => by
      have hlen1' : csrLen as = csrLen bs := Nat.succ.inj hlen1
      have hlen2' : csrLen bs = csrLen cs := Nat.succ.inj hlen2
      cases hab : natBle a b with
      | false => exact Bool.noConfusion ((csrLexConsFF a b as bs hab).symm.trans hmn)
      | true =>
        cases hbc : natBle b c with
        | false => exact Bool.noConfusion ((csrLexConsFF b c bs cs hbc).symm.trans hnp)
        | true =>
          have hac : natBle a c = true := natBleTrans a b c hab hbc
          cases hca : natBle c a with
          | false => exact csrLexConsTF a c as cs hac hca
          | true =>
            have hba : natBle b a = true := natBleTrans b c a hbc hca
            have hcb : natBle c b = true := natBleTrans c a b hca hab
            have hmn' : csrLexBle as bs = true := by
              rw [csrLexConsTT a b as bs hab hba] at hmn; exact hmn
            have hnp' : csrLexBle bs cs = true := by
              rw [csrLexConsTT b c bs cs hbc hcb] at hnp; exact hnp
            rw [csrLexConsTT a c as cs hac hca]
            exact csrLexBleTransEqLen as bs cs hlen1' hlen2' hmn' hnp'
theorem csrMonoBleTotal (m n : List Nat) : csrMonoBle m n = false → csrMonoBle n m = true := by
  intro hfalse
  cases hmn : natBle (csrLen m) (csrLen n) with
  | false => exact csrMonoBleTF n m (natBleTotal (csrLen m) (csrLen n) hmn) hmn
  | true =>
      cases hnm : natBle (csrLen n) (csrLen m) with
      | false => exact Bool.noConfusion ((csrMonoBleTF m n hmn hnm).symm.trans hfalse)
      | true =>
          have hlex : csrLexBle m n = false := by
            rw [csrMonoBleTT m n hmn hnm] at hfalse; exact hfalse
          have hlen : csrLen m = csrLen n := natBleAntisymm _ _ hmn hnm
          rw [csrMonoBleTT n m hnm hmn]
          exact csrLexBleTotalEqLen m n hlen hlex
theorem csrMonoBleAntisymm (m n : List Nat) :
    csrMonoBle m n = true → csrMonoBle n m = true → m = n := by
  intro hmn hnm
  cases hlmn : natBle (csrLen m) (csrLen n) with
  | false => exact absurd hmn (by rw [csrMonoBleFF m n hlmn]; exact Bool.noConfusion)
  | true =>
      cases hlnm : natBle (csrLen n) (csrLen m) with
      | false => exact absurd hnm (by rw [csrMonoBleFF n m hlnm]; exact Bool.noConfusion)
      | true =>
          have hlen : csrLen m = csrLen n := natBleAntisymm _ _ hlmn hlnm
          have h1 : csrLexBle m n = true := by rw [csrMonoBleTT m n hlmn hlnm] at hmn; exact hmn
          have h2 : csrLexBle n m = true := by rw [csrMonoBleTT n m hlnm hlmn] at hnm; exact hnm
          exact csrLexBleAntisymmEqLen m n hlen h1 h2
theorem csrMonoBleTrans (m n p : List Nat) :
    csrMonoBle m n = true → csrMonoBle n p = true → csrMonoBle m p = true := by
  intro hmn hnp
  cases hlmn : natBle (csrLen m) (csrLen n) with
  | false => exact absurd hmn (by rw [csrMonoBleFF m n hlmn]; exact Bool.noConfusion)
  | true =>
      cases hlnp : natBle (csrLen n) (csrLen p) with
      | false => exact absurd hnp (by rw [csrMonoBleFF n p hlnp]; exact Bool.noConfusion)
      | true =>
          have hlmp : natBle (csrLen m) (csrLen p) = true := natBleTrans _ _ _ hlmn hlnp
          cases hlpm : natBle (csrLen p) (csrLen m) with
          | false => exact csrMonoBleTF m p hlmp hlpm
          | true =>
              have hlpn : natBle (csrLen p) (csrLen n) = true := natBleTrans _ _ _ hlpm hlmn
              have hlnm : natBle (csrLen n) (csrLen m) = true := natBleTrans _ _ _ hlnp hlpm
              have hlen1 : csrLen m = csrLen n := natBleAntisymm _ _ hlmn hlnm
              have hlen2 : csrLen n = csrLen p := natBleAntisymm _ _ hlnp hlpn
              have h1 : csrLexBle m n = true := by rw [csrMonoBleTT m n hlmn hlnm] at hmn; exact hmn
              have h2 : csrLexBle n p = true := by rw [csrMonoBleTT n p hlnp hlpn] at hnp; exact hnp
              rw [csrMonoBleTT m p hlmp hlpm]
              exact csrLexBleTransEqLen m n p hlen1 hlen2 h1 h2
theorem csrNatBeqRefl : (a : Nat) → Nat.beq a a = true
  | 0 => rfl
  | Nat.succ k => csrNatBeqRefl k
theorem csrNatBeqSymm : (a b : Nat) → Nat.beq a b = Nat.beq b a
  | 0, 0 => rfl
  | 0, Nat.succ _ => rfl
  | Nat.succ _, 0 => rfl
  | Nat.succ x, Nat.succ y => csrNatBeqSymm x y
theorem csrNatEqOfBeq : (a b : Nat) → Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, Nat.succ _, h => Bool.noConfusion h
  | Nat.succ _, 0, h => Bool.noConfusion h
  | Nat.succ x, Nat.succ y, h => congrArg Nat.succ (csrNatEqOfBeq x y h)
theorem csrNatListEqRefl : (m : List Nat) → csrNatListEq m m = true
  | [] => rfl
  | a :: as => by
      show (Nat.beq a a && csrNatListEq as as) = true
      rw [csrNatBeqRefl a, csrNatListEqRefl as]; rfl
theorem csrNatListEqSymm : (m n : List Nat) → csrNatListEq m n = csrNatListEq n m
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
      show (Nat.beq a b && csrNatListEq as bs) = (Nat.beq b a && csrNatListEq bs as)
      rw [csrNatBeqSymm a b, csrNatListEqSymm as bs]
theorem csrNatListEq_eq : (m n : List Nat) → csrNatListEq m n = true → m = n
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | a :: as, b :: bs, h => by
      have hand : (Nat.beq a b && csrNatListEq as bs) = true := h
      cases hab : Nat.beq a b with
      | false => rw [hab] at hand; exact Bool.noConfusion hand
      | true =>
          rw [hab] at hand
          rw [csrNatEqOfBeq a b hab, csrNatListEq_eq as bs hand]
theorem csrNatListEqOfEq (m n : List Nat) (h : m = n) : csrNatListEq m n = true := by
  rw [h]; exact csrNatListEqRefl n
theorem csrNatMulAssoc : (a b c : Nat) → a * b * c = a * (b * c)
  | a, b, 0 => by rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | a, b, Nat.succ c => by
      rw [Nat.mul_succ, csrNatMulAssoc a b c, Nat.mul_succ, Nat.mul_add]
theorem csrNatAddMul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

/-- 3-way monomial comparison. -/
inductive CsrMonoOrd where
  | lt
  | eq
  | gt
def csrCompare (m n : List Nat) : CsrMonoOrd :=
  match csrNatListEq m n with
  | true => CsrMonoOrd.eq
  | false => match csrMonoBle m n with
             | true => CsrMonoOrd.lt
             | false => CsrMonoOrd.gt
theorem csrCompareEqExpand (m n : List Nat) (h : csrNatListEq m n = true) :
    csrCompare m n = CsrMonoOrd.eq := by
  show (match csrNatListEq m n with
        | true => CsrMonoOrd.eq
        | false => match csrMonoBle m n with
                   | true => CsrMonoOrd.lt
                   | false => CsrMonoOrd.gt) = CsrMonoOrd.eq
  rw [h]
theorem csrCompareLtExpand (m n : List Nat) (h1 : csrNatListEq m n = false) (h2 : csrMonoBle m n = true) :
    csrCompare m n = CsrMonoOrd.lt := by
  show (match csrNatListEq m n with
        | true => CsrMonoOrd.eq
        | false => match csrMonoBle m n with
                   | true => CsrMonoOrd.lt
                   | false => CsrMonoOrd.gt) = CsrMonoOrd.lt
  rw [h1, h2]
theorem csrCompareGtExpand (m n : List Nat) (h1 : csrNatListEq m n = false) (h2 : csrMonoBle m n = false) :
    csrCompare m n = CsrMonoOrd.gt := by
  show (match csrNatListEq m n with
        | true => CsrMonoOrd.eq
        | false => match csrMonoBle m n with
                   | true => CsrMonoOrd.lt
                   | false => CsrMonoOrd.gt) = CsrMonoOrd.gt
  rw [h1, h2]
theorem csrCompareRefl (m : List Nat) : csrCompare m m = CsrMonoOrd.eq :=
  csrCompareEqExpand m m (csrNatListEqRefl m)
theorem csrCompareOfEq (m n : List Nat) (h : m = n) : csrCompare m n = CsrMonoOrd.eq :=
  csrCompareEqExpand m n (csrNatListEqOfEq m n h)
theorem csrCompareEq_of (m n : List Nat) (h : csrCompare m n = CsrMonoOrd.eq) : m = n := by
  cases hb : csrNatListEq m n with
  | true => exact csrNatListEq_eq m n hb
  | false =>
      cases hle : csrMonoBle m n with
      | true => exact absurd h (by rw [csrCompareLtExpand m n hb hle]; exact fun hh => CsrMonoOrd.noConfusion hh)
      | false => exact absurd h (by rw [csrCompareGtExpand m n hb hle]; exact fun hh => CsrMonoOrd.noConfusion hh)
theorem csrCompareSwapLt (m n : List Nat) (h : csrCompare m n = CsrMonoOrd.lt) :
    csrCompare n m = CsrMonoOrd.gt := by
  cases hb : csrNatListEq m n with
  | true => exact absurd h (by rw [csrCompareEqExpand m n hb]; exact fun hh => CsrMonoOrd.noConfusion hh)
  | false =>
      cases hle : csrMonoBle m n with
      | false => exact absurd h (by rw [csrCompareGtExpand m n hb hle]; exact fun hh => CsrMonoOrd.noConfusion hh)
      | true =>
          have hnmEq : csrNatListEq n m = false := by rw [csrNatListEqSymm n m]; exact hb
          have hnmBle : csrMonoBle n m = false := by
            cases hnm : csrMonoBle n m with
            | false => rfl
            | true => exact absurd (csrMonoBleAntisymm m n hle hnm) (fun heq => by
                rw [csrNatListEqOfEq m n heq] at hb; exact Bool.noConfusion hb)
          exact csrCompareGtExpand n m hnmEq hnmBle
theorem csrCompareSwapGt (m n : List Nat) (h : csrCompare m n = CsrMonoOrd.gt) :
    csrCompare n m = CsrMonoOrd.lt := by
  cases hb : csrNatListEq m n with
  | true => exact absurd h (by rw [csrCompareEqExpand m n hb]; exact fun hh => CsrMonoOrd.noConfusion hh)
  | false =>
      cases hle : csrMonoBle m n with
      | true => exact absurd h (by rw [csrCompareLtExpand m n hb hle]; exact fun hh => CsrMonoOrd.noConfusion hh)
      | false =>
          have hnmEq : csrNatListEq n m = false := by rw [csrNatListEqSymm n m]; exact hb
          have hnmBle : csrMonoBle n m = true := csrMonoBleTotal m n hle
          exact csrCompareLtExpand n m hnmEq hnmBle
theorem csrCompareTransLt (m n p : List Nat)
    (h1 : csrCompare m n = CsrMonoOrd.lt) (h2 : csrCompare n p = CsrMonoOrd.lt) :
    csrCompare m p = CsrMonoOrd.lt := by
  -- extract facts
  have hmnEq : csrNatListEq m n = false := by
    cases hb : csrNatListEq m n with
    | false => rfl
    | true => exact absurd h1 (by rw [csrCompareEqExpand m n hb]; exact fun hh => CsrMonoOrd.noConfusion hh)
  have hmnBle : csrMonoBle m n = true := by
    cases hle : csrMonoBle m n with
    | true => rfl
    | false => exact absurd h1 (by rw [csrCompareGtExpand m n hmnEq hle]; exact fun hh => CsrMonoOrd.noConfusion hh)
  have hnpEq : csrNatListEq n p = false := by
    cases hb : csrNatListEq n p with
    | false => rfl
    | true => exact absurd h2 (by rw [csrCompareEqExpand n p hb]; exact fun hh => CsrMonoOrd.noConfusion hh)
  have hnpBle : csrMonoBle n p = true := by
    cases hle : csrMonoBle n p with
    | true => rfl
    | false => exact absurd h2 (by rw [csrCompareGtExpand n p hnpEq hle]; exact fun hh => CsrMonoOrd.noConfusion hh)
  have hmpBle : csrMonoBle m p = true := csrMonoBleTrans m n p hmnBle hnpBle
  have hmpEq : csrNatListEq m p = false := by
    cases hb : csrNatListEq m p with
    | false => rfl
    | true =>
        have hmeqp : m = p := csrNatListEq_eq m p hb
        -- then p ≤ n (from m ≤ n and m = p) and n ≤ p gives n = p, contradiction hnpEq
        have hpn : csrMonoBle p n = true := by rw [← hmeqp]; exact hmnBle
        have hneqp : n = p := csrMonoBleAntisymm n p hnpBle hpn
        rw [csrNatListEqOfEq n p hneqp] at hnpEq
        exact Bool.noConfusion hnpEq
  exact csrCompareLtExpand m p hmpEq hmpBle


abbrev CsrNF := List (List Nat × Nat)

def csrInsertTerm : (List Nat × Nat) → CsrNF → CsrNF
  | term, [] => [term]
  | (m, c), (p, e) :: rest =>
      match csrCompare m p with
      | CsrMonoOrd.eq => (p, e + c) :: rest
      | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
      | CsrMonoOrd.gt => (p, e) :: csrInsertTerm (m, c) rest
theorem csrInsertTermNil (m : List Nat) (c : Nat) : csrInsertTerm (m, c) [] = [(m, c)] := rfl
theorem csrInsertTermEqE (m : List Nat) (c : Nat) (p : List Nat) (e : Nat) (rest : CsrNF)
    (h : csrCompare m p = CsrMonoOrd.eq) :
    csrInsertTerm (m, c) ((p, e) :: rest) = (p, e + c) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, e + c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: csrInsertTerm (m, c) rest) = (p, e + c) :: rest
  rw [h]
theorem csrInsertTermLtE (m : List Nat) (c : Nat) (p : List Nat) (e : Nat) (rest : CsrNF)
    (h : csrCompare m p = CsrMonoOrd.lt) :
    csrInsertTerm (m, c) ((p, e) :: rest) = (m, c) :: (p, e) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, e + c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: csrInsertTerm (m, c) rest) = (m, c) :: (p, e) :: rest
  rw [h]
theorem csrInsertTermGtE (m : List Nat) (c : Nat) (p : List Nat) (e : Nat) (rest : CsrNF)
    (h : csrCompare m p = CsrMonoOrd.gt) :
    csrInsertTerm (m, c) ((p, e) :: rest) = (p, e) :: csrInsertTerm (m, c) rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, e + c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: csrInsertTerm (m, c) rest) = (p, e) :: csrInsertTerm (m, c) rest
  rw [h]
theorem csrAddRightComm (e d c : Nat) : e + d + c = e + c + d := by
  rw [Nat.add_assoc e d c, Nat.add_comm d c, ← Nat.add_assoc e c d]
theorem csrInsertTermComm (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) (P : CsrNF) :
    csrInsertTerm (m, c) (csrInsertTerm (n, d) P)
      = csrInsertTerm (n, d) (csrInsertTerm (m, c) P) := by
  induction P with
  | nil =>
      cases hmn : csrCompare m n with
      | eq =>
          have hmeqn : m = n := csrCompareEq_of m n hmn
          have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
          rw [csrInsertTermNil n d, csrInsertTermNil m c,
              csrInsertTermEqE m c n d [] hmn, csrInsertTermEqE n d m c [] hnm, hmeqn,
              Nat.add_comm d c]
      | lt =>
          have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
          rw [csrInsertTermNil n d, csrInsertTermNil m c,
              csrInsertTermLtE m c n d [] hmn, csrInsertTermGtE n d m c [] hnm, csrInsertTermNil n d]
      | gt =>
          have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn
          rw [csrInsertTermNil n d, csrInsertTermNil m c,
              csrInsertTermGtE m c n d [] hmn, csrInsertTermNil m c, csrInsertTermLtE n d m c [] hnm]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [csrInsertTermEqE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [csrInsertTermEqE m c p (e + d) rest hmp, csrInsertTermEqE m c p e rest hmp,
                  csrInsertTermEqE n d p (e + c) rest hnp, csrAddRightComm e d c]
          | lt =>
              have hpm : csrCompare p m = CsrMonoOrd.gt := csrCompareSwapLt m p hmp
              have hnm : csrCompare n m = CsrMonoOrd.gt := by rw [hnp_eq]; exact hpm
              rw [csrInsertTermLtE m c p (e + d) rest hmp, csrInsertTermLtE m c p e rest hmp,
                  csrInsertTermGtE n d m c ((p, e) :: rest) hnm, csrInsertTermEqE n d p e rest hnp]
          | gt =>
              rw [csrInsertTermGtE m c p (e + d) rest hmp, csrInsertTermGtE m c p e rest hmp,
                  csrInsertTermEqE n d p e (csrInsertTerm (m, c) rest) hnp]
      | lt =>
          rw [csrInsertTermLtE n d p e rest hnp]
          cases hmn : csrCompare m n with
          | eq =>
              have hmeqn : m = n := csrCompareEq_of m n hmn
              have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
              have hmp : csrCompare m p = CsrMonoOrd.lt := by rw [hmeqn]; exact hnp
              rw [csrInsertTermEqE m c n d ((p, e) :: rest) hmn, csrInsertTermLtE m c p e rest hmp,
                  csrInsertTermEqE n d m c ((p, e) :: rest) hnm, hmeqn, Nat.add_comm d c]
          | lt =>
              have hmp : csrCompare m p = CsrMonoOrd.lt := csrCompareTransLt m n p hmn hnp
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [csrInsertTermLtE m c n d ((p, e) :: rest) hmn, csrInsertTermLtE m c p e rest hmp,
                  csrInsertTermGtE n d m c ((p, e) :: rest) hnm, csrInsertTermLtE n d p e rest hnp]
          | gt =>
              have hmn_gt : csrCompare m n = CsrMonoOrd.gt := hmn
              rw [csrInsertTermGtE m c n d ((p, e) :: rest) hmn]
              cases hmp : csrCompare m p with
              | eq =>
                  rw [csrInsertTermEqE m c p e rest hmp,
                      csrInsertTermLtE n d p (e + c) rest hnp]
              | lt =>
                  have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn_gt
                  rw [csrInsertTermLtE m c p e rest hmp,
                      csrInsertTermLtE n d m c ((p, e) :: rest) hnm]
              | gt =>
                  rw [csrInsertTermGtE m c p e rest hmp,
                      csrInsertTermLtE n d p e (csrInsertTerm (m, c) rest) hnp]
      | gt =>
          rw [csrInsertTermGtE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [csrInsertTermEqE m c p e (csrInsertTerm (n, d) rest) hmp,
                  csrInsertTermEqE m c p e rest hmp,
                  csrInsertTermGtE n d p (e + c) rest hnp]
          | lt =>
              have hpn : csrCompare p n = CsrMonoOrd.lt := csrCompareSwapGt n p hnp
              have hmn : csrCompare m n = CsrMonoOrd.lt := csrCompareTransLt m p n hmp hpn
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [csrInsertTermLtE m c p e (csrInsertTerm (n, d) rest) hmp,
                  csrInsertTermLtE m c p e rest hmp,
                  csrInsertTermGtE n d m c ((p, e) :: rest) hnm,
                  csrInsertTermGtE n d p e rest hnp]
          | gt =>
              rw [csrInsertTermGtE m c p e (csrInsertTerm (n, d) rest) hmp,
                  csrInsertTermGtE m c p e rest hmp,
                  csrInsertTermGtE n d p e (csrInsertTerm (m, c) rest) hnp, ih]

-- boolean helpers
theorem csrAndTrueLeft (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a with | true => rfl | false => exact Bool.noConfusion h
theorem csrAndTrueRight (a b : Bool) (h : (a && b) = true) : b = true := by
  cases a with | true => exact h | false => exact Bool.noConfusion h
theorem csrAndIntro (a b : Bool) (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]; rfl

-- additive engine
def csrMergeAdd : CsrNF → CsrNF → CsrNF
  | [], b => b
  | t :: a', b => csrInsertTerm t (csrMergeAdd a' b)
theorem csrMergeAddNilLeft (b : CsrNF) : csrMergeAdd [] b = b := rfl
theorem csrMergeAddCons (t : List Nat × Nat) (a' b : CsrNF) :
    csrMergeAdd (t :: a') b = csrInsertTerm t (csrMergeAdd a' b) := rfl
theorem csrInsertTerm_mergeAdd (t : List Nat × Nat) (a b : CsrNF) :
    csrInsertTerm t (csrMergeAdd a b) = csrMergeAdd a (csrInsertTerm t b) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      obtain ⟨um, uc⟩ := u
      obtain ⟨tm, tc⟩ := t
      show csrInsertTerm (tm, tc) (csrInsertTerm (um, uc) (csrMergeAdd a' b))
        = csrMergeAdd ((um, uc) :: a') (csrInsertTerm (tm, tc) b)
      rw [csrMergeAddCons, csrInsertTermComm tm tc um uc (csrMergeAdd a' b), ih]
/-- inserting the same monomial twice collapses (coefficients add). -/
theorem csrInsertTermMergeSame (m : List Nat) (c1 c2 : Nat) (Z : CsrNF) :
    csrInsertTerm (m, c1) (csrInsertTerm (m, c2) Z) = csrInsertTerm (m, c2 + c1) Z := by
  induction Z with
  | nil =>
      rw [csrInsertTermNil m c2, csrInsertTermEqE m c1 m c2 [] (csrCompareRefl m),
          csrInsertTermNil m (c2 + c1)]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          rw [csrInsertTermEqE m c2 p e rest hmp, csrInsertTermEqE m c1 p (e + c2) rest hmp,
              csrInsertTermEqE m (c2 + c1) p e rest hmp, Nat.add_assoc e c2 c1]
      | lt =>
          rw [csrInsertTermLtE m c2 p e rest hmp, csrInsertTermEqE m c1 m c2 ((p, e) :: rest)
                (csrCompareRefl m), csrInsertTermLtE m (c2 + c1) p e rest hmp]
      | gt =>
          rw [csrInsertTermGtE m c2 p e rest hmp, csrInsertTermGtE m c1 p e
                (csrInsertTerm (m, c2) rest) hmp, csrInsertTermGtE m (c2 + c1) p e rest hmp, ih]
/-- pulling an insertion out of the left list of a merge. -/
theorem csrMergeAddInsertTermLeft (u : List Nat × Nat) (Y c : CsrNF) :
    csrMergeAdd (csrInsertTerm u Y) c = csrInsertTerm u (csrMergeAdd Y c) := by
  obtain ⟨um, uc⟩ := u
  induction Y with
  | nil => rfl
  | cons head Y' ih =>
      obtain ⟨v, ve⟩ := head
      cases huv : csrCompare um v with
      | eq =>
          have hum_eq : um = v := csrCompareEq_of um v huv
          rw [csrInsertTermEqE um uc v ve Y' huv, csrMergeAddCons,
              csrMergeAddCons (v, ve) Y' c, hum_eq,
              csrInsertTermMergeSame v uc ve (csrMergeAdd Y' c)]
      | lt =>
          rw [csrInsertTermLtE um uc v ve Y' huv, csrMergeAddCons, csrMergeAddCons (v, ve) Y' c]
      | gt =>
          rw [csrInsertTermGtE um uc v ve Y' huv, csrMergeAddCons (v, ve) (csrInsertTerm (um, uc) Y') c,
              csrMergeAddCons (v, ve) Y' c, ih,
              csrInsertTermComm v ve um uc (csrMergeAdd Y' c)]
theorem csrMergeAddAssoc (a b c : CsrNF) :
    csrMergeAdd (csrMergeAdd a b) c = csrMergeAdd a (csrMergeAdd b c) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show csrMergeAdd (csrInsertTerm u (csrMergeAdd a' b)) c
        = csrInsertTerm u (csrMergeAdd a' (csrMergeAdd b c))
      rw [csrMergeAddInsertTermLeft u (csrMergeAdd a' b) c, ih]
theorem csrMergeAddSwap (a b acc : CsrNF) :
    csrMergeAdd a (csrMergeAdd b acc) = csrMergeAdd b (csrMergeAdd a acc) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show csrInsertTerm u (csrMergeAdd a' (csrMergeAdd b acc))
        = csrMergeAdd b (csrInsertTerm u (csrMergeAdd a' acc))
      rw [ih, csrInsertTerm_mergeAdd u b (csrMergeAdd a' acc)]

-- sortedness invariant
def csrBelowHead (m : List Nat) : CsrNF → Bool
  | [] => true
  | (p, _) :: _ =>
      match csrCompare m p with
      | CsrMonoOrd.lt => true
      | CsrMonoOrd.eq => false
      | CsrMonoOrd.gt => false
def csrNFSorted : CsrNF → Bool
  | [] => true
  | (m, _) :: rest => csrBelowHead m rest && csrNFSorted rest
theorem csrBelowHeadNil (m : List Nat) : csrBelowHead m [] = true := rfl
theorem csrBelowHeadConsTrue (m p : List Nat) (e : Nat) (rest : CsrNF)
    (h : csrCompare m p = CsrMonoOrd.lt) : csrBelowHead m ((p, e) :: rest) = true := by
  show (match csrCompare m p with
        | CsrMonoOrd.lt => true
        | CsrMonoOrd.eq => false
        | CsrMonoOrd.gt => false) = true
  rw [h]
theorem csrBelowHeadConsLt (m p : List Nat) (e : Nat) (rest : CsrNF)
    (h : csrBelowHead m ((p, e) :: rest) = true) : csrCompare m p = CsrMonoOrd.lt := by
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
theorem csrNFSortedCons (m : List Nat) (c : Nat) (rest : CsrNF) :
    csrNFSorted ((m, c) :: rest) = (csrBelowHead m rest && csrNFSorted rest) := rfl
theorem csrBelowHeadInsert (q m : List Nat) (c : Nat) (B : CsrNF)
    (hq : csrCompare q m = CsrMonoOrd.lt) (hB : csrBelowHead q B = true) :
    csrBelowHead q (csrInsertTerm (m, c) B) = true := by
  cases B with
  | nil => exact csrBelowHeadConsTrue q m c [] hq
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq => rw [csrInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [csrInsertTermLtE m c p e rest hmp]; exact csrBelowHeadConsTrue q m c ((p, e) :: rest) hq
      | gt =>
          rw [csrInsertTermGtE m c p e rest hmp]
          exact csrBelowHeadConsTrue q p e (csrInsertTerm (m, c) rest) (csrBelowHeadConsLt q p e rest hB)
theorem csrInsertPreservesSorted (m : List Nat) (c : Nat) (B : CsrNF)
    (hB : csrNFSorted B = true) : csrNFSorted (csrInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hbelow : csrBelowHead p rest = true := csrAndTrueLeft _ _ hB
      have hrest : csrNFSorted rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq => rw [csrInsertTermEqE m c p e rest hmp]; exact hB
      | lt =>
          rw [csrInsertTermLtE m c p e rest hmp, csrNFSortedCons]
          exact csrAndIntro _ _ (csrBelowHeadConsTrue m p e rest hmp) hB
      | gt =>
          rw [csrInsertTermGtE m c p e rest hmp, csrNFSortedCons]
          have hpm : csrCompare p m = CsrMonoOrd.lt := csrCompareSwapGt m p hmp
          exact csrAndIntro _ _
            (csrBelowHeadInsert p m c rest hpm hbelow) (ih hrest)
theorem csrInsertFront (m : List Nat) (c : Nat) (B : CsrNF) (h : csrBelowHead m B = true) :
    csrInsertTerm (m, c) B = (m, c) :: B := by
  cases B with
  | nil => rfl
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      exact csrInsertTermLtE m c p e rest (csrBelowHeadConsLt m p e rest h)
theorem csrMergeAddNilRight (A : CsrNF) (hA : csrNFSorted A = true) : csrMergeAdd A [] = A := by
  induction A with
  | nil => rfl
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      have hbelow : csrBelowHead m a' = true := csrAndTrueLeft _ _ hA
      have hrest : csrNFSorted a' = true := csrAndTrueRight _ _ hA
      show csrInsertTerm (m, c) (csrMergeAdd a' []) = (m, c) :: a'
      rw [ih hrest, csrInsertFront m c a' hbelow]
theorem csrMergeAddComm (A B : CsrNF) (hA : csrNFSorted A = true) (hB : csrNFSorted B = true) :
    csrMergeAdd A B = csrMergeAdd B A := by
  have h := csrMergeAddSwap A B []
  rw [csrMergeAddNilRight B hB, csrMergeAddNilRight A hA] at h
  exact h
theorem csrMergeAddPreservesSorted (A B : CsrNF) (hB : csrNFSorted B = true) :
    csrNFSorted (csrMergeAdd A B) = true := by
  induction A with
  | nil => exact hB
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      show csrNFSorted (csrInsertTerm (m, c) (csrMergeAdd a' B)) = true
      exact csrInsertPreservesSorted m c (csrMergeAdd a' B) ih


-- monomial multiplication = multiset union of exponents
def csrMonoMul (m n : List Nat) : List Nat := insertMany n m
theorem csrMonoMulNilRight (m : List Nat) : csrMonoMul m [] = m := rfl
theorem csrMonoMulAssoc (m n p : List Nat) :
    csrMonoMul (csrMonoMul m n) p = csrMonoMul m (csrMonoMul n p) := by
  show insertMany p (insertMany n m) = insertMany (insertMany p n) m
  exact (insertManyAssoc p n m).symm

-- monomial sortedness
def csrMonoBelow (a : Nat) : List Nat → Bool
  | [] => true
  | b :: _ => natBle a b
def csrMonoSorted : List Nat → Bool
  | [] => true
  | a :: rest => csrMonoBelow a rest && csrMonoSorted rest
theorem csrMonoBelowNil (a : Nat) : csrMonoBelow a [] = true := rfl
theorem csrMonoBelowCons (a b : Nat) (rest : List Nat) : csrMonoBelow a (b :: rest) = natBle a b := rfl
theorem csrMonoSortedCons (a : Nat) (rest : List Nat) :
    csrMonoSorted (a :: rest) = (csrMonoBelow a rest && csrMonoSorted rest) := rfl
theorem csrMonoSortedSingleton (a : Nat) : csrMonoSorted [a] = true := rfl
theorem csrMonoBelowInsert (a v : Nat) (xs : List Nat)
    (hav : natBle a v = true) (hx : csrMonoBelow a xs = true) :
    csrMonoBelow a (insertSorted v xs) = true := by
  cases xs with
  | nil =>
      rw [insertSortedNilEq v, csrMonoBelowCons a v []]; exact hav
  | cons b rest =>
      have hab : natBle a b = true := by rw [csrMonoBelowCons a b rest] at hx; exact hx
      cases hvb : natBle v b with
      | true => rw [insertSortedConsTrue v b rest hvb, csrMonoBelowCons a v (b :: rest)]; exact hav
      | false => rw [insertSortedConsFalse v b rest hvb, csrMonoBelowCons a b (insertSorted v rest)]; exact hab
theorem csrInsertSortedPreservesSorted (v : Nat) (xs : List Nat)
    (hx : csrMonoSorted xs = true) : csrMonoSorted (insertSorted v xs) = true := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      have hbelow : csrMonoBelow a rest = true := csrAndTrueLeft _ _ hx
      have hrest : csrMonoSorted rest = true := csrAndTrueRight _ _ hx
      cases hva : natBle v a with
      | true =>
          rw [insertSortedConsTrue v a rest hva, csrMonoSortedCons v (a :: rest)]
          exact csrAndIntro _ _ (by rw [csrMonoBelowCons v a rest]; exact hva) hx
      | false =>
          rw [insertSortedConsFalse v a rest hva, csrMonoSortedCons a (insertSorted v rest)]
          have hav : natBle a v = true := natBleTotal v a hva
          exact csrAndIntro _ _ (csrMonoBelowInsert a v rest hav hbelow) (ih hrest)
theorem csrInsertManyPreservesSorted (ys xs : List Nat)
    (hx : csrMonoSorted xs = true) : csrMonoSorted (insertMany ys xs) = true := by
  induction ys with
  | nil => exact hx
  | cons y ys' ih =>
      show csrMonoSorted (insertSorted y (insertMany ys' xs)) = true
      exact csrInsertSortedPreservesSorted y (insertMany ys' xs) ih
theorem csrMonoMulSorted (m n : List Nat) (hm : csrMonoSorted m = true) :
    csrMonoSorted (csrMonoMul m n) = true := csrInsertManyPreservesSorted n m hm
theorem csrMonoInsertFront (a : Nat) (rest : List Nat) (h : csrMonoBelow a rest = true) :
    insertSorted a rest = a :: rest := by
  cases rest with
  | nil => rfl
  | cons b r' =>
      have hab : natBle a b = true := by rw [csrMonoBelowCons a b r'] at h; exact h
      exact insertSortedConsTrue a b r' hab
theorem csrMonoFixpoint (xs : List Nat) (h : csrMonoSorted xs = true) : insertMany xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      have hbelow : csrMonoBelow a rest = true := csrAndTrueLeft _ _ h
      have hrest : csrMonoSorted rest = true := csrAndTrueRight _ _ h
      show insertSorted a (insertMany rest []) = a :: rest
      rw [ih hrest, csrMonoInsertFront a rest hbelow]
theorem csrMonoMulComm (m n : List Nat) (hm : csrMonoSorted m = true) (hn : csrMonoSorted n = true) :
    csrMonoMul m n = csrMonoMul n m := by
  show insertMany n m = insertMany m n
  have h := insertManyComm n m []
  rw [csrMonoFixpoint m hm, csrMonoFixpoint n hn] at h
  exact h


-- single term times a poly (right multiply), and the convolution
def csrTermMul (m : List Nat) (c : Nat) : CsrNF → CsrNF
  | [] => []
  | (n, d) :: rest => csrInsertTerm (csrMonoMul m n, c * d) (csrTermMul m c rest)
def csrMulConvolve : CsrNF → CsrNF → CsrNF
  | [], _ => []
  | (m, c) :: rest, b => csrMergeAdd (csrTermMul m c b) (csrMulConvolve rest b)
theorem csrTermMulNil (m : List Nat) (c : Nat) : csrTermMul m c [] = [] := rfl
theorem csrTermMulCons (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) (rest : CsrNF) :
    csrTermMul m c ((n, d) :: rest) = csrInsertTerm (csrMonoMul m n, c * d) (csrTermMul m c rest) := rfl
theorem csrMulConvolveNil (b : CsrNF) : csrMulConvolve [] b = [] := rfl
theorem csrMulConvolveCons (m : List Nat) (c : Nat) (rest b : CsrNF) :
    csrMulConvolve ((m, c) :: rest) b = csrMergeAdd (csrTermMul m c b) (csrMulConvolve rest b) := rfl

theorem csrTermMulSorted (m : List Nat) (c : Nat) (B : CsrNF) :
    csrNFSorted (csrTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show csrNFSorted (csrInsertTerm (csrMonoMul m n, c * d) (csrTermMul m c rest)) = true
      exact csrInsertPreservesSorted (csrMonoMul m n) (c * d) (csrTermMul m c rest) ih
theorem csrMulConvolveSorted (A B : CsrNF) : csrNFSorted (csrMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show csrNFSorted (csrMergeAdd (csrTermMul m c B) (csrMulConvolve rest B)) = true
      exact csrMergeAddPreservesSorted (csrTermMul m c B) (csrMulConvolve rest B) ih

/-- ★ termMul commutes with a single insertion (coefficients distribute via `Nat.mul_add`). -/
theorem csrTermMul_insertTerm (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) (B : CsrNF) :
    csrTermMul m c (csrInsertTerm (n, d) B)
      = csrInsertTerm (csrMonoMul m n, c * d) (csrTermMul m c B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [csrInsertTermEqE n d p e rest hnp, csrTermMulCons m c p (e + d) rest,
              csrTermMulCons m c p e rest, hnp_eq,
              csrInsertTermMergeSame (csrMonoMul m p) (c * d) (c * e) (csrTermMul m c rest),
              Nat.mul_add c e d]
      | lt =>
          rw [csrInsertTermLtE n d p e rest hnp, csrTermMulCons m c n d ((p, e) :: rest),
              csrTermMulCons m c p e rest]
      | gt =>
          rw [csrInsertTermGtE n d p e rest hnp, csrTermMulCons m c p e (csrInsertTerm (n, d) rest),
              ih, csrTermMulCons m c p e rest,
              csrInsertTermComm (csrMonoMul m p) (c * e) (csrMonoMul m n) (c * d) (csrTermMul m c rest)]

theorem csrTermMul_merge (m : List Nat) (c : Nat) (B C : CsrNF) :
    csrTermMul m c (csrMergeAdd B C) = csrMergeAdd (csrTermMul m c B) (csrTermMul m c C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show csrTermMul m c (csrInsertTerm (n, d) (csrMergeAdd B' C))
        = csrMergeAdd (csrInsertTerm (csrMonoMul m n, c * d) (csrTermMul m c B')) (csrTermMul m c C)
      rw [csrTermMul_insertTerm m c n d (csrMergeAdd B' C), ih,
          csrMergeAddInsertTermLeft (csrMonoMul m n, c * d) (csrTermMul m c B') (csrTermMul m c C)]

theorem csrMulConvolveAnnihil (A : CsrNF) : csrMulConvolve A [] = [] := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show csrMergeAdd (csrTermMul m c []) (csrMulConvolve rest []) = []
      rw [csrTermMulNil m c, csrMergeAddNilLeft, ih]

/-- rearrange a merge of four sorted NFs, swapping the inner two. -/
theorem csrMergeAdd4Swap (a b c d : CsrNF)
    (hb : csrNFSorted b = true) (hc : csrNFSorted c = true) :
    csrMergeAdd (csrMergeAdd a b) (csrMergeAdd c d)
      = csrMergeAdd (csrMergeAdd a c) (csrMergeAdd b d) := by
  rw [csrMergeAddAssoc a b (csrMergeAdd c d), ← csrMergeAddAssoc b c d,
      csrMergeAddComm b c hb hc, csrMergeAddAssoc c b d, ← csrMergeAddAssoc a c (csrMergeAdd b d)]

/-- ★ left distributivity: `A * (B + C) = A*B + A*C`. -/
theorem csrMulConvolve_leftDistrib (A B C : CsrNF) :
    csrMulConvolve A (csrMergeAdd B C)
      = csrMergeAdd (csrMulConvolve A B) (csrMulConvolve A C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show csrMergeAdd (csrTermMul m c (csrMergeAdd B C)) (csrMulConvolve A' (csrMergeAdd B C))
        = csrMergeAdd (csrMergeAdd (csrTermMul m c B) (csrMulConvolve A' B))
            (csrMergeAdd (csrTermMul m c C) (csrMulConvolve A' C))
      rw [csrTermMul_merge m c B C, ih]
      exact csrMergeAdd4Swap (csrTermMul m c B) (csrTermMul m c C) (csrMulConvolve A' B)
        (csrMulConvolve A' C) (csrTermMulSorted m c C) (csrMulConvolveSorted A' B)


/-- termMul distributes over a coefficient sum. -/
theorem csrTermMul_coeffAdd (m : List Nat) (c1 c2 : Nat) (Z : CsrNF) :
    csrTermMul m (c1 + c2) Z = csrMergeAdd (csrTermMul m c1 Z) (csrTermMul m c2 Z) := by
  induction Z with
  | nil => rfl
  | cons head Z' ih =>
      obtain ⟨n, d⟩ := head
      show csrInsertTerm (csrMonoMul m n, (c1 + c2) * d) (csrTermMul m (c1 + c2) Z')
        = csrMergeAdd (csrInsertTerm (csrMonoMul m n, c1 * d) (csrTermMul m c1 Z'))
            (csrInsertTerm (csrMonoMul m n, c2 * d) (csrTermMul m c2 Z'))
      rw [csrMergeAddInsertTermLeft (csrMonoMul m n, c1 * d) (csrTermMul m c1 Z')
            (csrInsertTerm (csrMonoMul m n, c2 * d) (csrTermMul m c2 Z')),
          ← csrInsertTerm_mergeAdd (csrMonoMul m n, c2 * d) (csrTermMul m c1 Z') (csrTermMul m c2 Z'),
          csrInsertTermMergeSame (csrMonoMul m n) (c1 * d) (c2 * d)
            (csrMergeAdd (csrTermMul m c1 Z') (csrTermMul m c2 Z')),
          ih, csrNatAddMul c1 c2 d, Nat.add_comm (c1 * d) (c2 * d)]

/-- convolving after one insertion into the first argument. -/
theorem csrConvolve_insertTermLeft (m : List Nat) (c : Nat) (W Z : CsrNF) :
    csrMulConvolve (csrInsertTerm (m, c) W) Z
      = csrMergeAdd (csrTermMul m c Z) (csrMulConvolve W Z) := by
  induction W with
  | nil => rfl
  | cons head W' ih =>
      obtain ⟨p, g⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [csrInsertTermEqE m c p g W' hmp, csrMulConvolveCons p (g + c) W' Z,
              csrMulConvolveCons p g W' Z, hmeqp,
              csrTermMul_coeffAdd p g c Z,
              csrMergeAddAssoc (csrTermMul p g Z) (csrTermMul p c Z) (csrMulConvolve W' Z),
              csrMergeAddSwap (csrTermMul p g Z) (csrTermMul p c Z) (csrMulConvolve W' Z)]
      | lt =>
          rw [csrInsertTermLtE m c p g W' hmp, csrMulConvolveCons m c ((p, g) :: W') Z]
      | gt =>
          rw [csrInsertTermGtE m c p g W' hmp,
              csrMulConvolveCons p g (csrInsertTerm (m, c) W') Z, ih,
              csrMulConvolveCons p g W' Z,
              csrMergeAddSwap (csrTermMul p g Z) (csrTermMul m c Z) (csrMulConvolve W' Z)]

/-- ★ right distributivity: `(X + Y) * Z = X*Z + Y*Z`. -/
theorem csrMulConvolve_rightDistrib (X Y Z : CsrNF) :
    csrMulConvolve (csrMergeAdd X Y) Z
      = csrMergeAdd (csrMulConvolve X Z) (csrMulConvolve Y Z) := by
  induction X with
  | nil => rfl
  | cons head X' ih =>
      obtain ⟨m, c⟩ := head
      show csrMulConvolve (csrInsertTerm (m, c) (csrMergeAdd X' Y)) Z
        = csrMergeAdd (csrMergeAdd (csrTermMul m c Z) (csrMulConvolve X' Z)) (csrMulConvolve Y Z)
      rw [csrConvolve_insertTermLeft m c (csrMergeAdd X' Y) Z, ih,
          csrMergeAddAssoc (csrTermMul m c Z) (csrMulConvolve X' Z) (csrMulConvolve Y Z)]

/-- termMul composition: `(m*n)·(c*d)` applied to `C` equals scaling by `(m,c)` then `(n,d)`. -/
theorem csrTermMul_compose (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) (C : CsrNF) :
    csrTermMul (csrMonoMul m n) (c * d) C = csrTermMul m c (csrTermMul n d C) := by
  induction C with
  | nil => rfl
  | cons head C' ih =>
      obtain ⟨p, f⟩ := head
      show csrInsertTerm (csrMonoMul (csrMonoMul m n) p, c * d * f)
            (csrTermMul (csrMonoMul m n) (c * d) C')
        = csrTermMul m c (csrInsertTerm (csrMonoMul n p, d * f) (csrTermMul n d C'))
      rw [csrTermMul_insertTerm m c (csrMonoMul n p) (d * f) (csrTermMul n d C'), ih,
          csrMonoMulAssoc m n p, csrNatMulAssoc c d f]

/-- convolving a termMul equals termMul of a convolve. -/
theorem csrTermMul_convolve (m : List Nat) (c : Nat) (B C : CsrNF) :
    csrMulConvolve (csrTermMul m c B) C = csrTermMul m c (csrMulConvolve B C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show csrMulConvolve (csrInsertTerm (csrMonoMul m n, c * d) (csrTermMul m c B')) C
        = csrTermMul m c (csrMergeAdd (csrTermMul n d C) (csrMulConvolve B' C))
      rw [csrConvolve_insertTermLeft (csrMonoMul m n) (c * d) (csrTermMul m c B') C, ih,
          csrTermMul_merge m c (csrTermMul n d C) (csrMulConvolve B' C),
          csrTermMul_compose m c n d C]

/-- ★ associativity of the convolution: `(A*B)*C = A*(B*C)`. -/
theorem csrMulConvolveAssoc (A B C : CsrNF) :
    csrMulConvolve (csrMulConvolve A B) C = csrMulConvolve A (csrMulConvolve B C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show csrMulConvolve (csrMergeAdd (csrTermMul m c B) (csrMulConvolve A' B)) C
        = csrMergeAdd (csrTermMul m c (csrMulConvolve B C)) (csrMulConvolve A' (csrMulConvolve B C))
      rw [csrMulConvolve_rightDistrib (csrTermMul m c B) (csrMulConvolve A' B) C, ih,
          csrTermMul_convolve m c B C]


-- every monomial in the NF is sorted
def csrNFMonoSorted : CsrNF → Bool
  | [] => true
  | (m, _) :: rest => csrMonoSorted m && csrNFMonoSorted rest
theorem csrNFMonoSortedCons (m : List Nat) (c : Nat) (rest : CsrNF) :
    csrNFMonoSorted ((m, c) :: rest) = (csrMonoSorted m && csrNFMonoSorted rest) := rfl
theorem csrInsertTermMonoSorted (m : List Nat) (c : Nat) (B : CsrNF)
    (hm : csrMonoSorted m = true) (hB : csrNFMonoSorted B = true) :
    csrNFMonoSorted (csrInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rw [csrInsertTermNil m c, csrNFMonoSortedCons]; exact csrAndIntro _ _ hm rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hp : csrMonoSorted p = true := csrAndTrueLeft _ _ hB
      have hrest : csrNFMonoSorted rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq => rw [csrInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [csrInsertTermLtE m c p e rest hmp, csrNFMonoSortedCons]; exact csrAndIntro _ _ hm hB
      | gt =>
          rw [csrInsertTermGtE m c p e rest hmp, csrNFMonoSortedCons]
          exact csrAndIntro _ _ hp (ih hrest)
theorem csrMergeAddMonoSorted (A B : CsrNF) (hA : csrNFMonoSorted A = true)
    (hB : csrNFMonoSorted B = true) : csrNFMonoSorted (csrMergeAdd A B) = true := by
  induction A with
  | nil => exact hB
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hm : csrMonoSorted m = true := csrAndTrueLeft _ _ hA
      have hA' : csrNFMonoSorted A' = true := csrAndTrueRight _ _ hA
      show csrNFMonoSorted (csrInsertTerm (m, c) (csrMergeAdd A' B)) = true
      exact csrInsertTermMonoSorted m c (csrMergeAdd A' B) hm (ih hA')
theorem csrTermMulMonoSorted (m : List Nat) (c : Nat) (B : CsrNF) (hm : csrMonoSorted m = true) :
    csrNFMonoSorted (csrTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show csrNFMonoSorted (csrInsertTerm (csrMonoMul m n, c * d) (csrTermMul m c rest)) = true
      exact csrInsertTermMonoSorted (csrMonoMul m n) (c * d) (csrTermMul m c rest)
        (csrMonoMulSorted m n hm) ih
theorem csrMulConvolveMonoSorted (A B : CsrNF) (hA : csrNFMonoSorted A = true)
    (_hB : csrNFMonoSorted B = true) : csrNFMonoSorted (csrMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hm : csrMonoSorted m = true := csrAndTrueLeft _ _ hA
      have hA' : csrNFMonoSorted A' = true := csrAndTrueRight _ _ hA
      show csrNFMonoSorted (csrMergeAdd (csrTermMul m c B) (csrMulConvolve A' B)) = true
      exact csrMergeAddMonoSorted (csrTermMul m c B) (csrMulConvolve A' B)
        (csrTermMulMonoSorted m c B hm) (ih hA')

/-- termMul equals convolving with a single-term poly (needs sorted monomials for `monoMul` comm). -/
theorem csrTermMulEqConvolveSingle (m : List Nat) (c : Nat) (hm : csrMonoSorted m = true) :
    (B : CsrNF) → csrNFMonoSorted B = true → csrTermMul m c B = csrMulConvolve B [(m, c)]
  | [], _ => rfl
  | (n, d) :: B', hB => by
      have hn : csrMonoSorted n = true := csrAndTrueLeft _ _ hB
      have hB' : csrNFMonoSorted B' = true := csrAndTrueRight _ _ hB
      have ih := csrTermMulEqConvolveSingle m c hm B' hB'
      show csrInsertTerm (csrMonoMul m n, c * d) (csrTermMul m c B')
        = csrMergeAdd (csrTermMul n d [(m, c)]) (csrMulConvolve B' [(m, c)])
      rw [csrTermMulCons n d m c [], csrTermMulNil n d,
          csrMergeAddInsertTermLeft (csrMonoMul n m, d * c) [] (csrMulConvolve B' [(m, c)]),
          csrMergeAddNilLeft, ← ih, csrMonoMulComm m n hm hn, Nat.mul_comm c d]

/-- ★ commutativity of the convolution (needs sorted first arg + sorted monomials). -/
theorem csrMulConvolveComm : (A B : CsrNF) → csrNFSorted A = true → csrNFMonoSorted A = true →
    csrNFMonoSorted B = true → csrMulConvolve A B = csrMulConvolve B A
  | [], B, _, _, _ => (csrMulConvolveAnnihil B).symm
  | (m, c) :: A', B, hAs, hAm, hBm => by
      have hbelow : csrBelowHead m A' = true := csrAndTrueLeft _ _ hAs
      have hAs' : csrNFSorted A' = true := csrAndTrueRight _ _ hAs
      have hm : csrMonoSorted m = true := csrAndTrueLeft _ _ hAm
      have hAm' : csrNFMonoSorted A' = true := csrAndTrueRight _ _ hAm
      have ih := csrMulConvolveComm A' B hAs' hAm' hBm
      show csrMergeAdd (csrTermMul m c B) (csrMulConvolve A' B) = csrMulConvolve B ((m, c) :: A')
      rw [csrTermMulEqConvolveSingle m c hm B hBm, ih,
          ← csrMulConvolve_leftDistrib B [(m, c)] A', csrMergeAddCons (m, c) [] A',
          csrMergeAddNilLeft, csrInsertFront m c A' hbelow]


/-- ★ multiplicative unit: `A * [([],1)] = A` for a sorted NF. -/
theorem csrMulConvolveUnit : (A : CsrNF) → csrNFSorted A = true → csrMulConvolve A [([], 1)] = A
  | [], _ => rfl
  | (m, c) :: A', hAs => by
      have hbelow : csrBelowHead m A' = true := csrAndTrueLeft _ _ hAs
      have hAs' : csrNFSorted A' = true := csrAndTrueRight _ _ hAs
      have ih := csrMulConvolveUnit A' hAs'
      show csrMergeAdd (csrTermMul m c [([], 1)]) (csrMulConvolve A' [([], 1)]) = (m, c) :: A'
      rw [csrTermMulCons m c [] 1 [], csrTermMulNil m c, csrMonoMulNilRight m, Nat.mul_one c,
          csrMergeAddInsertTermLeft (m, c) [] (csrMulConvolve A' [([], 1)]), csrMergeAddNilLeft,
          ih, csrInsertFront m c A' hbelow]

/-- ★ the free commutative-semiring tree carrier. -/
inductive CsrTree where
  /-- a colour-tagged generator (variable). -/
  | gen (colour : Nat)
  /-- the additive unit `0`. -/
  | zeroOp
  /-- the multiplicative unit `1`. -/
  | oneOp
  /-- binary addition. -/
  | addOp : CsrTree → CsrTree → CsrTree
  /-- binary multiplication. -/
  | mulOp : CsrTree → CsrTree → CsrTree

/-- ★ normalize a tree to its polynomial normal form (sorted terms, positive coefficients). -/
def csrNormalize : CsrTree → CsrNF
  | .gen colour => [([colour], 1)]
  | .zeroOp => []
  | .oneOp => [([], 1)]
  | .addOp l r => csrMergeAdd (csrNormalize l) (csrNormalize r)
  | .mulOp l r => csrMulConvolve (csrNormalize l) (csrNormalize r)

theorem csrNormalize_gen (c : Nat) : csrNormalize (CsrTree.gen c) = [([c], 1)] := rfl
theorem csrNormalizeSorted (t : CsrTree) : csrNFSorted (csrNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | addOp l r ihl ihr =>
      show csrNFSorted (csrMergeAdd (csrNormalize l) (csrNormalize r)) = true
      exact csrMergeAddPreservesSorted (csrNormalize l) (csrNormalize r) ihr
  | mulOp l r _ _ =>
      show csrNFSorted (csrMulConvolve (csrNormalize l) (csrNormalize r)) = true
      exact csrMulConvolveSorted (csrNormalize l) (csrNormalize r)
theorem csrNormalizeMonoSorted (t : CsrTree) : csrNFMonoSorted (csrNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | addOp l r ihl ihr =>
      show csrNFMonoSorted (csrMergeAdd (csrNormalize l) (csrNormalize r)) = true
      exact csrMergeAddMonoSorted (csrNormalize l) (csrNormalize r) ihl ihr
  | mulOp l r ihl ihr =>
      show csrNFMonoSorted (csrMulConvolve (csrNormalize l) (csrNormalize r)) = true
      exact csrMulConvolveMonoSorted (csrNormalize l) (csrNormalize r) ihl ihr

/-- rfl smokes for the normal form. -/
theorem csrNormalize_zero_smoke : csrNormalize CsrTree.zeroOp = [] := rfl
theorem csrNormalize_one_smoke : csrNormalize CsrTree.oneOp = [([], 1)] := rfl
theorem csrNormalize_distrib_smoke :
    csrNormalize (CsrTree.mulOp (CsrTree.gen 0) (CsrTree.addOp (CsrTree.gen 1) (CsrTree.gen 2)))
      = csrNormalize (CsrTree.addOp (CsrTree.mulOp (CsrTree.gen 0) (CsrTree.gen 1))
          (CsrTree.mulOp (CsrTree.gen 0) (CsrTree.gen 2))) := rfl

/-- ★ commutative-semiring convertibility. -/
inductive SemiringTreeConv : CsrTree → CsrTree → Prop where
  | addAssoc (a b c : CsrTree) :
      SemiringTreeConv (CsrTree.addOp (CsrTree.addOp a b) c) (CsrTree.addOp a (CsrTree.addOp b c))
  | addComm (a b : CsrTree) : SemiringTreeConv (CsrTree.addOp a b) (CsrTree.addOp b a)
  | addZero (a : CsrTree) : SemiringTreeConv (CsrTree.addOp a CsrTree.zeroOp) a
  | mulAssoc (a b c : CsrTree) :
      SemiringTreeConv (CsrTree.mulOp (CsrTree.mulOp a b) c) (CsrTree.mulOp a (CsrTree.mulOp b c))
  | mulComm (a b : CsrTree) : SemiringTreeConv (CsrTree.mulOp a b) (CsrTree.mulOp b a)
  | mulOne (a : CsrTree) : SemiringTreeConv (CsrTree.mulOp a CsrTree.oneOp) a
  | distribLeft (a b c : CsrTree) :
      SemiringTreeConv (CsrTree.mulOp a (CsrTree.addOp b c))
        (CsrTree.addOp (CsrTree.mulOp a b) (CsrTree.mulOp a c))
  | annihilRight (a : CsrTree) : SemiringTreeConv (CsrTree.mulOp a CsrTree.zeroOp) CsrTree.zeroOp
  | addCongr {leftOld leftNew rightOld rightNew : CsrTree} :
      SemiringTreeConv leftOld leftNew → SemiringTreeConv rightOld rightNew →
      SemiringTreeConv (CsrTree.addOp leftOld rightOld) (CsrTree.addOp leftNew rightNew)
  | mulCongr {leftOld leftNew rightOld rightNew : CsrTree} :
      SemiringTreeConv leftOld leftNew → SemiringTreeConv rightOld rightNew →
      SemiringTreeConv (CsrTree.mulOp leftOld rightOld) (CsrTree.mulOp leftNew rightNew)
  | refl (t : CsrTree) : SemiringTreeConv t t
  | symm {s t : CsrTree} : SemiringTreeConv s t → SemiringTreeConv t s
  | trans {s t u : CsrTree} : SemiringTreeConv s t → SemiringTreeConv t u → SemiringTreeConv s u

/-- ★ soundness: convertible trees have equal normal form. -/
theorem csrNormalize_respects {s t : CsrTree} (conv : SemiringTreeConv s t) :
    csrNormalize s = csrNormalize t := by
  induction conv with
  | addAssoc a b c => exact csrMergeAddAssoc (csrNormalize a) (csrNormalize b) (csrNormalize c)
  | addComm a b =>
      exact csrMergeAddComm (csrNormalize a) (csrNormalize b)
        (csrNormalizeSorted a) (csrNormalizeSorted b)
  | addZero a =>
      show csrMergeAdd (csrNormalize a) [] = csrNormalize a
      exact csrMergeAddNilRight (csrNormalize a) (csrNormalizeSorted a)
  | mulAssoc a b c => exact csrMulConvolveAssoc (csrNormalize a) (csrNormalize b) (csrNormalize c)
  | mulComm a b =>
      exact csrMulConvolveComm (csrNormalize a) (csrNormalize b)
        (csrNormalizeSorted a) (csrNormalizeMonoSorted a) (csrNormalizeMonoSorted b)
  | mulOne a =>
      show csrMulConvolve (csrNormalize a) [([], 1)] = csrNormalize a
      exact csrMulConvolveUnit (csrNormalize a) (csrNormalizeSorted a)
  | distribLeft a b c =>
      exact csrMulConvolve_leftDistrib (csrNormalize a) (csrNormalize b) (csrNormalize c)
  | annihilRight a =>
      show csrMulConvolve (csrNormalize a) [] = []
      exact csrMulConvolveAnnihil (csrNormalize a)
  | addCongr _ _ ihl ihr =>
      show csrMergeAdd (csrNormalize _) (csrNormalize _) = csrMergeAdd (csrNormalize _) (csrNormalize _)
      rw [ihl, ihr]
  | mulCongr _ _ ihl ihr =>
      show csrMulConvolve (csrNormalize _) (csrNormalize _) = csrMulConvolve (csrNormalize _) (csrNormalize _)
      rw [ihl, ihr]
  | refl t => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2


-- derived Conv helpers
theorem csrConvAddZeroLeft (a : CsrTree) : SemiringTreeConv (CsrTree.addOp CsrTree.zeroOp a) a :=
  (SemiringTreeConv.addComm CsrTree.zeroOp a).trans (SemiringTreeConv.addZero a)
theorem csrConvMulOneLeft (a : CsrTree) : SemiringTreeConv (CsrTree.mulOp CsrTree.oneOp a) a :=
  (SemiringTreeConv.mulComm CsrTree.oneOp a).trans (SemiringTreeConv.mulOne a)
theorem csrConvAnnihilLeft (a : CsrTree) :
    SemiringTreeConv (CsrTree.mulOp CsrTree.zeroOp a) CsrTree.zeroOp :=
  (SemiringTreeConv.mulComm CsrTree.zeroOp a).trans (SemiringTreeConv.annihilRight a)
theorem csrConvDistribRight (a b c : CsrTree) :
    SemiringTreeConv (CsrTree.mulOp (CsrTree.addOp a b) c)
      (CsrTree.addOp (CsrTree.mulOp a c) (CsrTree.mulOp b c)) :=
  (SemiringTreeConv.mulComm (CsrTree.addOp a b) c).trans
    ((SemiringTreeConv.distribLeft c a b).trans
      (SemiringTreeConv.addCongr (SemiringTreeConv.mulComm c a) (SemiringTreeConv.mulComm c b)))
theorem csrConvAddSwap13 (x y z : CsrTree) :
    SemiringTreeConv (CsrTree.addOp x (CsrTree.addOp y z)) (CsrTree.addOp y (CsrTree.addOp x z)) :=
  (SemiringTreeConv.symm (SemiringTreeConv.addAssoc x y z)).trans
    ((SemiringTreeConv.addCongr (SemiringTreeConv.addComm x y) (SemiringTreeConv.refl z)).trans
      (SemiringTreeConv.addAssoc y x z))
theorem csrConvMulSwap13 (x y z : CsrTree) :
    SemiringTreeConv (CsrTree.mulOp x (CsrTree.mulOp y z)) (CsrTree.mulOp y (CsrTree.mulOp x z)) :=
  (SemiringTreeConv.symm (SemiringTreeConv.mulAssoc x y z)).trans
    ((SemiringTreeConv.mulCongr (SemiringTreeConv.mulComm x y) (SemiringTreeConv.refl z)).trans
      (SemiringTreeConv.mulAssoc y x z))

-- coefficient-many copies of a monomial tree
def csrScaleTree (mono : CsrTree) : Nat → CsrTree
  | 0 => CsrTree.zeroOp
  | Nat.succ k => CsrTree.addOp mono (csrScaleTree mono k)
theorem csrScaleTreeCongr {mono1 mono2 : CsrTree} (h : SemiringTreeConv mono1 mono2) (n : Nat) :
    SemiringTreeConv (csrScaleTree mono1 n) (csrScaleTree mono2 n) := by
  induction n with
  | zero => exact SemiringTreeConv.refl CsrTree.zeroOp
  | succ k ih => exact SemiringTreeConv.addCongr h ih
theorem csrScaleAdd (mono : CsrTree) (a b : Nat) :
    SemiringTreeConv (csrScaleTree mono (a + b))
      (CsrTree.addOp (csrScaleTree mono a) (csrScaleTree mono b)) := by
  induction b with
  | zero => exact (SemiringTreeConv.addZero (csrScaleTree mono a)).symm
  | succ k ih =>
      exact (SemiringTreeConv.addCongr (SemiringTreeConv.refl mono) ih).trans
        (csrConvAddSwap13 mono (csrScaleTree mono a) (csrScaleTree mono k))
theorem csrScaleTreeMulLeft (p q : CsrTree) (c : Nat) :
    SemiringTreeConv (csrScaleTree (CsrTree.mulOp p q) c) (CsrTree.mulOp (csrScaleTree p c) q) := by
  induction c with
  | zero => exact (csrConvAnnihilLeft q).symm
  | succ k ih =>
      exact (SemiringTreeConv.addCongr (SemiringTreeConv.refl (CsrTree.mulOp p q)) ih).trans
        (csrConvDistribRight p (csrScaleTree p k) q).symm
theorem csrScaleTreeMulRight (p q : CsrTree) (d : Nat) :
    SemiringTreeConv (csrScaleTree (CsrTree.mulOp p q) d) (CsrTree.mulOp p (csrScaleTree q d)) := by
  induction d with
  | zero => exact (SemiringTreeConv.annihilRight p).symm
  | succ k ih =>
      exact (SemiringTreeConv.addCongr (SemiringTreeConv.refl (CsrTree.mulOp p q)) ih).trans
        (SemiringTreeConv.distribLeft p q (csrScaleTree q k)).symm
theorem csrScaleTreeMulCoeff (X : CsrTree) (c d : Nat) :
    SemiringTreeConv (csrScaleTree X (c * d)) (csrScaleTree (csrScaleTree X d) c) := by
  induction c with
  | zero => rw [Nat.zero_mul d]; exact SemiringTreeConv.refl CsrTree.zeroOp
  | succ k ih =>
      rw [Nat.succ_mul k d]
      exact (csrScaleAdd X (k * d) d).trans
        ((SemiringTreeConv.addCongr ih (SemiringTreeConv.refl (csrScaleTree X d))).trans
          (SemiringTreeConv.addComm (csrScaleTree (csrScaleTree X d) k) (csrScaleTree X d)))

-- monomial → tree, and its reification
def csrMonoToTree : List Nat → CsrTree
  | [] => CsrTree.oneOp
  | c :: rest => CsrTree.mulOp (CsrTree.gen c) (csrMonoToTree rest)
theorem csrMonoToTreeInsertSorted (v : Nat) (xs : List Nat) :
    SemiringTreeConv (csrMonoToTree (insertSorted v xs))
      (CsrTree.mulOp (CsrTree.gen v) (csrMonoToTree xs)) := by
  induction xs with
  | nil => exact SemiringTreeConv.refl (CsrTree.mulOp (CsrTree.gen v) CsrTree.oneOp)
  | cons a rest ih =>
      cases hva : natBle v a with
      | true =>
          rw [insertSortedConsTrue v a rest hva]
          exact SemiringTreeConv.refl _
      | false =>
          rw [insertSortedConsFalse v a rest hva]
          show SemiringTreeConv (CsrTree.mulOp (CsrTree.gen a) (csrMonoToTree (insertSorted v rest)))
            (CsrTree.mulOp (CsrTree.gen v) (CsrTree.mulOp (CsrTree.gen a) (csrMonoToTree rest)))
          exact (SemiringTreeConv.mulCongr (SemiringTreeConv.refl (CsrTree.gen a)) ih).trans
            (csrConvMulSwap13 (CsrTree.gen a) (CsrTree.gen v) (csrMonoToTree rest))
theorem csrMonoToTreeInsertMany (n m : List Nat) :
    SemiringTreeConv (csrMonoToTree (insertMany n m))
      (CsrTree.mulOp (csrMonoToTree n) (csrMonoToTree m)) := by
  induction n with
  | nil => exact (csrConvMulOneLeft (csrMonoToTree m)).symm
  | cons a n' ih =>
      show SemiringTreeConv (csrMonoToTree (insertSorted a (insertMany n' m)))
        (CsrTree.mulOp (CsrTree.mulOp (CsrTree.gen a) (csrMonoToTree n')) (csrMonoToTree m))
      exact (csrMonoToTreeInsertSorted a (insertMany n' m)).trans
        ((SemiringTreeConv.mulCongr (SemiringTreeConv.refl (CsrTree.gen a)) ih).trans
          (SemiringTreeConv.symm
            (SemiringTreeConv.mulAssoc (CsrTree.gen a) (csrMonoToTree n') (csrMonoToTree m))))
theorem csrMonoToTreeMonoMul (m n : List Nat) :
    SemiringTreeConv (csrMonoToTree (csrMonoMul m n))
      (CsrTree.mulOp (csrMonoToTree m) (csrMonoToTree n)) := by
  show SemiringTreeConv (csrMonoToTree (insertMany n m))
    (CsrTree.mulOp (csrMonoToTree m) (csrMonoToTree n))
  exact (csrMonoToTreeInsertMany n m).trans (SemiringTreeConv.mulComm (csrMonoToTree n) (csrMonoToTree m))

-- term → tree, and the term-product reification
def csrTermToTree (mono : List Nat) (coeff : Nat) : CsrTree := csrScaleTree (csrMonoToTree mono) coeff
theorem csrTermToTreeMul (m : List Nat) (c : Nat) (n : List Nat) (d : Nat) :
    SemiringTreeConv (csrTermToTree (csrMonoMul m n) (c * d))
      (CsrTree.mulOp (csrTermToTree m c) (csrTermToTree n d)) := by
  show SemiringTreeConv (csrScaleTree (csrMonoToTree (csrMonoMul m n)) (c * d))
    (CsrTree.mulOp (csrScaleTree (csrMonoToTree m) c) (csrScaleTree (csrMonoToTree n) d))
  exact (csrScaleTreeCongr (csrMonoToTreeMonoMul m n) (c * d)).trans
    ((csrScaleTreeMulCoeff (CsrTree.mulOp (csrMonoToTree m) (csrMonoToTree n)) c d).trans
      ((csrScaleTreeCongr
          (csrScaleTreeMulRight (csrMonoToTree m) (csrMonoToTree n) d) c).trans
        (csrScaleTreeMulLeft (csrMonoToTree m) (csrScaleTree (csrMonoToTree n) d) c)))


/-- rebuild a canonical tree from a normal form. -/
def csrCombOfNF : CsrNF → CsrTree
  | [] => CsrTree.zeroOp
  | (m, c) :: rest => CsrTree.addOp (csrTermToTree m c) (csrCombOfNF rest)
theorem csrCombOfNFCons (m : List Nat) (c : Nat) (rest : CsrNF) :
    csrCombOfNF ((m, c) :: rest) = CsrTree.addOp (csrTermToTree m c) (csrCombOfNF rest) := rfl

theorem csrCombInsertTerm (m : List Nat) (c : Nat) (A : CsrNF) :
    SemiringTreeConv (csrCombOfNF (csrInsertTerm (m, c) A))
      (CsrTree.addOp (csrTermToTree m c) (csrCombOfNF A)) := by
  induction A with
  | nil => exact SemiringTreeConv.refl _
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [csrInsertTermEqE m c p e rest hmp, csrCombOfNFCons p (e + c) rest,
              csrCombOfNFCons p e rest, hmeqp]
          exact (SemiringTreeConv.addCongr (csrScaleAdd (csrMonoToTree p) e c)
              (SemiringTreeConv.refl (csrCombOfNF rest))).trans
            ((SemiringTreeConv.addAssoc (csrTermToTree p e) (csrTermToTree p c) (csrCombOfNF rest)).trans
              (csrConvAddSwap13 (csrTermToTree p e) (csrTermToTree p c) (csrCombOfNF rest)))
      | lt =>
          rw [csrInsertTermLtE m c p e rest hmp, csrCombOfNFCons m c ((p, e) :: rest)]
          exact SemiringTreeConv.refl _
      | gt =>
          rw [csrInsertTermGtE m c p e rest hmp, csrCombOfNFCons p e (csrInsertTerm (m, c) rest),
              csrCombOfNFCons p e rest]
          exact (SemiringTreeConv.addCongr (SemiringTreeConv.refl (csrTermToTree p e)) ih).trans
            (csrConvAddSwap13 (csrTermToTree p e) (csrTermToTree m c) (csrCombOfNF rest))

theorem csrCombMergeAdd (A B : CsrNF) :
    SemiringTreeConv (csrCombOfNF (csrMergeAdd A B))
      (CsrTree.addOp (csrCombOfNF A) (csrCombOfNF B)) := by
  induction A with
  | nil => exact (csrConvAddZeroLeft (csrCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show SemiringTreeConv (csrCombOfNF (csrInsertTerm (m, c) (csrMergeAdd A' B)))
        (CsrTree.addOp (CsrTree.addOp (csrTermToTree m c) (csrCombOfNF A')) (csrCombOfNF B))
      exact ((csrCombInsertTerm m c (csrMergeAdd A' B)).trans
          (SemiringTreeConv.addCongr (SemiringTreeConv.refl (csrTermToTree m c)) ih)).trans
        (SemiringTreeConv.symm
          (SemiringTreeConv.addAssoc (csrTermToTree m c) (csrCombOfNF A') (csrCombOfNF B)))

theorem csrCombTermMul (m : List Nat) (c : Nat) (B : CsrNF) :
    SemiringTreeConv (csrCombOfNF (csrTermMul m c B))
      (CsrTree.mulOp (csrTermToTree m c) (csrCombOfNF B)) := by
  induction B with
  | nil => exact (SemiringTreeConv.annihilRight (csrTermToTree m c)).symm
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show SemiringTreeConv (csrCombOfNF (csrInsertTerm (csrMonoMul m n, c * d) (csrTermMul m c B')))
        (CsrTree.mulOp (csrTermToTree m c) (CsrTree.addOp (csrTermToTree n d) (csrCombOfNF B')))
      exact ((csrCombInsertTerm (csrMonoMul m n) (c * d) (csrTermMul m c B')).trans
          (SemiringTreeConv.addCongr (csrTermToTreeMul m c n d) ih)).trans
        (SemiringTreeConv.symm
          (SemiringTreeConv.distribLeft (csrTermToTree m c) (csrTermToTree n d) (csrCombOfNF B')))

theorem csrCombMulConvolve (A B : CsrNF) :
    SemiringTreeConv (csrCombOfNF (csrMulConvolve A B))
      (CsrTree.mulOp (csrCombOfNF A) (csrCombOfNF B)) := by
  induction A with
  | nil => exact (csrConvAnnihilLeft (csrCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show SemiringTreeConv (csrCombOfNF (csrMergeAdd (csrTermMul m c B) (csrMulConvolve A' B)))
        (CsrTree.mulOp (CsrTree.addOp (csrTermToTree m c) (csrCombOfNF A')) (csrCombOfNF B))
      exact ((csrCombMergeAdd (csrTermMul m c B) (csrMulConvolve A' B)).trans
          (SemiringTreeConv.addCongr (csrCombTermMul m c B) ih)).trans
        (SemiringTreeConv.symm (csrConvDistribRight (csrTermToTree m c) (csrCombOfNF A') (csrCombOfNF B)))

/-- ★ every tree is convertible to the rebuild of its own normal form. -/
theorem csrTreeReifies (t : CsrTree) : SemiringTreeConv t (csrCombOfNF (csrNormalize t)) := by
  induction t with
  | gen c =>
      show SemiringTreeConv (CsrTree.gen c)
        (CsrTree.addOp (csrTermToTree [c] 1) CsrTree.zeroOp)
      have hgen : SemiringTreeConv (CsrTree.gen c) (csrTermToTree [c] 1) :=
        (SemiringTreeConv.symm (SemiringTreeConv.mulOne (CsrTree.gen c))).trans
          (SemiringTreeConv.symm
            (SemiringTreeConv.addZero (CsrTree.mulOp (CsrTree.gen c) CsrTree.oneOp)))
      exact hgen.trans (SemiringTreeConv.symm (SemiringTreeConv.addZero (csrTermToTree [c] 1)))
  | zeroOp => exact SemiringTreeConv.refl CsrTree.zeroOp
  | oneOp =>
      show SemiringTreeConv CsrTree.oneOp (CsrTree.addOp (csrTermToTree [] 1) CsrTree.zeroOp)
      exact (SemiringTreeConv.symm (SemiringTreeConv.addZero CsrTree.oneOp)).trans
        (SemiringTreeConv.symm (SemiringTreeConv.addZero (csrTermToTree [] 1)))
  | addOp l r ihl ihr =>
      show SemiringTreeConv (CsrTree.addOp l r)
        (csrCombOfNF (csrMergeAdd (csrNormalize l) (csrNormalize r)))
      exact (SemiringTreeConv.addCongr ihl ihr).trans
        (SemiringTreeConv.symm (csrCombMergeAdd (csrNormalize l) (csrNormalize r)))
  | mulOp l r ihl ihr =>
      show SemiringTreeConv (CsrTree.mulOp l r)
        (csrCombOfNF (csrMulConvolve (csrNormalize l) (csrNormalize r)))
      exact (SemiringTreeConv.mulCongr ihl ihr).trans
        (SemiringTreeConv.symm (csrCombMulConvolve (csrNormalize l) (csrNormalize r)))

/-- ★ completeness: equal normal forms give convertible trees. -/
theorem csrConv_of_normalizeEq {s t : CsrTree} (h : csrNormalize s = csrNormalize t) :
    SemiringTreeConv s t := by
  have hcomb : csrCombOfNF (csrNormalize s) = csrCombOfNF (csrNormalize t) := congrArg csrCombOfNF h
  exact (csrTreeReifies s).trans (hcomb ▸ (csrTreeReifies t).symm)

-- structural NF equality
def csrNFEq : CsrNF → CsrNF → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | (m1, c1) :: r1, (m2, c2) :: r2 => (csrNatListEq m1 m2 && Nat.beq c1 c2) && csrNFEq r1 r2
theorem csrNFEqRefl (A : CsrNF) : csrNFEq A A = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show ((csrNatListEq m m && Nat.beq c c) && csrNFEq rest rest) = true
      exact csrAndIntro _ _ (csrAndIntro _ _ (csrNatListEqRefl m) (csrNatBeqRefl c)) ih
theorem csrNFEq_eq (A B : CsrNF) : csrNFEq A B = true → A = B := by
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
          have hpair : (csrNatListEq m1 m2 && Nat.beq c1 c2) = true := csrAndTrueLeft _ _ h
          have hrest : csrNFEq A' B' = true := csrAndTrueRight _ _ h
          have hm : m1 = m2 := csrNatListEq_eq m1 m2 (csrAndTrueLeft _ _ hpair)
          have hc : c1 = c2 := csrNatEqOfBeq c1 c2 (csrAndTrueRight _ _ hpair)
          rw [hm, hc, ih B' hrest]

/-- ★★ the decision procedure. -/
def csrDecideConv (s t : CsrTree) : Bool := csrNFEq (csrNormalize s) (csrNormalize t)

/-- ★★ THE DECISION: convertibility ⟺ equal polynomial normal form. -/
theorem semiringTreeConv_iff_normalForm (s t : CsrTree) :
    SemiringTreeConv s t ↔ csrDecideConv s t = true := by
  constructor
  · intro conv
    show csrNFEq (csrNormalize s) (csrNormalize t) = true
    rw [csrNormalize_respects conv]; exact csrNFEqRefl (csrNormalize t)
  · intro hdec
    exact csrConv_of_normalizeEq (csrNFEq_eq (csrNormalize s) (csrNormalize t) hdec)

/-- ★ decidability, via the biconditional (no `propext`). -/
instance csrDecidableConv (s t : CsrTree) : Decidable (SemiringTreeConv s t) :=
  if h : csrDecideConv s t = true then
    isTrue ((semiringTreeConv_iff_normalForm s t).mpr h)
  else
    isFalse (fun conv => h ((semiringTreeConv_iff_normalForm s t).mp conv))

/-- ★★ the walking free commutative semiring on ℕ is DECIDED. -/
def fxWalkingCommutativeSemiring_hasNormalFormDecision : Bool := true

-- genuineness smokes
#eval csrDecideConv (CsrTree.mulOp (CsrTree.gen 0) (CsrTree.addOp (CsrTree.gen 1) (CsrTree.gen 2)))
  (CsrTree.addOp (CsrTree.mulOp (CsrTree.gen 0) (CsrTree.gen 1))
    (CsrTree.mulOp (CsrTree.gen 0) (CsrTree.gen 2)))
#eval csrDecideConv (CsrTree.addOp (CsrTree.gen 0) (CsrTree.gen 1))
  (CsrTree.addOp (CsrTree.gen 1) (CsrTree.gen 0))
#eval csrDecideConv (CsrTree.mulOp (CsrTree.gen 0) (CsrTree.gen 1))
  (CsrTree.mulOp (CsrTree.gen 1) (CsrTree.gen 0))
#eval csrDecideConv (CsrTree.gen 0) (CsrTree.gen 1)
#eval csrDecideConv (CsrTree.mulOp (CsrTree.gen 0) CsrTree.zeroOp) CsrTree.zeroOp
#eval csrDecideConv
  (CsrTree.mulOp (CsrTree.addOp (CsrTree.gen 0) CsrTree.oneOp)
    (CsrTree.addOp (CsrTree.gen 0) CsrTree.oneOp))
  (CsrTree.addOp (CsrTree.addOp (CsrTree.addOp (CsrTree.mulOp (CsrTree.gen 0) (CsrTree.gen 0))
    (CsrTree.gen 0)) (CsrTree.gen 0)) CsrTree.oneOp)
#eval csrDecideConv (CsrTree.addOp (CsrTree.gen 0) (CsrTree.gen 0)) (CsrTree.gen 0)

end FX1Poly.Polygraph
