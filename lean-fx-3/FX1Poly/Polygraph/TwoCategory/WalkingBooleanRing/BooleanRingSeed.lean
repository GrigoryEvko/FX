import FX1Poly.Polygraph.TwoCategory.WalkingSemilattice.FiniteSetSemilatticeSeed
import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeSemiring.CommutativeSemiringSeed
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # WalkingBooleanRing/BooleanRingSeed — the walking free BOOLEAN RING on ℕ: F2[X]/(x²=x), the Zhegalkin decision

The idempotent-multiplication successor of the commutative-ring rung.  A **Boolean ring** is a commutative ring
in which every element is idempotent (`x·x = x`); equivalently the free F2-algebra with `x² = x` for every
generator.  The free Boolean ring on the colour set `ℕ` is the ZHEGALKIN normal form: every element is a unique
XOR (F2 sum) of squarefree MONOMIALS, where a monomial is a finite SET of distinct variables (because `x·x = x`,
variable exponents collapse to 0/1) and coefficients live in F2 (present/absent).  Two elements coincide exactly
when they have the same set of present monomials — a COMPLETE invariant, so the word problem is DECIDED.

## ★ The two ingredients that specialise the ℤ[X] ring to F2[X]/(x²=x)

* **Monomials are idempotent variable SETS.**  A monomial reuses the imported finite-SET kit
  (`insertSortedSet` / `insertManySet` from `FiniteSetSemilatticeSeed`, the dedup-on-equal inserts), so monomial
  product `brMonoMul m n := insertManySet n m` is variable-set UNION — idempotent (`{x} ∪ {x} = {x}`), which is
  exactly the `x·x = x` content.
* **Coefficients are F2, carried as `Bool`.**  Mirroring the ℤ[X] ring's subtraction-free `(pos, neg)`
  representation, this file carries each F2 coefficient as a `Bool` and, following the same NO-DROP discipline,
  never removes a cancelling term: `brCoeffXor` (F2 add = `Bool` xor), `brCoeffAnd` (F2 mul = `Bool` and),
  `brCoeffIsZero` (absent = `false`).  Because F2 addition is its own inverse (`x + x = 0`), NEGATION IS THE
  IDENTITY — the entire negate layer of the ℤ[X] ring disappears, and the difference `A − B` is simply `A + B`.

`BrNF := List (List Nat × Bool)` is a list of `(monomial, coeff)` terms sorted strictly by the imported monomial
order `csrCompare` (length-first then lex).  `brNormalize` sends `gen c ↦ [([c], true)]`, `zeroOp ↦ []`,
`oneOp ↦ [([], true)]` (the empty monomial is the multiplicative unit), `xorOp ↦ brMergeXor` (coefficient-XOR
merge), `andOp ↦ brMulConvolve` (the Cauchy convolution: monomial product = set union, coefficient product = and).

The DECISION is the F2 polynomial equality `brNFEq A B := brNFAllZero (brMergeXor A B)` — two polynomials agree
exactly when their XOR-difference has every coefficient absent.  Its soundness / completeness rest on the
`brEvalCross` semantic model (the per-monomial F2 coefficient), whose merge homomorphism makes `brNFEq` a
decidable congruence; the crux `brMergeXor A A` all-absent (the F2 self-inverse `x + x = 0`) falls out of the
model (each monomial's `c xor c = false`).

`andIdem` is imposed on GENERATORS (`andOp (gen c)(gen c) ≈ gen c`) — the honest presentation of the FREE
Boolean ring `F2[X]/(x_c² = x_c)`.  The composite Boolean-ring idempotence `a·a ≈ a` for every `a` is then a
DERIVED theorem, decided computationally and produced by completeness (see the `(x+1)²` grounding).

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` in the audit
twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`,
`Int`, `Nat.sub`, `List.append` (`++`), and every `Nat.le`/`Nat.ble` lemma — the ordering is the imported
structural `csrCompare` (over `natBle`), the monomial product is the imported cons-only `insertManySet`, and
coefficient arithmetic is the finite `Bool` xor/and kit (no coefficient multiplication beyond `Bool` and). -/

namespace FX1Poly.Polygraph

/-! ## The F2 coefficient algebra as `Bool` (xor / and), all laws by finite case analysis -/

/-- F2 addition on the `Bool` coefficient: exclusive or. -/
def brCoeffXor : Bool → Bool → Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

/-- F2 multiplication on the `Bool` coefficient: conjunction. -/
def brCoeffAnd : Bool → Bool → Bool
  | false, false => false
  | false, true => false
  | true, false => false
  | true, true => true

/-- A coefficient is zero (absent) exactly when it is `false`. -/
def brCoeffIsZero : Bool → Bool
  | false => true
  | true => false

theorem brCoeffXorComm (a b : Bool) : brCoeffXor a b = brCoeffXor b a := by
  cases a <;> cases b <;> rfl
theorem brCoeffXorAssoc (a b c : Bool) :
    brCoeffXor (brCoeffXor a b) c = brCoeffXor a (brCoeffXor b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem brCoeffXorFalseRight (a : Bool) : brCoeffXor a false = a := by cases a <;> rfl
theorem brCoeffXorFalseLeft (a : Bool) : brCoeffXor false a = a := by cases a <;> rfl
theorem brCoeffXorRightComm (e d c : Bool) :
    brCoeffXor (brCoeffXor e d) c = brCoeffXor (brCoeffXor e c) d := by
  cases e <;> cases d <;> cases c <;> rfl
theorem brCoeffXorSwap13 (x y z : Bool) :
    brCoeffXor x (brCoeffXor y z) = brCoeffXor y (brCoeffXor x z) := by
  cases x <;> cases y <;> cases z <;> rfl
theorem brCoeffAndComm (a b : Bool) : brCoeffAnd a b = brCoeffAnd b a := by
  cases a <;> cases b <;> rfl
theorem brCoeffAndTrueRight (a : Bool) : brCoeffAnd a true = a := by cases a <;> rfl
theorem brCoeffAndAssoc (a b c : Bool) :
    brCoeffAnd (brCoeffAnd a b) c = brCoeffAnd a (brCoeffAnd b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem brCoeffAndXorRight (a b c : Bool) :
    brCoeffAnd a (brCoeffXor b c) = brCoeffXor (brCoeffAnd a b) (brCoeffAnd a c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem brCoeffXorAndRight (a b c : Bool) :
    brCoeffAnd (brCoeffXor a b) c = brCoeffXor (brCoeffAnd a c) (brCoeffAnd b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem brCoeffXorSelfZero (a : Bool) : brCoeffIsZero (brCoeffXor a a) = true := by cases a <;> rfl
theorem brCoeffXorZeroValued (a b : Bool)
    (ha : brCoeffIsZero a = true) (hb : brCoeffIsZero b = true) :
    brCoeffIsZero (brCoeffXor a b) = true := by
  cases a with
  | true => exact Bool.noConfusion ha
  | false => cases b with
    | true => exact Bool.noConfusion hb
    | false => rfl
theorem brCoeffAndZeroValuedLeft (a b : Bool) (ha : brCoeffIsZero a = true) :
    brCoeffIsZero (brCoeffAnd a b) = true := by
  cases a with
  | true => exact Bool.noConfusion ha
  | false => cases b with | true => rfl | false => rfl
theorem brCoeffAndZeroValuedRight (a b : Bool) (hb : brCoeffIsZero b = true) :
    brCoeffIsZero (brCoeffAnd a b) = true := by
  rw [brCoeffAndComm a b]; exact brCoeffAndZeroValuedLeft b a hb
theorem brCoeffXorCancelZero (a b : Bool)
    (hsum : brCoeffIsZero (brCoeffXor a b) = true) (hb : brCoeffIsZero b = true) :
    brCoeffIsZero a = true := by
  cases b with
  | true => exact Bool.noConfusion hb
  | false => rw [brCoeffXorFalseRight a] at hsum; exact hsum

/-! ## The monomial layer: variable SETS via the imported `insertManySet`, strict-sorted and idempotent -/

/-- Strict-below test for a monomial's leading variable: `a` lies strictly before the head. -/
def brMonoBelow (a : Nat) : List Nat → Bool
  | [] => true
  | b :: _ =>
      match natBle b a with
      | true => false
      | false => true
/-- A monomial is a SORTED, DISTINCT variable list (a set). -/
def brMonoSorted : List Nat → Bool
  | [] => true
  | a :: rest => brMonoBelow a rest && brMonoSorted rest
theorem brMonoBelowNil (a : Nat) : brMonoBelow a [] = true := rfl
theorem brMonoSortedCons (a : Nat) (rest : List Nat) :
    brMonoSorted (a :: rest) = (brMonoBelow a rest && brMonoSorted rest) := rfl
theorem brMonoBelowConsTrue (a b : Nat) (rest : List Nat) (h : natBle b a = false) :
    brMonoBelow a (b :: rest) = true := by
  show (match natBle b a with | true => false | false => true) = true
  rw [h]
theorem brMonoBelowConsLt (a b : Nat) (rest : List Nat) (h : brMonoBelow a (b :: rest) = true) :
    natBle b a = false := by
  cases hb : natBle b a with
  | false => rfl
  | true =>
      exact absurd h (by
        show (match natBle b a with | true => false | false => true) ≠ true
        rw [hb]; exact fun hh => Bool.noConfusion hh)
theorem brMonoInsertFront (a : Nat) (rest : List Nat) (h : brMonoBelow a rest = true) :
    insertSortedSet a rest = a :: rest := by
  cases rest with
  | nil => exact insertSortedSetNilEq a
  | cons b r' =>
      have hba : natBle b a = false := brMonoBelowConsLt a b r' h
      have hab : natBle a b = true := natBleTotal b a hba
      exact insertSortedSetLt a b r' hab hba
theorem brMonoBelowInsertSortedSet (a v : Nat) (xs : List Nat)
    (hav : natBle v a = false) (hx : brMonoBelow a xs = true) :
    brMonoBelow a (insertSortedSet v xs) = true := by
  cases xs with
  | nil => rw [insertSortedSetNilEq v]; exact brMonoBelowConsTrue a v [] hav
  | cons b rest =>
      have hba : natBle b a = false := brMonoBelowConsLt a b rest hx
      cases hvb : natBle v b with
      | true =>
          cases hbv : natBle b v with
          | true => rw [insertSortedSetEq v b rest hvb hbv]; exact hx
          | false => rw [insertSortedSetLt v b rest hvb hbv]; exact brMonoBelowConsTrue a v (b :: rest) hav
      | false => rw [insertSortedSetGt v b rest hvb]; exact brMonoBelowConsTrue a b (insertSortedSet v rest) hba
theorem brInsertSortedSetPreservesMonoSorted (v : Nat) (xs : List Nat)
    (hx : brMonoSorted xs = true) : brMonoSorted (insertSortedSet v xs) = true := by
  induction xs with
  | nil => rw [insertSortedSetNilEq v]; rfl
  | cons a rest ih =>
      have hbelow : brMonoBelow a rest = true := csrAndTrueLeft _ _ hx
      have hrest : brMonoSorted rest = true := csrAndTrueRight _ _ hx
      cases hva : natBle v a with
      | false =>
          rw [insertSortedSetGt v a rest hva, brMonoSortedCons]
          exact csrAndIntro _ _ (brMonoBelowInsertSortedSet a v rest hva hbelow) (ih hrest)
      | true =>
          cases hav : natBle a v with
          | true => rw [insertSortedSetEq v a rest hva hav]; exact hx
          | false =>
              rw [insertSortedSetLt v a rest hva hav, brMonoSortedCons]
              exact csrAndIntro _ _ (brMonoBelowConsTrue v a rest hav) hx
theorem brInsertManySetPreservesMonoSorted (ys xs : List Nat)
    (hx : brMonoSorted xs = true) : brMonoSorted (insertManySet ys xs) = true := by
  induction ys with
  | nil => exact hx
  | cons y ys' ih =>
      show brMonoSorted (insertSortedSet y (insertManySet ys' xs)) = true
      exact brInsertSortedSetPreservesMonoSorted y (insertManySet ys' xs) ih
theorem brMonoFixpoint (xs : List Nat) (h : brMonoSorted xs = true) : insertManySet xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      have hbelow : brMonoBelow a rest = true := csrAndTrueLeft _ _ h
      have hrest : brMonoSorted rest = true := csrAndTrueRight _ _ h
      show insertSortedSet a (insertManySet rest []) = a :: rest
      rw [ih hrest]; exact brMonoInsertFront a rest hbelow

/-- Monomial multiplication is variable-set UNION (idempotent). -/
def brMonoMul (m n : List Nat) : List Nat := insertManySet n m
theorem brMonoMulNilRight (m : List Nat) : brMonoMul m [] = m := rfl
theorem brMonoMulAssoc (m n p : List Nat) :
    brMonoMul (brMonoMul m n) p = brMonoMul m (brMonoMul n p) := by
  show insertManySet p (insertManySet n m) = insertManySet (insertManySet p n) m
  exact (insertManySetAssoc p n m).symm
theorem brMonoMulComm (m n : List Nat) (hm : brMonoSorted m = true) (hn : brMonoSorted n = true) :
    brMonoMul m n = brMonoMul n m := by
  show insertManySet n m = insertManySet m n
  have h := insertManySetComm n m []
  rw [brMonoFixpoint m hm, brMonoFixpoint n hn] at h
  exact h
theorem brMonoMulSorted (m n : List Nat) (hm : brMonoSorted m = true) :
    brMonoSorted (brMonoMul m n) = true := brInsertManySetPreservesMonoSorted n m hm
theorem brMonoMulSelfSingleton (c : Nat) : brMonoMul [c] [c] = [c] := by
  show insertSortedSet c [c] = [c]
  exact insertSortedSetEq c c [] (natBleRefl c) (natBleRefl c)

/-! ## The Zhegalkin normal form and its coefficient-XOR additive engine (no-drop, mirroring ℤ[X]) -/

/-- The normal form: `(monomial, F2-coefficient)` terms, sorted strictly by the imported `csrCompare`. -/
abbrev BrNF := List (List Nat × Bool)

/-- Insert one term into a sorted normal form, XOR-ing coefficients on an equal monomial (never dropping). -/
def brInsertTerm : (List Nat × Bool) → BrNF → BrNF
  | term, [] => [term]
  | (m, c), (p, e) :: rest =>
      match csrCompare m p with
      | CsrMonoOrd.eq => (p, brCoeffXor e c) :: rest
      | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
      | CsrMonoOrd.gt => (p, e) :: brInsertTerm (m, c) rest
theorem brInsertTermNil (m : List Nat) (c : Bool) : brInsertTerm (m, c) [] = [(m, c)] := rfl
theorem brInsertTermEqE (m : List Nat) (c : Bool) (p : List Nat) (e : Bool) (rest : BrNF)
    (h : csrCompare m p = CsrMonoOrd.eq) :
    brInsertTerm (m, c) ((p, e) :: rest) = (p, brCoeffXor e c) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, brCoeffXor e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: brInsertTerm (m, c) rest) = (p, brCoeffXor e c) :: rest
  rw [h]
theorem brInsertTermLtE (m : List Nat) (c : Bool) (p : List Nat) (e : Bool) (rest : BrNF)
    (h : csrCompare m p = CsrMonoOrd.lt) :
    brInsertTerm (m, c) ((p, e) :: rest) = (m, c) :: (p, e) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, brCoeffXor e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: brInsertTerm (m, c) rest) = (m, c) :: (p, e) :: rest
  rw [h]
theorem brInsertTermGtE (m : List Nat) (c : Bool) (p : List Nat) (e : Bool) (rest : BrNF)
    (h : csrCompare m p = CsrMonoOrd.gt) :
    brInsertTerm (m, c) ((p, e) :: rest) = (p, e) :: brInsertTerm (m, c) rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, brCoeffXor e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: brInsertTerm (m, c) rest) = (p, e) :: brInsertTerm (m, c) rest
  rw [h]

/-- ★ The crux commutation: two term-insertions commute (permutation-invariance of the XOR merge).
Structurally identical to the ℤ[X] sibling's `fcrInsertTermComm`, with `Bool` coefficient xor. -/
theorem brInsertTermComm (m : List Nat) (c : Bool) (n : List Nat) (d : Bool) (P : BrNF) :
    brInsertTerm (m, c) (brInsertTerm (n, d) P)
      = brInsertTerm (n, d) (brInsertTerm (m, c) P) := by
  induction P with
  | nil =>
      cases hmn : csrCompare m n with
      | eq =>
          have hmeqn : m = n := csrCompareEq_of m n hmn
          have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
          rw [brInsertTermNil n d, brInsertTermNil m c,
              brInsertTermEqE m c n d [] hmn, brInsertTermEqE n d m c [] hnm, hmeqn,
              brCoeffXorComm d c]
      | lt =>
          have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
          rw [brInsertTermNil n d, brInsertTermNil m c,
              brInsertTermLtE m c n d [] hmn, brInsertTermGtE n d m c [] hnm, brInsertTermNil n d]
      | gt =>
          have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn
          rw [brInsertTermNil n d, brInsertTermNil m c,
              brInsertTermGtE m c n d [] hmn, brInsertTermNil m c, brInsertTermLtE n d m c [] hnm]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [brInsertTermEqE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [brInsertTermEqE m c p (brCoeffXor e d) rest hmp, brInsertTermEqE m c p e rest hmp,
                  brInsertTermEqE n d p (brCoeffXor e c) rest hnp, brCoeffXorRightComm e d c]
          | lt =>
              have hpm : csrCompare p m = CsrMonoOrd.gt := csrCompareSwapLt m p hmp
              have hnm : csrCompare n m = CsrMonoOrd.gt := by rw [hnp_eq]; exact hpm
              rw [brInsertTermLtE m c p (brCoeffXor e d) rest hmp, brInsertTermLtE m c p e rest hmp,
                  brInsertTermGtE n d m c ((p, e) :: rest) hnm, brInsertTermEqE n d p e rest hnp]
          | gt =>
              rw [brInsertTermGtE m c p (brCoeffXor e d) rest hmp, brInsertTermGtE m c p e rest hmp,
                  brInsertTermEqE n d p e (brInsertTerm (m, c) rest) hnp]
      | lt =>
          rw [brInsertTermLtE n d p e rest hnp]
          cases hmn : csrCompare m n with
          | eq =>
              have hmeqn : m = n := csrCompareEq_of m n hmn
              have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
              have hmp : csrCompare m p = CsrMonoOrd.lt := by rw [hmeqn]; exact hnp
              rw [brInsertTermEqE m c n d ((p, e) :: rest) hmn, brInsertTermLtE m c p e rest hmp,
                  brInsertTermEqE n d m c ((p, e) :: rest) hnm, hmeqn, brCoeffXorComm d c]
          | lt =>
              have hmp : csrCompare m p = CsrMonoOrd.lt := csrCompareTransLt m n p hmn hnp
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [brInsertTermLtE m c n d ((p, e) :: rest) hmn, brInsertTermLtE m c p e rest hmp,
                  brInsertTermGtE n d m c ((p, e) :: rest) hnm, brInsertTermLtE n d p e rest hnp]
          | gt =>
              have hmn_gt : csrCompare m n = CsrMonoOrd.gt := hmn
              rw [brInsertTermGtE m c n d ((p, e) :: rest) hmn]
              cases hmp : csrCompare m p with
              | eq =>
                  rw [brInsertTermEqE m c p e rest hmp,
                      brInsertTermLtE n d p (brCoeffXor e c) rest hnp]
              | lt =>
                  have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn_gt
                  rw [brInsertTermLtE m c p e rest hmp,
                      brInsertTermLtE n d m c ((p, e) :: rest) hnm]
              | gt =>
                  rw [brInsertTermGtE m c p e rest hmp,
                      brInsertTermLtE n d p e (brInsertTerm (m, c) rest) hnp]
      | gt =>
          rw [brInsertTermGtE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [brInsertTermEqE m c p e (brInsertTerm (n, d) rest) hmp,
                  brInsertTermEqE m c p e rest hmp,
                  brInsertTermGtE n d p (brCoeffXor e c) rest hnp]
          | lt =>
              have hpn : csrCompare p n = CsrMonoOrd.lt := csrCompareSwapGt n p hnp
              have hmn : csrCompare m n = CsrMonoOrd.lt := csrCompareTransLt m p n hmp hpn
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [brInsertTermLtE m c p e (brInsertTerm (n, d) rest) hmp,
                  brInsertTermLtE m c p e rest hmp,
                  brInsertTermGtE n d m c ((p, e) :: rest) hnm,
                  brInsertTermGtE n d p e rest hnp]
          | gt =>
              rw [brInsertTermGtE m c p e (brInsertTerm (n, d) rest) hmp,
                  brInsertTermGtE m c p e rest hmp,
                  brInsertTermGtE n d p e (brInsertTerm (m, c) rest) hnp, ih]

/-- The additive XOR merge: insert every term of the first list into the second. -/
def brMergeXor : BrNF → BrNF → BrNF
  | [], b => b
  | t :: a', b => brInsertTerm t (brMergeXor a' b)
theorem brMergeXorNilLeft (b : BrNF) : brMergeXor [] b = b := rfl
theorem brMergeXorCons (t : List Nat × Bool) (a' b : BrNF) :
    brMergeXor (t :: a') b = brInsertTerm t (brMergeXor a' b) := rfl
theorem brInsertTerm_mergeXor (t : List Nat × Bool) (a b : BrNF) :
    brInsertTerm t (brMergeXor a b) = brMergeXor a (brInsertTerm t b) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      obtain ⟨um, uc⟩ := u
      obtain ⟨tm, tc⟩ := t
      show brInsertTerm (tm, tc) (brInsertTerm (um, uc) (brMergeXor a' b))
        = brMergeXor ((um, uc) :: a') (brInsertTerm (tm, tc) b)
      rw [brMergeXorCons, brInsertTermComm tm tc um uc (brMergeXor a' b), ih]
/-- Inserting the same monomial twice XORs the two coefficients. -/
theorem brInsertTermMergeSame (m : List Nat) (c1 c2 : Bool) (Z : BrNF) :
    brInsertTerm (m, c1) (brInsertTerm (m, c2) Z) = brInsertTerm (m, brCoeffXor c2 c1) Z := by
  induction Z with
  | nil =>
      rw [brInsertTermNil m c2, brInsertTermEqE m c1 m c2 [] (csrCompareRefl m),
          brInsertTermNil m (brCoeffXor c2 c1)]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          rw [brInsertTermEqE m c2 p e rest hmp, brInsertTermEqE m c1 p (brCoeffXor e c2) rest hmp,
              brInsertTermEqE m (brCoeffXor c2 c1) p e rest hmp, brCoeffXorAssoc e c2 c1]
      | lt =>
          rw [brInsertTermLtE m c2 p e rest hmp, brInsertTermEqE m c1 m c2 ((p, e) :: rest)
                (csrCompareRefl m), brInsertTermLtE m (brCoeffXor c2 c1) p e rest hmp]
      | gt =>
          rw [brInsertTermGtE m c2 p e rest hmp, brInsertTermGtE m c1 p e
                (brInsertTerm (m, c2) rest) hmp, brInsertTermGtE m (brCoeffXor c2 c1) p e rest hmp, ih]
/-- Pulling an insertion out of the left list of a merge. -/
theorem brMergeXorInsertTermLeft (u : List Nat × Bool) (Y c : BrNF) :
    brMergeXor (brInsertTerm u Y) c = brInsertTerm u (brMergeXor Y c) := by
  obtain ⟨um, uc⟩ := u
  induction Y with
  | nil => rfl
  | cons head Y' ih =>
      obtain ⟨v, ve⟩ := head
      cases huv : csrCompare um v with
      | eq =>
          have hum_eq : um = v := csrCompareEq_of um v huv
          rw [brInsertTermEqE um uc v ve Y' huv, brMergeXorCons,
              brMergeXorCons (v, ve) Y' c, hum_eq,
              brInsertTermMergeSame v uc ve (brMergeXor Y' c)]
      | lt =>
          rw [brInsertTermLtE um uc v ve Y' huv, brMergeXorCons, brMergeXorCons (v, ve) Y' c]
      | gt =>
          rw [brInsertTermGtE um uc v ve Y' huv, brMergeXorCons (v, ve) (brInsertTerm (um, uc) Y') c,
              brMergeXorCons (v, ve) Y' c, ih,
              brInsertTermComm v ve um uc (brMergeXor Y' c)]
theorem brMergeXorAssoc (a b c : BrNF) :
    brMergeXor (brMergeXor a b) c = brMergeXor a (brMergeXor b c) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show brMergeXor (brInsertTerm u (brMergeXor a' b)) c
        = brInsertTerm u (brMergeXor a' (brMergeXor b c))
      rw [brMergeXorInsertTermLeft u (brMergeXor a' b) c, ih]
theorem brMergeXorSwap (a b acc : BrNF) :
    brMergeXor a (brMergeXor b acc) = brMergeXor b (brMergeXor a acc) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show brInsertTerm u (brMergeXor a' (brMergeXor b acc))
        = brMergeXor b (brInsertTerm u (brMergeXor a' acc))
      rw [ih, brInsertTerm_mergeXor u b (brMergeXor a' acc)]

/-! ## The strict-sortedness invariant on the normal form -/

def brBelowHead (m : List Nat) : BrNF → Bool
  | [] => true
  | (p, _) :: _ =>
      match csrCompare m p with
      | CsrMonoOrd.lt => true
      | CsrMonoOrd.eq => false
      | CsrMonoOrd.gt => false
def brNFSorted : BrNF → Bool
  | [] => true
  | (m, _) :: rest => brBelowHead m rest && brNFSorted rest
theorem brBelowHeadNil (m : List Nat) : brBelowHead m [] = true := rfl
theorem brBelowHeadConsTrue (m p : List Nat) (e : Bool) (rest : BrNF)
    (h : csrCompare m p = CsrMonoOrd.lt) : brBelowHead m ((p, e) :: rest) = true := by
  show (match csrCompare m p with
        | CsrMonoOrd.lt => true
        | CsrMonoOrd.eq => false
        | CsrMonoOrd.gt => false) = true
  rw [h]
theorem brBelowHeadConsLt (m p : List Nat) (e : Bool) (rest : BrNF)
    (h : brBelowHead m ((p, e) :: rest) = true) : csrCompare m p = CsrMonoOrd.lt := by
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
theorem brNFSortedCons (m : List Nat) (c : Bool) (rest : BrNF) :
    brNFSorted ((m, c) :: rest) = (brBelowHead m rest && brNFSorted rest) := rfl
theorem brBelowHeadInsert (q m : List Nat) (c : Bool) (B : BrNF)
    (hq : csrCompare q m = CsrMonoOrd.lt) (hB : brBelowHead q B = true) :
    brBelowHead q (brInsertTerm (m, c) B) = true := by
  cases B with
  | nil => exact brBelowHeadConsTrue q m c [] hq
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq => rw [brInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [brInsertTermLtE m c p e rest hmp]; exact brBelowHeadConsTrue q m c ((p, e) :: rest) hq
      | gt =>
          rw [brInsertTermGtE m c p e rest hmp]
          exact brBelowHeadConsTrue q p e (brInsertTerm (m, c) rest) (brBelowHeadConsLt q p e rest hB)
theorem brInsertPreservesSorted (m : List Nat) (c : Bool) (B : BrNF)
    (hB : brNFSorted B = true) : brNFSorted (brInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hbelow : brBelowHead p rest = true := csrAndTrueLeft _ _ hB
      have hrest : brNFSorted rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq => rw [brInsertTermEqE m c p e rest hmp]; exact hB
      | lt =>
          rw [brInsertTermLtE m c p e rest hmp, brNFSortedCons]
          exact csrAndIntro _ _ (brBelowHeadConsTrue m p e rest hmp) hB
      | gt =>
          rw [brInsertTermGtE m c p e rest hmp, brNFSortedCons]
          have hpm : csrCompare p m = CsrMonoOrd.lt := csrCompareSwapGt m p hmp
          exact csrAndIntro _ _
            (brBelowHeadInsert p m c rest hpm hbelow) (ih hrest)
theorem brInsertFront (m : List Nat) (c : Bool) (B : BrNF) (h : brBelowHead m B = true) :
    brInsertTerm (m, c) B = (m, c) :: B := by
  cases B with
  | nil => rfl
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      exact brInsertTermLtE m c p e rest (brBelowHeadConsLt m p e rest h)
theorem brMergeXorNilRight (A : BrNF) (hA : brNFSorted A = true) : brMergeXor A [] = A := by
  induction A with
  | nil => rfl
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      have hbelow : brBelowHead m a' = true := csrAndTrueLeft _ _ hA
      have hrest : brNFSorted a' = true := csrAndTrueRight _ _ hA
      show brInsertTerm (m, c) (brMergeXor a' []) = (m, c) :: a'
      rw [ih hrest, brInsertFront m c a' hbelow]
theorem brMergeXorComm (A B : BrNF) (hA : brNFSorted A = true) (hB : brNFSorted B = true) :
    brMergeXor A B = brMergeXor B A := by
  have h := brMergeXorSwap A B []
  rw [brMergeXorNilRight B hB, brMergeXorNilRight A hA] at h
  exact h
theorem brMergeXorPreservesSorted (A B : BrNF) (hB : brNFSorted B = true) :
    brNFSorted (brMergeXor A B) = true := by
  induction A with
  | nil => exact hB
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      show brNFSorted (brInsertTerm (m, c) (brMergeXor a' B)) = true
      exact brInsertPreservesSorted m c (brMergeXor a' B) ih

/-! ## The multiplicative convolution (monomial set-union × coefficient `and`) -/

/-- A single term `(m, c)` times a polynomial: monomial product is the set-union `brMonoMul`, coefficient
product is `brCoeffAnd`. -/
def brTermMul (m : List Nat) (c : Bool) : BrNF → BrNF
  | [] => []
  | (n, d) :: rest => brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c rest)
/-- The Cauchy convolution of two polynomials. -/
def brMulConvolve : BrNF → BrNF → BrNF
  | [], _ => []
  | (m, c) :: rest, b => brMergeXor (brTermMul m c b) (brMulConvolve rest b)
theorem brTermMulNil (m : List Nat) (c : Bool) : brTermMul m c [] = [] := rfl
theorem brTermMulCons (m : List Nat) (c : Bool) (n : List Nat) (d : Bool) (rest : BrNF) :
    brTermMul m c ((n, d) :: rest) = brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c rest) := rfl
theorem brMulConvolveNil (b : BrNF) : brMulConvolve [] b = [] := rfl
theorem brMulConvolveCons (m : List Nat) (c : Bool) (rest b : BrNF) :
    brMulConvolve ((m, c) :: rest) b = brMergeXor (brTermMul m c b) (brMulConvolve rest b) := rfl
theorem brTermMulSorted (m : List Nat) (c : Bool) (B : BrNF) :
    brNFSorted (brTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show brNFSorted (brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c rest)) = true
      exact brInsertPreservesSorted (brMonoMul m n) (brCoeffAnd c d) (brTermMul m c rest) ih
theorem brMulConvolveSorted (A B : BrNF) : brNFSorted (brMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show brNFSorted (brMergeXor (brTermMul m c B) (brMulConvolve rest B)) = true
      exact brMergeXorPreservesSorted (brTermMul m c B) (brMulConvolve rest B) ih
/-- termMul commutes with a single insertion (coefficients distribute via `brCoeffAndXorRight`). -/
theorem brTermMul_insertTerm (m : List Nat) (c : Bool) (n : List Nat) (d : Bool) (B : BrNF) :
    brTermMul m c (brInsertTerm (n, d) B)
      = brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [brInsertTermEqE n d p e rest hnp, brTermMulCons m c p (brCoeffXor e d) rest,
              brTermMulCons m c p e rest, hnp_eq,
              brInsertTermMergeSame (brMonoMul m p) (brCoeffAnd c d) (brCoeffAnd c e)
                (brTermMul m c rest), brCoeffAndXorRight c e d]
      | lt =>
          rw [brInsertTermLtE n d p e rest hnp, brTermMulCons m c n d ((p, e) :: rest),
              brTermMulCons m c p e rest]
      | gt =>
          rw [brInsertTermGtE n d p e rest hnp, brTermMulCons m c p e (brInsertTerm (n, d) rest),
              ih, brTermMulCons m c p e rest,
              brInsertTermComm (brMonoMul m p) (brCoeffAnd c e) (brMonoMul m n) (brCoeffAnd c d)
                (brTermMul m c rest)]
theorem brTermMul_merge (m : List Nat) (c : Bool) (B C : BrNF) :
    brTermMul m c (brMergeXor B C) = brMergeXor (brTermMul m c B) (brTermMul m c C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show brTermMul m c (brInsertTerm (n, d) (brMergeXor B' C))
        = brMergeXor (brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c B')) (brTermMul m c C)
      rw [brTermMul_insertTerm m c n d (brMergeXor B' C), ih,
          brMergeXorInsertTermLeft (brMonoMul m n, brCoeffAnd c d) (brTermMul m c B') (brTermMul m c C)]
theorem brMulConvolveAnnihil (A : BrNF) : brMulConvolve A [] = [] := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show brMergeXor (brTermMul m c []) (brMulConvolve rest []) = []
      rw [brTermMulNil m c, brMergeXorNilLeft, ih]
/-- Rearrange a merge of four sorted NFs, swapping the inner two. -/
theorem brMergeXor4Swap (a b c d : BrNF)
    (hb : brNFSorted b = true) (hc : brNFSorted c = true) :
    brMergeXor (brMergeXor a b) (brMergeXor c d)
      = brMergeXor (brMergeXor a c) (brMergeXor b d) := by
  rw [brMergeXorAssoc a b (brMergeXor c d), ← brMergeXorAssoc b c d,
      brMergeXorComm b c hb hc, brMergeXorAssoc c b d, ← brMergeXorAssoc a c (brMergeXor b d)]
/-- ★ left distributivity: `A · (B + C) = A·B + A·C`. -/
theorem brMulConvolve_leftDistrib (A B C : BrNF) :
    brMulConvolve A (brMergeXor B C)
      = brMergeXor (brMulConvolve A B) (brMulConvolve A C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show brMergeXor (brTermMul m c (brMergeXor B C)) (brMulConvolve A' (brMergeXor B C))
        = brMergeXor (brMergeXor (brTermMul m c B) (brMulConvolve A' B))
            (brMergeXor (brTermMul m c C) (brMulConvolve A' C))
      rw [brTermMul_merge m c B C, ih]
      exact brMergeXor4Swap (brTermMul m c B) (brTermMul m c C) (brMulConvolve A' B)
        (brMulConvolve A' C) (brTermMulSorted m c C) (brMulConvolveSorted A' B)
/-- termMul distributes over a coefficient XOR. -/
theorem brTermMul_coeffXor (m : List Nat) (c1 c2 : Bool) (Z : BrNF) :
    brTermMul m (brCoeffXor c1 c2) Z = brMergeXor (brTermMul m c1 Z) (brTermMul m c2 Z) := by
  induction Z with
  | nil => rfl
  | cons head Z' ih =>
      obtain ⟨n, d⟩ := head
      show brInsertTerm (brMonoMul m n, brCoeffAnd (brCoeffXor c1 c2) d) (brTermMul m (brCoeffXor c1 c2) Z')
        = brMergeXor (brInsertTerm (brMonoMul m n, brCoeffAnd c1 d) (brTermMul m c1 Z'))
            (brInsertTerm (brMonoMul m n, brCoeffAnd c2 d) (brTermMul m c2 Z'))
      rw [brMergeXorInsertTermLeft (brMonoMul m n, brCoeffAnd c1 d) (brTermMul m c1 Z')
            (brInsertTerm (brMonoMul m n, brCoeffAnd c2 d) (brTermMul m c2 Z')),
          ← brInsertTerm_mergeXor (brMonoMul m n, brCoeffAnd c2 d) (brTermMul m c1 Z') (brTermMul m c2 Z'),
          brInsertTermMergeSame (brMonoMul m n) (brCoeffAnd c1 d) (brCoeffAnd c2 d)
            (brMergeXor (brTermMul m c1 Z') (brTermMul m c2 Z')),
          ih, brCoeffXorAndRight c1 c2 d, brCoeffXorComm (brCoeffAnd c1 d) (brCoeffAnd c2 d)]
/-- convolving after one insertion into the first argument. -/
theorem brConvolve_insertTermLeft (m : List Nat) (c : Bool) (W Z : BrNF) :
    brMulConvolve (brInsertTerm (m, c) W) Z
      = brMergeXor (brTermMul m c Z) (brMulConvolve W Z) := by
  induction W with
  | nil => rfl
  | cons head W' ih =>
      obtain ⟨p, g⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [brInsertTermEqE m c p g W' hmp, brMulConvolveCons p (brCoeffXor g c) W' Z,
              brMulConvolveCons p g W' Z, hmeqp,
              brTermMul_coeffXor p g c Z,
              brMergeXorAssoc (brTermMul p g Z) (brTermMul p c Z) (brMulConvolve W' Z),
              brMergeXorSwap (brTermMul p g Z) (brTermMul p c Z) (brMulConvolve W' Z)]
      | lt =>
          rw [brInsertTermLtE m c p g W' hmp, brMulConvolveCons m c ((p, g) :: W') Z]
      | gt =>
          rw [brInsertTermGtE m c p g W' hmp,
              brMulConvolveCons p g (brInsertTerm (m, c) W') Z, ih,
              brMulConvolveCons p g W' Z,
              brMergeXorSwap (brTermMul p g Z) (brTermMul m c Z) (brMulConvolve W' Z)]
/-- ★ right distributivity: `(X + Y) · Z = X·Z + Y·Z`. -/
theorem brMulConvolve_rightDistrib (X Y Z : BrNF) :
    brMulConvolve (brMergeXor X Y) Z
      = brMergeXor (brMulConvolve X Z) (brMulConvolve Y Z) := by
  induction X with
  | nil => rfl
  | cons head X' ih =>
      obtain ⟨m, c⟩ := head
      show brMulConvolve (brInsertTerm (m, c) (brMergeXor X' Y)) Z
        = brMergeXor (brMergeXor (brTermMul m c Z) (brMulConvolve X' Z)) (brMulConvolve Y Z)
      rw [brConvolve_insertTermLeft m c (brMergeXor X' Y) Z, ih,
          brMergeXorAssoc (brTermMul m c Z) (brMulConvolve X' Z) (brMulConvolve Y Z)]
/-- termMul composition: `(m ⊎ n)·(c ∧ d)` applied to `C` equals scaling by `(m,c)` then `(n,d)`. -/
theorem brTermMul_compose (m : List Nat) (c : Bool) (n : List Nat) (d : Bool) (C : BrNF) :
    brTermMul (brMonoMul m n) (brCoeffAnd c d) C = brTermMul m c (brTermMul n d C) := by
  induction C with
  | nil => rfl
  | cons head C' ih =>
      obtain ⟨p, f⟩ := head
      show brInsertTerm (brMonoMul (brMonoMul m n) p, brCoeffAnd (brCoeffAnd c d) f)
            (brTermMul (brMonoMul m n) (brCoeffAnd c d) C')
        = brTermMul m c (brInsertTerm (brMonoMul n p, brCoeffAnd d f) (brTermMul n d C'))
      rw [brTermMul_insertTerm m c (brMonoMul n p) (brCoeffAnd d f) (brTermMul n d C'), ih,
          brMonoMulAssoc m n p, brCoeffAndAssoc c d f]
/-- convolving a termMul equals termMul of a convolve. -/
theorem brTermMul_convolve (m : List Nat) (c : Bool) (B C : BrNF) :
    brMulConvolve (brTermMul m c B) C = brTermMul m c (brMulConvolve B C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show brMulConvolve (brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c B')) C
        = brTermMul m c (brMergeXor (brTermMul n d C) (brMulConvolve B' C))
      rw [brConvolve_insertTermLeft (brMonoMul m n) (brCoeffAnd c d) (brTermMul m c B') C, ih,
          brTermMul_merge m c (brTermMul n d C) (brMulConvolve B' C),
          brTermMul_compose m c n d C]
/-- ★ associativity of the convolution: `(A·B)·C = A·(B·C)`. -/
theorem brMulConvolveAssoc (A B C : BrNF) :
    brMulConvolve (brMulConvolve A B) C = brMulConvolve A (brMulConvolve B C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show brMulConvolve (brMergeXor (brTermMul m c B) (brMulConvolve A' B)) C
        = brMergeXor (brTermMul m c (brMulConvolve B C)) (brMulConvolve A' (brMulConvolve B C))
      rw [brMulConvolve_rightDistrib (brTermMul m c B) (brMulConvolve A' B) C, ih,
          brTermMul_convolve m c B C]

/-! ## Monomial-sortedness of every term, and convolution commutativity / unit -/

def brNFMonoSorted : BrNF → Bool
  | [] => true
  | (m, _) :: rest => brMonoSorted m && brNFMonoSorted rest
theorem brNFMonoSortedCons (m : List Nat) (c : Bool) (rest : BrNF) :
    brNFMonoSorted ((m, c) :: rest) = (brMonoSorted m && brNFMonoSorted rest) := rfl
theorem brInsertTermMonoSorted (m : List Nat) (c : Bool) (B : BrNF)
    (hm : brMonoSorted m = true) (hB : brNFMonoSorted B = true) :
    brNFMonoSorted (brInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rw [brInsertTermNil m c, brNFMonoSortedCons]; exact csrAndIntro _ _ hm rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hp : brMonoSorted p = true := csrAndTrueLeft _ _ hB
      have hrest : brNFMonoSorted rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq => rw [brInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [brInsertTermLtE m c p e rest hmp, brNFMonoSortedCons]; exact csrAndIntro _ _ hm hB
      | gt =>
          rw [brInsertTermGtE m c p e rest hmp, brNFMonoSortedCons]
          exact csrAndIntro _ _ hp (ih hrest)
theorem brMergeXorMonoSorted (A B : BrNF) (hA : brNFMonoSorted A = true)
    (hB : brNFMonoSorted B = true) : brNFMonoSorted (brMergeXor A B) = true := by
  induction A with
  | nil => exact hB
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hm : brMonoSorted m = true := csrAndTrueLeft _ _ hA
      have hA' : brNFMonoSorted A' = true := csrAndTrueRight _ _ hA
      show brNFMonoSorted (brInsertTerm (m, c) (brMergeXor A' B)) = true
      exact brInsertTermMonoSorted m c (brMergeXor A' B) hm (ih hA')
theorem brTermMulMonoSorted (m : List Nat) (c : Bool) (B : BrNF) (hm : brMonoSorted m = true) :
    brNFMonoSorted (brTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show brNFMonoSorted (brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c rest)) = true
      exact brInsertTermMonoSorted (brMonoMul m n) (brCoeffAnd c d) (brTermMul m c rest)
        (brMonoMulSorted m n hm) ih
theorem brMulConvolveMonoSorted (A B : BrNF) (hA : brNFMonoSorted A = true)
    (_hB : brNFMonoSorted B = true) : brNFMonoSorted (brMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hm : brMonoSorted m = true := csrAndTrueLeft _ _ hA
      have hA' : brNFMonoSorted A' = true := csrAndTrueRight _ _ hA
      show brNFMonoSorted (brMergeXor (brTermMul m c B) (brMulConvolve A' B)) = true
      exact brMergeXorMonoSorted (brTermMul m c B) (brMulConvolve A' B)
        (brTermMulMonoSorted m c B hm) (ih hA')
/-- termMul equals convolving with a single-term poly (needs sorted monomials for `brMonoMul` comm). -/
theorem brTermMulEqConvolveSingle (m : List Nat) (c : Bool) (hm : brMonoSorted m = true) :
    (B : BrNF) → brNFMonoSorted B = true → brTermMul m c B = brMulConvolve B [(m, c)]
  | [], _ => rfl
  | (n, d) :: B', hB => by
      have hn : brMonoSorted n = true := csrAndTrueLeft _ _ hB
      have hB' : brNFMonoSorted B' = true := csrAndTrueRight _ _ hB
      have ih := brTermMulEqConvolveSingle m c hm B' hB'
      show brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c B')
        = brMergeXor (brTermMul n d [(m, c)]) (brMulConvolve B' [(m, c)])
      rw [brTermMulCons n d m c [], brTermMulNil n d,
          brMergeXorInsertTermLeft (brMonoMul n m, brCoeffAnd d c) [] (brMulConvolve B' [(m, c)]),
          brMergeXorNilLeft, ← ih, brMonoMulComm m n hm hn, brCoeffAndComm c d]
/-- ★ commutativity of the convolution (needs sorted first arg + sorted monomials). -/
theorem brMulConvolveComm : (A B : BrNF) → brNFSorted A = true → brNFMonoSorted A = true →
    brNFMonoSorted B = true → brMulConvolve A B = brMulConvolve B A
  | [], B, _, _, _ => (brMulConvolveAnnihil B).symm
  | (m, c) :: A', B, hAs, hAm, hBm => by
      have hbelow : brBelowHead m A' = true := csrAndTrueLeft _ _ hAs
      have hAs' : brNFSorted A' = true := csrAndTrueRight _ _ hAs
      have hm : brMonoSorted m = true := csrAndTrueLeft _ _ hAm
      have hAm' : brNFMonoSorted A' = true := csrAndTrueRight _ _ hAm
      have ih := brMulConvolveComm A' B hAs' hAm' hBm
      show brMergeXor (brTermMul m c B) (brMulConvolve A' B) = brMulConvolve B ((m, c) :: A')
      rw [brTermMulEqConvolveSingle m c hm B hBm, ih,
          ← brMulConvolve_leftDistrib B [(m, c)] A', brMergeXorCons (m, c) [] A',
          brMergeXorNilLeft, brInsertFront m c A' hbelow]
/-- ★ multiplicative unit: `A · [([], true)] = A` for a sorted NF. -/
theorem brMulConvolveUnit : (A : BrNF) → brNFSorted A = true → brMulConvolve A [([], true)] = A
  | [], _ => rfl
  | (m, c) :: A', hAs => by
      have hbelow : brBelowHead m A' = true := csrAndTrueLeft _ _ hAs
      have hAs' : brNFSorted A' = true := csrAndTrueRight _ _ hAs
      have ih := brMulConvolveUnit A' hAs'
      show brMergeXor (brTermMul m c [([], true)]) (brMulConvolve A' [([], true)]) = (m, c) :: A'
      rw [brTermMulCons m c [] true [], brTermMulNil m c, brMonoMulNilRight m, brCoeffAndTrueRight c,
          brMergeXorInsertTermLeft (m, c) [] (brMulConvolve A' [([], true)]), brMergeXorNilLeft,
          ih, brInsertFront m c A' hbelow]

/-! ## The all-absent predicate and its closure lemmas -/

/-- Every coefficient is absent (`false`).  The single-list structural check underlying the decision. -/
def brNFAllZero : BrNF → Bool
  | [] => true
  | (_, c) :: rest => brCoeffIsZero c && brNFAllZero rest
theorem brNFAllZeroCons (m : List Nat) (c : Bool) (rest : BrNF) :
    brNFAllZero ((m, c) :: rest) = (brCoeffIsZero c && brNFAllZero rest) := rfl
theorem brInsertTermAllZero (m : List Nat) (c : Bool) (B : BrNF)
    (hc : brCoeffIsZero c = true) (hB : brNFAllZero B = true) :
    brNFAllZero (brInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rw [brInsertTermNil m c, brNFAllZeroCons]; exact csrAndIntro _ _ hc rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have he : brCoeffIsZero e = true := csrAndTrueLeft _ _ hB
      have hrest : brNFAllZero rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq =>
          rw [brInsertTermEqE m c p e rest hmp, brNFAllZeroCons]
          exact csrAndIntro _ _ (brCoeffXorZeroValued e c he hc) hrest
      | lt =>
          rw [brInsertTermLtE m c p e rest hmp, brNFAllZeroCons]
          exact csrAndIntro _ _ hc hB
      | gt =>
          rw [brInsertTermGtE m c p e rest hmp, brNFAllZeroCons]
          exact csrAndIntro _ _ he (ih hrest)
theorem brMergeXorAllZero (A B : BrNF) (hA : brNFAllZero A = true) (hB : brNFAllZero B = true) :
    brNFAllZero (brMergeXor A B) = true := by
  induction A with
  | nil => exact hB
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hc : brCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hA' : brNFAllZero A' = true := csrAndTrueRight _ _ hA
      show brNFAllZero (brInsertTerm (m, c) (brMergeXor A' B)) = true
      exact brInsertTermAllZero m c (brMergeXor A' B) hc (ih hA')

/-! ## The `brEvalCross` semantic model: the per-monomial F2 coefficient -/

/-- The coefficient contributed by a term at a queried monomial: `d` on a match, `false` otherwise. -/
def brCondCoeff : Bool → Bool → Bool
  | true, d => d
  | false, _ => false
theorem brCondCoeffTrue (d : Bool) : brCondCoeff true d = d := rfl
theorem brCondCoeffFalse (d : Bool) : brCondCoeff false d = false := rfl
theorem brCondCoeffZero (b : Bool) (c : Bool) (hc : brCoeffIsZero c = true) :
    brCoeffIsZero (brCondCoeff b c) = true := by
  cases b with
  | true => exact hc
  | false => rfl
/-- A monomial `m` distinct from `q` (witnessed by `csrCompare m q = lt`) has `csrNatListEq m q = false`. -/
theorem brMonoEqFalseOfLt (m q : List Nat) (h : csrCompare m q = CsrMonoOrd.lt) :
    csrNatListEq m q = false := by
  cases hb : csrNatListEq m q with
  | false => rfl
  | true =>
      have hmq : m = q := csrNatListEq_eq m q hb
      rw [csrCompareOfEq m q hmq] at h
      exact CsrMonoOrd.noConfusion h
/-- The per-monomial F2 coefficient of a normal form. -/
def brEvalCross (m : List Nat) : BrNF → Bool
  | [] => false
  | (p, c) :: rest => brCoeffXor (brCondCoeff (csrNatListEq m p) c) (brEvalCross m rest)
theorem brEvalCrossNil (m : List Nat) : brEvalCross m [] = false := rfl
theorem brEvalCrossCons (m p : List Nat) (c : Bool) (rest : BrNF) :
    brEvalCross m ((p, c) :: rest) = brCoeffXor (brCondCoeff (csrNatListEq m p) c) (brEvalCross m rest) :=
  rfl
theorem brEvalCross_insertTerm (m n : List Nat) (d : Bool) (B : BrNF) :
    brEvalCross m (brInsertTerm (n, d) B)
      = brCoeffXor (brCondCoeff (csrNatListEq m n) d) (brEvalCross m B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hn_eq : n = p := csrCompareEq_of n p hnp
          rw [brInsertTermEqE n d p e rest hnp, brEvalCrossCons, brEvalCrossCons, hn_eq]
          cases hmp : csrNatListEq m p with
          | true =>
              rw [brCondCoeffTrue, brCondCoeffTrue, brCondCoeffTrue,
                  brCoeffXorAssoc e d (brEvalCross m rest), brCoeffXorSwap13 e d (brEvalCross m rest)]
          | false =>
              rw [brCondCoeffFalse, brCondCoeffFalse, brCondCoeffFalse,
                  brCoeffXorFalseLeft, brCoeffXorFalseLeft]
      | lt =>
          rw [brInsertTermLtE n d p e rest hnp, brEvalCrossCons]
      | gt =>
          rw [brInsertTermGtE n d p e rest hnp, brEvalCrossCons, ih, brEvalCrossCons]
          exact brCoeffXorSwap13 (brCondCoeff (csrNatListEq m p) e)
            (brCondCoeff (csrNatListEq m n) d) (brEvalCross m rest)
theorem brEvalCross_mergeXor (m : List Nat) (A B : BrNF) :
    brEvalCross m (brMergeXor A B) = brCoeffXor (brEvalCross m A) (brEvalCross m B) := by
  induction A with
  | nil => rw [brMergeXorNilLeft, brEvalCrossNil, brCoeffXorFalseLeft]
  | cons head A' ih =>
      obtain ⟨p, c⟩ := head
      show brEvalCross m (brInsertTerm (p, c) (brMergeXor A' B))
        = brCoeffXor (brCoeffXor (brCondCoeff (csrNatListEq m p) c) (brEvalCross m A')) (brEvalCross m B)
      rw [brEvalCross_insertTerm m p c (brMergeXor A' B), ih,
          brCoeffXorAssoc (brCondCoeff (csrNatListEq m p) c) (brEvalCross m A') (brEvalCross m B)]
theorem brAllZero_evalZero (m : List Nat) (W : BrNF) (hW : brNFAllZero W = true) :
    brCoeffIsZero (brEvalCross m W) = true := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      have hc : brCoeffIsZero c = true := csrAndTrueLeft _ _ hW
      have hrest : brNFAllZero rest = true := csrAndTrueRight _ _ hW
      rw [brEvalCrossCons]
      exact brCoeffXorZeroValued _ _ (brCondCoeffZero (csrNatListEq m p) c hc) (ih hrest)
theorem brEvalBelowZero (m : List Nat) (W : BrNF) (hbelow : brBelowHead m W = true)
    (hsorted : brNFSorted W = true) : brEvalCross m W = false := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨q, e⟩ := head
      have hmq : csrCompare m q = CsrMonoOrd.lt := brBelowHeadConsLt m q e rest hbelow
      have hmqEq : csrNatListEq m q = false := brMonoEqFalseOfLt m q hmq
      have hqbelow : brBelowHead q rest = true := csrAndTrueLeft _ _ hsorted
      have hrest : brNFSorted rest = true := csrAndTrueRight _ _ hsorted
      have hmrest : brBelowHead m rest = true := by
        cases rest with
        | nil => rfl
        | cons head2 rest2 =>
            obtain ⟨r, f⟩ := head2
            have hqr : csrCompare q r = CsrMonoOrd.lt := brBelowHeadConsLt q r f rest2 hqbelow
            exact brBelowHeadConsTrue m r f rest2 (csrCompareTransLt m q r hmq hqr)
      rw [brEvalCrossCons, hmqEq, brCondCoeffFalse, brCoeffXorFalseLeft, ih hmrest hrest]
/-- The extensionality that inverts `brAllZero_evalZero` on sorted NFs. -/
theorem brSortedEvalZero_allZero (W : BrNF) (hsorted : brNFSorted W = true)
    (hzero : ∀ m, brCoeffIsZero (brEvalCross m W) = true) : brNFAllZero W = true := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      have hbelow : brBelowHead p rest = true := csrAndTrueLeft _ _ hsorted
      have hrest : brNFSorted rest = true := csrAndTrueRight _ _ hsorted
      have hevalPrest : brEvalCross p rest = false := brEvalBelowZero p rest hbelow hrest
      have hc : brCoeffIsZero c = true := by
        have h := hzero p
        rw [brEvalCrossCons, csrNatListEqRefl p, brCondCoeffTrue, hevalPrest, brCoeffXorFalseRight] at h
        exact h
      have hrestZero : ∀ mm, brCoeffIsZero (brEvalCross mm rest) = true := by
        intro mm
        cases hmp : csrNatListEq mm p with
        | true =>
            have hmeqp : mm = p := csrNatListEq_eq mm p hmp
            rw [hmeqp, hevalPrest]; rfl
        | false =>
            have h := hzero mm
            rw [brEvalCrossCons, hmp, brCondCoeffFalse, brCoeffXorFalseLeft] at h
            exact h
      rw [brNFAllZeroCons]
      exact csrAndIntro _ _ hc (ih hrest hrestZero)
/-- ★ The all-absent cancellation: if `mergeXor X Z` and `Z` are both all-absent (with `X` sorted), so is `X`. -/
theorem brMergeXorAllZeroCancel (X Z : BrNF) (hX : brNFSorted X = true)
    (hXZ : brNFAllZero (brMergeXor X Z) = true) (hZ : brNFAllZero Z = true) :
    brNFAllZero X = true := by
  apply brSortedEvalZero_allZero X hX
  intro m
  have hmerge : brCoeffIsZero (brEvalCross m (brMergeXor X Z)) = true := brAllZero_evalZero m _ hXZ
  rw [brEvalCross_mergeXor m X Z] at hmerge
  exact brCoeffXorCancelZero (brEvalCross m X) (brEvalCross m Z) hmerge (brAllZero_evalZero m Z hZ)
/-- ★ The F2 self-inverse: a polynomial XOR itself is all-absent (`x + x = 0`), read off `brEvalCross`. -/
theorem brMergeXorSelfAllZero (A : BrNF) (hA : brNFSorted A = true) :
    brNFAllZero (brMergeXor A A) = true := by
  apply brSortedEvalZero_allZero _ (brMergeXorPreservesSorted A A hA)
  intro m
  rw [brEvalCross_mergeXor m A A]
  exact brCoeffXorSelfZero (brEvalCross m A)

/-! ## Multiplying by an all-absent polynomial (for the multiplicative congruence) -/

theorem brTermMulCoeffZeroAllZero (m : List Nat) (c : Bool) (hc : brCoeffIsZero c = true) (B : BrNF) :
    brNFAllZero (brTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show brNFAllZero (brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c rest)) = true
      exact brInsertTermAllZero _ _ _ (brCoeffAndZeroValuedLeft c d hc) ih
theorem brTermMulRightAllZero (m : List Nat) (c : Bool) (B : BrNF) (hB : brNFAllZero B = true) :
    brNFAllZero (brTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      have hd : brCoeffIsZero d = true := csrAndTrueLeft _ _ hB
      have hrest : brNFAllZero rest = true := csrAndTrueRight _ _ hB
      show brNFAllZero (brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c rest)) = true
      exact brInsertTermAllZero _ _ _ (brCoeffAndZeroValuedRight c d hd) (ih hrest)
theorem brMulConvolveLeftAllZero (A B : BrNF) (hA : brNFAllZero A = true) :
    brNFAllZero (brMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hc : brCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hA' : brNFAllZero A' = true := csrAndTrueRight _ _ hA
      show brNFAllZero (brMergeXor (brTermMul m c B) (brMulConvolve A' B)) = true
      exact brMergeXorAllZero _ _ (brTermMulCoeffZeroAllZero m c hc B) (ih hA')
theorem brMulConvolveRightAllZero (A B : BrNF) (hB : brNFAllZero B = true) :
    brNFAllZero (brMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show brNFAllZero (brMergeXor (brTermMul m c B) (brMulConvolve A' B)) = true
      exact brMergeXorAllZero _ _ (brTermMulRightAllZero m c B hB) ih

/-! ## The decision equivalence `brNFEq` and its equivalence + congruence structure -/

/-- The F2 polynomial equality: two normal forms agree exactly when their XOR-difference is all-absent.
Because F2 negation is the identity (`−B = B`), the difference is simply `A + B`. -/
def brNFEq (A B : BrNF) : Bool := brNFAllZero (brMergeXor A B)
/-- ★ `brNFEq` is reflexive on a sorted NF — this IS the F2 self-inverse. -/
theorem brNFEqRefl (A : BrNF) (hA : brNFSorted A = true) : brNFEq A A = true :=
  brMergeXorSelfAllZero A hA
/-- Literal-equal (sorted) normal forms are `brNFEq`. -/
theorem brNFEqOfEq (A B : BrNF) (hB : brNFSorted B = true) (h : A = B) : brNFEq A B = true := by
  rw [h]; exact brNFEqRefl B hB
/-- `brNFEq` is symmetric on sorted NFs (via merge commutativity). -/
theorem brNFEqSymm (A B : BrNF) (hA : brNFSorted A = true) (hB : brNFSorted B = true)
    (h : brNFEq A B = true) : brNFEq B A = true := by
  show brNFAllZero (brMergeXor B A) = true
  rw [brMergeXorComm B A hB hA]; exact h
/-- ★ `brNFEq` is transitive on sorted NFs — routed through the all-absent cancellation. -/
theorem brNFEqTrans (A B C : BrNF) (_hA : brNFSorted A = true) (hB : brNFSorted B = true)
    (hC : brNFSorted C = true) (hAB : brNFEq A B = true) (hBC : brNFEq B C = true) :
    brNFEq A C = true := by
  have hrearr : brMergeXor (brMergeXor A B) (brMergeXor B C)
              = brMergeXor (brMergeXor A C) (brMergeXor B B) := by
    rw [brMergeXor4Swap A B B C hB hB, brMergeXor4Swap A C B B hC hB,
        brMergeXorComm B C hB hC]
  have hall : brNFAllZero (brMergeXor (brMergeXor A C) (brMergeXor B B)) = true := by
    rw [← hrearr]; exact brMergeXorAllZero _ _ hAB hBC
  exact brMergeXorAllZeroCancel (brMergeXor A C) (brMergeXor B B)
    (brMergeXorPreservesSorted A C hC) hall (brMergeXorSelfAllZero B hB)
/-- ★ `brNFEq` respects the additive merge. -/
theorem brNFEqMergeCongr (A A' B B' : BrNF) (hA' : brNFSorted A' = true) (hB : brNFSorted B = true)
    (hAA' : brNFEq A A' = true) (hBB' : brNFEq B B' = true) :
    brNFEq (brMergeXor A B) (brMergeXor A' B') = true := by
  show brNFAllZero (brMergeXor (brMergeXor A B) (brMergeXor A' B')) = true
  rw [brMergeXor4Swap A B A' B' hB hA']
  exact brMergeXorAllZero _ _ hAA' hBB'
/-- ★ `brNFEq` respects the multiplicative convolution. -/
theorem brNFEqMulCongr (A A' B B' : BrNF) (hAA' : brNFEq A A' = true) (hBB' : brNFEq B B' = true) :
    brNFEq (brMulConvolve A B) (brMulConvolve A' B') = true := by
  have step1 : brNFEq (brMulConvolve A B) (brMulConvolve A' B) = true := by
    show brNFAllZero (brMergeXor (brMulConvolve A B) (brMulConvolve A' B)) = true
    rw [← brMulConvolve_rightDistrib A A' B]
    exact brMulConvolveLeftAllZero (brMergeXor A A') B hAA'
  have step2 : brNFEq (brMulConvolve A' B) (brMulConvolve A' B') = true := by
    show brNFAllZero (brMergeXor (brMulConvolve A' B) (brMulConvolve A' B')) = true
    rw [← brMulConvolve_leftDistrib A' B B']
    exact brMulConvolveRightAllZero A' (brMergeXor B B') hBB'
  exact brNFEqTrans (brMulConvolve A B) (brMulConvolve A' B) (brMulConvolve A' B')
    (brMulConvolveSorted A B) (brMulConvolveSorted A' B) (brMulConvolveSorted A' B') step1 step2
/-- An all-absent (sorted) NF is `brNFEq` to the empty NF. -/
theorem brNFEqNil (X : BrNF) (hX : brNFSorted X = true) (hall : brNFAllZero X = true) :
    brNFEq X [] = true := by
  show brNFAllZero (brMergeXor X []) = true
  rw [brMergeXorNilRight X hX]; exact hall

/-! ## The free Boolean-ring tree carrier and its normal form -/

/-- ★ The free Boolean-ring tree carrier: colour-tagged generators, the additive unit `0`, the multiplicative
unit `1`, F2 addition `xorOp`, and ring multiplication `andOp`.  There is no negation constructor — in F2 the
additive inverse of `x` is `x` itself. -/
inductive BrTree where
  /-- a colour-tagged generator (variable). -/
  | gen (colour : Nat)
  /-- the additive unit `0` (F2 zero, `⊥`). -/
  | zeroOp
  /-- the multiplicative unit `1` (F2 one, the empty monomial `⊤`). -/
  | oneOp
  /-- F2 addition (XOR). -/
  | xorOp : BrTree → BrTree → BrTree
  /-- ring multiplication (AND). -/
  | andOp : BrTree → BrTree → BrTree

/-- ★ normalize a tree to its Zhegalkin normal form (sorted squarefree monomials, F2 coefficients). -/
def brNormalize : BrTree → BrNF
  | .gen colour => [([colour], true)]
  | .zeroOp => []
  | .oneOp => [([], true)]
  | .xorOp l r => brMergeXor (brNormalize l) (brNormalize r)
  | .andOp l r => brMulConvolve (brNormalize l) (brNormalize r)

theorem brNormalize_zero_smoke : brNormalize BrTree.zeroOp = [] := rfl
theorem brNormalize_one_smoke : brNormalize BrTree.oneOp = [([], true)] := rfl
theorem brNormalize_gen_smoke : brNormalize (BrTree.gen 2) = [([2], true)] := rfl
theorem brNormalizeSorted (t : BrTree) : brNFSorted (brNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | xorOp l r _ ihr => exact brMergeXorPreservesSorted (brNormalize l) (brNormalize r) ihr
  | andOp l r _ _ => exact brMulConvolveSorted (brNormalize l) (brNormalize r)
theorem brNormalizeMonoSorted (t : BrTree) : brNFMonoSorted (brNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | xorOp l r ihl ihr => exact brMergeXorMonoSorted (brNormalize l) (brNormalize r) ihl ihr
  | andOp l r ihl ihr => exact brMulConvolveMonoSorted (brNormalize l) (brNormalize r) ihl ihr
/-- Generator idempotence at the normal-form level: `[x]·[x] = [x]` (the monomial set-union `{x} ∪ {x} = {x}`
followed by the F2 coefficient `true ∧ true = true`). -/
theorem brNormalizeAndIdemGen (c : Nat) :
    brMulConvolve [([c], true)] [([c], true)] = [([c], true)] := by
  show brMergeXor (brInsertTerm (brMonoMul [c] [c], brCoeffAnd true true) []) [] = [([c], true)]
  rw [brMonoMulSelfSingleton c]; rfl

/-! ## The Boolean-ring tree convertibility -/

/-- ★ The free convertibility of the `{+, ·, 0, 1}` signature over colour-tagged generators, closed under the
Boolean-ring laws: the additive ABELIAN GROUP OF EXPONENT 2 (associativity, commutativity, right unit, and the
F2 self-inverse `xorSelf : a + a ≈ 0`), the commutative multiplicative monoid (associativity, commutativity,
right unit), the GENERATOR idempotence `andIdemGen : x·x ≈ x`, distributivity and right-annihilation, the full
congruences `xorCongr` / `andCongr`, and `refl` / `symm` / `trans`.  This presents the FREE Boolean ring
`F2[X_c : c ∈ ℕ]`; composite idempotence `a·a ≈ a` is a derived theorem (see the decision). -/
inductive BooleanRingTreeConv : BrTree → BrTree → Prop where
  /-- **Additive associativity** `(a + b) + c ≈ a + (b + c)`. -/
  | xorAssoc (a b c : BrTree) :
      BooleanRingTreeConv (BrTree.xorOp (BrTree.xorOp a b) c) (BrTree.xorOp a (BrTree.xorOp b c))
  /-- **Additive commutativity** `a + b ≈ b + a`. -/
  | xorComm (a b : BrTree) : BooleanRingTreeConv (BrTree.xorOp a b) (BrTree.xorOp b a)
  /-- **Additive right unit** `a + 0 ≈ a`. -/
  | xorZero (a : BrTree) : BooleanRingTreeConv (BrTree.xorOp a BrTree.zeroOp) a
  /-- ★ **The F2 self-inverse** `a + a ≈ 0` — every element is its own additive inverse. -/
  | xorSelf (a : BrTree) : BooleanRingTreeConv (BrTree.xorOp a a) BrTree.zeroOp
  /-- **Multiplicative associativity** `(a · b) · c ≈ a · (b · c)`. -/
  | andAssoc (a b c : BrTree) :
      BooleanRingTreeConv (BrTree.andOp (BrTree.andOp a b) c) (BrTree.andOp a (BrTree.andOp b c))
  /-- **Multiplicative commutativity** `a · b ≈ b · a`. -/
  | andComm (a b : BrTree) : BooleanRingTreeConv (BrTree.andOp a b) (BrTree.andOp b a)
  /-- **Multiplicative right unit** `a · 1 ≈ a`. -/
  | andOne (a : BrTree) : BooleanRingTreeConv (BrTree.andOp a BrTree.oneOp) a
  /-- ★ **Generator idempotence** `x · x ≈ x` — the defining Boolean-ring law, imposed on generators. -/
  | andIdemGen (c : Nat) : BooleanRingTreeConv (BrTree.andOp (BrTree.gen c) (BrTree.gen c)) (BrTree.gen c)
  /-- **Left distributivity** `a · (b + c) ≈ a·b + a·c`. -/
  | distribLeft (a b c : BrTree) :
      BooleanRingTreeConv (BrTree.andOp a (BrTree.xorOp b c))
        (BrTree.xorOp (BrTree.andOp a b) (BrTree.andOp a c))
  /-- **Right annihilation** `a · 0 ≈ 0`. -/
  | annihilRight (a : BrTree) : BooleanRingTreeConv (BrTree.andOp a BrTree.zeroOp) BrTree.zeroOp
  /-- **Additive congruence** — into both summands. -/
  | xorCongr {leftOld leftNew rightOld rightNew : BrTree} :
      BooleanRingTreeConv leftOld leftNew → BooleanRingTreeConv rightOld rightNew →
      BooleanRingTreeConv (BrTree.xorOp leftOld rightOld) (BrTree.xorOp leftNew rightNew)
  /-- **Multiplicative congruence** — into both factors. -/
  | andCongr {leftOld leftNew rightOld rightNew : BrTree} :
      BooleanRingTreeConv leftOld leftNew → BooleanRingTreeConv rightOld rightNew →
      BooleanRingTreeConv (BrTree.andOp leftOld rightOld) (BrTree.andOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (t : BrTree) : BooleanRingTreeConv t t
  /-- Symmetry. -/
  | symm {s t : BrTree} : BooleanRingTreeConv s t → BooleanRingTreeConv t s
  /-- Transitivity. -/
  | trans {s t u : BrTree} : BooleanRingTreeConv s t → BooleanRingTreeConv t u → BooleanRingTreeConv s u

/-! ## Soundness: convertible ⟹ `brNFEq` normal forms -/

/-- ★ Soundness — convertible trees have `brNFEq` normal forms.  Every core ring law is a LITERAL normal-form
equality (`brNFEqOfEq` off the merge / convolve algebra); the F2 self-inverse falls to `brMergeXorSelfAllZero`
(`brNFEqNil`); generator idempotence to `brNormalizeAndIdemGen`; the congruences / equivalence to the `brNFEq`
structure. -/
theorem brNormalize_respects {s t : BrTree} (conv : BooleanRingTreeConv s t) :
    brNFEq (brNormalize s) (brNormalize t) = true := by
  induction conv with
  | xorAssoc a b c =>
      exact brNFEqOfEq _ _
        (brMergeXorPreservesSorted _ _ (brMergeXorPreservesSorted _ _ (brNormalizeSorted c)))
        (brMergeXorAssoc (brNormalize a) (brNormalize b) (brNormalize c))
  | xorComm a b =>
      exact brNFEqOfEq _ _
        (brMergeXorPreservesSorted _ _ (brNormalizeSorted a))
        (brMergeXorComm (brNormalize a) (brNormalize b) (brNormalizeSorted a) (brNormalizeSorted b))
  | xorZero a =>
      exact brNFEqOfEq _ _ (brNormalizeSorted a)
        (brMergeXorNilRight (brNormalize a) (brNormalizeSorted a))
  | xorSelf a =>
      exact brNFEqNil _
        (brMergeXorPreservesSorted _ _ (brNormalizeSorted a))
        (brMergeXorSelfAllZero (brNormalize a) (brNormalizeSorted a))
  | andAssoc a b c =>
      exact brNFEqOfEq _ _ (brMulConvolveSorted _ _)
        (brMulConvolveAssoc (brNormalize a) (brNormalize b) (brNormalize c))
  | andComm a b =>
      exact brNFEqOfEq _ _ (brMulConvolveSorted _ _)
        (brMulConvolveComm (brNormalize a) (brNormalize b)
          (brNormalizeSorted a) (brNormalizeMonoSorted a) (brNormalizeMonoSorted b))
  | andOne a =>
      exact brNFEqOfEq _ _ (brNormalizeSorted a)
        (brMulConvolveUnit (brNormalize a) (brNormalizeSorted a))
  | andIdemGen c =>
      exact brNFEqOfEq (brMulConvolve [([c], true)] [([c], true)]) [([c], true)] rfl
        (brNormalizeAndIdemGen c)
  | distribLeft a b c =>
      exact brNFEqOfEq _ _
        (brMergeXorPreservesSorted _ _ (brMulConvolveSorted _ _))
        (brMulConvolve_leftDistrib (brNormalize a) (brNormalize b) (brNormalize c))
  | annihilRight a =>
      exact brNFEqOfEq _ _ rfl (brMulConvolveAnnihil (brNormalize a))
  | @xorCongr lo ln ro rn _ _ ihl ihr =>
      exact brNFEqMergeCongr (brNormalize lo) (brNormalize ln) (brNormalize ro) (brNormalize rn)
        (brNormalizeSorted ln) (brNormalizeSorted ro) ihl ihr
  | @andCongr lo ln ro rn _ _ ihl ihr =>
      exact brNFEqMulCongr (brNormalize lo) (brNormalize ln) (brNormalize ro) (brNormalize rn) ihl ihr
  | refl t => exact brNFEqRefl (brNormalize t) (brNormalizeSorted t)
  | @symm s t _ ih =>
      exact brNFEqSymm (brNormalize s) (brNormalize t)
        (brNormalizeSorted s) (brNormalizeSorted t) ih
  | @trans s t u _ _ ih1 ih2 =>
      exact brNFEqTrans (brNormalize s) (brNormalize t) (brNormalize u)
        (brNormalizeSorted s) (brNormalizeSorted t) (brNormalizeSorted u) ih1 ih2

/-! ## Derived convertibility lemmas (for the rebuild reification) -/

theorem brConvXorZeroLeft (a : BrTree) : BooleanRingTreeConv (BrTree.xorOp BrTree.zeroOp a) a :=
  (BooleanRingTreeConv.xorComm BrTree.zeroOp a).trans (BooleanRingTreeConv.xorZero a)
theorem brConvAndOneLeft (a : BrTree) : BooleanRingTreeConv (BrTree.andOp BrTree.oneOp a) a :=
  (BooleanRingTreeConv.andComm BrTree.oneOp a).trans (BooleanRingTreeConv.andOne a)
theorem brConvAnnihilLeft (a : BrTree) :
    BooleanRingTreeConv (BrTree.andOp BrTree.zeroOp a) BrTree.zeroOp :=
  (BooleanRingTreeConv.andComm BrTree.zeroOp a).trans (BooleanRingTreeConv.annihilRight a)
theorem brConvDistribRight (a b c : BrTree) :
    BooleanRingTreeConv (BrTree.andOp (BrTree.xorOp a b) c)
      (BrTree.xorOp (BrTree.andOp a c) (BrTree.andOp b c)) :=
  (BooleanRingTreeConv.andComm (BrTree.xorOp a b) c).trans
    ((BooleanRingTreeConv.distribLeft c a b).trans
      (BooleanRingTreeConv.xorCongr (BooleanRingTreeConv.andComm c a) (BooleanRingTreeConv.andComm c b)))
theorem brConvXorSwap13 (x y z : BrTree) :
    BooleanRingTreeConv (BrTree.xorOp x (BrTree.xorOp y z)) (BrTree.xorOp y (BrTree.xorOp x z)) :=
  (BooleanRingTreeConv.symm (BooleanRingTreeConv.xorAssoc x y z)).trans
    ((BooleanRingTreeConv.xorCongr (BooleanRingTreeConv.xorComm x y) (BooleanRingTreeConv.refl z)).trans
      (BooleanRingTreeConv.xorAssoc y x z))
theorem brConvAndSwap13 (x y z : BrTree) :
    BooleanRingTreeConv (BrTree.andOp x (BrTree.andOp y z)) (BrTree.andOp y (BrTree.andOp x z)) :=
  (BooleanRingTreeConv.symm (BooleanRingTreeConv.andAssoc x y z)).trans
    ((BooleanRingTreeConv.andCongr (BooleanRingTreeConv.andComm x y) (BooleanRingTreeConv.refl z)).trans
      (BooleanRingTreeConv.andAssoc y x z))

/-! ## The monomial tree and its multiplicative reification -/

def brMonoToTree : List Nat → BrTree
  | [] => BrTree.oneOp
  | c :: rest => BrTree.andOp (BrTree.gen c) (brMonoToTree rest)
/-- Reifying an insert into the sorted monomial: `monoToTree (insertSortedSet v xs) ≈ gen v · monoToTree xs`.
The EQUAL (dedup) case is where GENERATOR IDEMPOTENCE `x·x ≈ x` is consumed. -/
theorem brMonoToTreeInsertSortedSet (v : Nat) (xs : List Nat) :
    BooleanRingTreeConv (brMonoToTree (insertSortedSet v xs))
      (BrTree.andOp (BrTree.gen v) (brMonoToTree xs)) := by
  induction xs with
  | nil => exact BooleanRingTreeConv.refl (BrTree.andOp (BrTree.gen v) (brMonoToTree []))
  | cons a rest ih =>
      cases hva : natBle v a with
      | false =>
          rw [insertSortedSetGt v a rest hva]
          show BooleanRingTreeConv (BrTree.andOp (BrTree.gen a) (brMonoToTree (insertSortedSet v rest)))
            (BrTree.andOp (BrTree.gen v) (BrTree.andOp (BrTree.gen a) (brMonoToTree rest)))
          exact (BooleanRingTreeConv.andCongr (BooleanRingTreeConv.refl (BrTree.gen a)) ih).trans
            (brConvAndSwap13 (BrTree.gen a) (BrTree.gen v) (brMonoToTree rest))
      | true =>
          cases hav : natBle a v with
          | false =>
              rw [insertSortedSetLt v a rest hva hav]
              exact BooleanRingTreeConv.refl _
          | true =>
              rw [insertSortedSetEq v a rest hva hav]
              have hva_eq : v = a := natBleAntisymm v a hva hav
              rw [hva_eq]
              show BooleanRingTreeConv (BrTree.andOp (BrTree.gen a) (brMonoToTree rest))
                (BrTree.andOp (BrTree.gen a) (BrTree.andOp (BrTree.gen a) (brMonoToTree rest)))
              exact BooleanRingTreeConv.symm
                ((BooleanRingTreeConv.symm
                    (BooleanRingTreeConv.andAssoc (BrTree.gen a) (BrTree.gen a) (brMonoToTree rest))).trans
                  (BooleanRingTreeConv.andCongr (BooleanRingTreeConv.andIdemGen a)
                    (BooleanRingTreeConv.refl (brMonoToTree rest))))
theorem brMonoToTreeInsertManySet : (n m : List Nat) →
    BooleanRingTreeConv (brMonoToTree (insertManySet n m))
      (BrTree.andOp (brMonoToTree n) (brMonoToTree m))
  | [], m => (brConvAndOneLeft (brMonoToTree m)).symm
  | a :: n', m => by
      show BooleanRingTreeConv (brMonoToTree (insertSortedSet a (insertManySet n' m)))
        (BrTree.andOp (BrTree.andOp (BrTree.gen a) (brMonoToTree n')) (brMonoToTree m))
      exact (brMonoToTreeInsertSortedSet a (insertManySet n' m)).trans
        ((BooleanRingTreeConv.andCongr (BooleanRingTreeConv.refl (BrTree.gen a))
            (brMonoToTreeInsertManySet n' m)).trans
          (BooleanRingTreeConv.symm
            (BooleanRingTreeConv.andAssoc (BrTree.gen a) (brMonoToTree n') (brMonoToTree m))))
theorem brMonoToTreeMonoMul (m n : List Nat) :
    BooleanRingTreeConv (brMonoToTree (brMonoMul m n))
      (BrTree.andOp (brMonoToTree m) (brMonoToTree n)) := by
  show BooleanRingTreeConv (brMonoToTree (insertManySet n m))
    (BrTree.andOp (brMonoToTree m) (brMonoToTree n))
  exact (brMonoToTreeInsertManySet n m).trans
    (BooleanRingTreeConv.andComm (brMonoToTree n) (brMonoToTree m))

/-! ## The term tree (an F2 coefficient applied to a monomial) and its reification -/

/-- The tree of a single term `(mono, c)`: the monomial tree when present, `0` when absent. -/
def brTermToTree (mono : List Nat) : Bool → BrTree
  | false => BrTree.zeroOp
  | true => brMonoToTree mono
/-- The term tree distributes over coefficient XOR (four finite `Bool` cases; the `true, true` case is the F2
self-inverse `x + x ≈ 0`). -/
theorem brTermToTreeXor (m : List Nat) (e c : Bool) :
    BooleanRingTreeConv (brTermToTree m (brCoeffXor e c))
      (BrTree.xorOp (brTermToTree m e) (brTermToTree m c)) := by
  cases e with
  | false => cases c with
    | false => exact (BooleanRingTreeConv.xorZero BrTree.zeroOp).symm
    | true => exact (brConvXorZeroLeft (brMonoToTree m)).symm
  | true => cases c with
    | false => exact (BooleanRingTreeConv.xorZero (brMonoToTree m)).symm
    | true => exact (BooleanRingTreeConv.xorSelf (brMonoToTree m)).symm
/-- The term-product reification: `termToTree (m ⊎ n) (c1 ∧ c2) ≈ (termToTree m c1) · (termToTree n c2)`
(four finite `Bool` cases; the present-present case is `brMonoToTreeMonoMul`). -/
theorem brTermToTreeMul (m : List Nat) (c1 : Bool) (n : List Nat) (c2 : Bool) :
    BooleanRingTreeConv (brTermToTree (brMonoMul m n) (brCoeffAnd c1 c2))
      (BrTree.andOp (brTermToTree m c1) (brTermToTree n c2)) := by
  cases c1 with
  | true => cases c2 with
    | true => exact brMonoToTreeMonoMul m n
    | false => exact (BooleanRingTreeConv.annihilRight (brMonoToTree m)).symm
  | false => cases c2 with
    | true => exact (brConvAnnihilLeft (brMonoToTree n)).symm
    | false => exact (BooleanRingTreeConv.annihilRight BrTree.zeroOp).symm
/-- An absent term tree is convertible to `0`. -/
theorem brTermToTreeZero (m : List Nat) (c : Bool) (hc : brCoeffIsZero c = true) :
    BooleanRingTreeConv (brTermToTree m c) BrTree.zeroOp := by
  cases c with
  | false => exact BooleanRingTreeConv.refl BrTree.zeroOp
  | true => exact Bool.noConfusion hc

/-! ## The normal-form rebuild `brCombOfNF` and its convertibility algebra -/

/-- Rebuild a canonical tree from a normal form (XOR-fold the term trees). -/
def brCombOfNF : BrNF → BrTree
  | [] => BrTree.zeroOp
  | (m, c) :: rest => BrTree.xorOp (brTermToTree m c) (brCombOfNF rest)
theorem brCombOfNFCons (m : List Nat) (c : Bool) (rest : BrNF) :
    brCombOfNF ((m, c) :: rest) = BrTree.xorOp (brTermToTree m c) (brCombOfNF rest) := rfl
theorem brCombInsertTerm (m : List Nat) (c : Bool) (A : BrNF) :
    BooleanRingTreeConv (brCombOfNF (brInsertTerm (m, c) A))
      (BrTree.xorOp (brTermToTree m c) (brCombOfNF A)) := by
  induction A with
  | nil => exact BooleanRingTreeConv.refl _
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [brInsertTermEqE m c p e rest hmp, brCombOfNFCons p (brCoeffXor e c) rest,
              brCombOfNFCons p e rest, hmeqp]
          exact (BooleanRingTreeConv.xorCongr (brTermToTreeXor p e c)
              (BooleanRingTreeConv.refl (brCombOfNF rest))).trans
            ((BooleanRingTreeConv.xorAssoc (brTermToTree p e) (brTermToTree p c) (brCombOfNF rest)).trans
              (brConvXorSwap13 (brTermToTree p e) (brTermToTree p c) (brCombOfNF rest)))
      | lt =>
          rw [brInsertTermLtE m c p e rest hmp, brCombOfNFCons m c ((p, e) :: rest)]
          exact BooleanRingTreeConv.refl _
      | gt =>
          rw [brInsertTermGtE m c p e rest hmp, brCombOfNFCons p e (brInsertTerm (m, c) rest),
              brCombOfNFCons p e rest]
          exact (BooleanRingTreeConv.xorCongr (BooleanRingTreeConv.refl (brTermToTree p e)) ih).trans
            (brConvXorSwap13 (brTermToTree p e) (brTermToTree m c) (brCombOfNF rest))
theorem brCombMergeXor (A B : BrNF) :
    BooleanRingTreeConv (brCombOfNF (brMergeXor A B))
      (BrTree.xorOp (brCombOfNF A) (brCombOfNF B)) := by
  induction A with
  | nil => exact (brConvXorZeroLeft (brCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show BooleanRingTreeConv (brCombOfNF (brInsertTerm (m, c) (brMergeXor A' B)))
        (BrTree.xorOp (BrTree.xorOp (brTermToTree m c) (brCombOfNF A')) (brCombOfNF B))
      exact ((brCombInsertTerm m c (brMergeXor A' B)).trans
          (BooleanRingTreeConv.xorCongr (BooleanRingTreeConv.refl (brTermToTree m c)) ih)).trans
        (BooleanRingTreeConv.symm
          (BooleanRingTreeConv.xorAssoc (brTermToTree m c) (brCombOfNF A') (brCombOfNF B)))
theorem brCombTermMul (m : List Nat) (c : Bool) (B : BrNF) :
    BooleanRingTreeConv (brCombOfNF (brTermMul m c B))
      (BrTree.andOp (brTermToTree m c) (brCombOfNF B)) := by
  induction B with
  | nil => exact (BooleanRingTreeConv.annihilRight (brTermToTree m c)).symm
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show BooleanRingTreeConv (brCombOfNF (brInsertTerm (brMonoMul m n, brCoeffAnd c d) (brTermMul m c B')))
        (BrTree.andOp (brTermToTree m c) (BrTree.xorOp (brTermToTree n d) (brCombOfNF B')))
      exact ((brCombInsertTerm (brMonoMul m n) (brCoeffAnd c d) (brTermMul m c B')).trans
          (BooleanRingTreeConv.xorCongr (brTermToTreeMul m c n d) ih)).trans
        (BooleanRingTreeConv.symm
          (BooleanRingTreeConv.distribLeft (brTermToTree m c) (brTermToTree n d) (brCombOfNF B')))
theorem brCombMulConvolve (A B : BrNF) :
    BooleanRingTreeConv (brCombOfNF (brMulConvolve A B))
      (BrTree.andOp (brCombOfNF A) (brCombOfNF B)) := by
  induction A with
  | nil => exact (brConvAnnihilLeft (brCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show BooleanRingTreeConv (brCombOfNF (brMergeXor (brTermMul m c B) (brMulConvolve A' B)))
        (BrTree.andOp (BrTree.xorOp (brTermToTree m c) (brCombOfNF A')) (brCombOfNF B))
      exact ((brCombMergeXor (brTermMul m c B) (brMulConvolve A' B)).trans
          (BooleanRingTreeConv.xorCongr (brCombTermMul m c B) ih)).trans
        (BooleanRingTreeConv.symm (brConvDistribRight (brTermToTree m c) (brCombOfNF A') (brCombOfNF B)))
/-- An all-absent rebuild reduces to `0`. -/
theorem brCombAllZero (A : BrNF) (hA : brNFAllZero A = true) :
    BooleanRingTreeConv (brCombOfNF A) BrTree.zeroOp := by
  induction A with
  | nil => exact BooleanRingTreeConv.refl BrTree.zeroOp
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      have hc : brCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hrest : brNFAllZero rest = true := csrAndTrueRight _ _ hA
      show BooleanRingTreeConv (BrTree.xorOp (brTermToTree m c) (brCombOfNF rest)) BrTree.zeroOp
      exact (BooleanRingTreeConv.xorCongr (brTermToTreeZero m c hc) (ih hrest)).trans
        (BooleanRingTreeConv.xorZero BrTree.zeroOp)

/-! ## Reification: every tree is convertible to the rebuild of its own normal form -/

/-- ★ Every tree is convertible to the rebuild of its own normal form. -/
theorem brTreeReifies (t : BrTree) : BooleanRingTreeConv t (brCombOfNF (brNormalize t)) := by
  induction t with
  | gen c =>
      show BooleanRingTreeConv (BrTree.gen c) (BrTree.xorOp (brTermToTree [c] true) BrTree.zeroOp)
      have hgen : BooleanRingTreeConv (BrTree.gen c) (brMonoToTree [c]) :=
        (BooleanRingTreeConv.andOne (BrTree.gen c)).symm
      exact hgen.trans (BooleanRingTreeConv.symm (BooleanRingTreeConv.xorZero (brMonoToTree [c])))
  | zeroOp => exact BooleanRingTreeConv.refl BrTree.zeroOp
  | oneOp =>
      show BooleanRingTreeConv BrTree.oneOp (BrTree.xorOp (brTermToTree [] true) BrTree.zeroOp)
      exact (BooleanRingTreeConv.xorZero (brMonoToTree [])).symm
  | xorOp l r ihl ihr =>
      show BooleanRingTreeConv (BrTree.xorOp l r)
        (brCombOfNF (brMergeXor (brNormalize l) (brNormalize r)))
      exact (BooleanRingTreeConv.xorCongr ihl ihr).trans
        (BooleanRingTreeConv.symm (brCombMergeXor (brNormalize l) (brNormalize r)))
  | andOp l r ihl ihr =>
      show BooleanRingTreeConv (BrTree.andOp l r)
        (brCombOfNF (brMulConvolve (brNormalize l) (brNormalize r)))
      exact (BooleanRingTreeConv.andCongr ihl ihr).trans
        (BooleanRingTreeConv.symm (brCombMulConvolve (brNormalize l) (brNormalize r)))

/-! ## Completeness: `brNFEq` normal forms give convertible trees -/

/-- If `x + y ≈ 0` then `x ≈ y` — in F2 the additive inverse of `y` is `y`, so `x + y ≈ 0` forces `x ≈ y`. -/
theorem brConvOfXorZero (x y : BrTree)
    (h : BooleanRingTreeConv (BrTree.xorOp x y) BrTree.zeroOp) : BooleanRingTreeConv x y :=
  (BooleanRingTreeConv.xorZero x).symm.trans
    ((BooleanRingTreeConv.xorCongr (BooleanRingTreeConv.refl x)
        (BooleanRingTreeConv.symm (BooleanRingTreeConv.xorSelf y))).trans
      ((BooleanRingTreeConv.symm (BooleanRingTreeConv.xorAssoc x y y)).trans
        ((BooleanRingTreeConv.xorCongr h (BooleanRingTreeConv.refl y)).trans
          (brConvXorZeroLeft y))))
/-- The rebuilds of `brNFEq` normal forms are convertible. -/
theorem brCombOfNFEqConv (A B : BrNF) (h : brNFEq A B = true) :
    BooleanRingTreeConv (brCombOfNF A) (brCombOfNF B) := by
  apply brConvOfXorZero (brCombOfNF A) (brCombOfNF B)
  have hall : BooleanRingTreeConv (brCombOfNF (brMergeXor A B)) BrTree.zeroOp :=
    brCombAllZero (brMergeXor A B) h
  exact (BooleanRingTreeConv.symm (brCombMergeXor A B)).trans hall
/-- ★ Completeness — `brNFEq` normal forms give convertible trees. -/
theorem brConv_of_normalizeEq {s t : BrTree} (h : brNFEq (brNormalize s) (brNormalize t) = true) :
    BooleanRingTreeConv s t :=
  (brTreeReifies s).trans
    ((brCombOfNFEqConv (brNormalize s) (brNormalize t) h).trans (BooleanRingTreeConv.symm (brTreeReifies t)))

/-! ## The decision -/

/-- ★★ the decision procedure: convertible iff the Zhegalkin XOR-difference is all-absent. -/
def brDecideConv (s t : BrTree) : Bool := brNFEq (brNormalize s) (brNormalize t)
/-- ★★ THE DECISION: convertibility ⟺ equal Zhegalkin (F2[X]/(x²=x)) normal form. -/
theorem booleanRingTreeConv_iff_normalForm (s t : BrTree) :
    BooleanRingTreeConv s t ↔ brDecideConv s t = true := by
  constructor
  · intro conv
    exact brNormalize_respects conv
  · intro hdec
    exact brConv_of_normalizeEq hdec
/-- ★ decidability, via the biconditional (no `propext`). -/
instance instDecidableBooleanRingTreeConv (s t : BrTree) : Decidable (BooleanRingTreeConv s t) :=
  if h : brDecideConv s t = true then
    isTrue ((booleanRingTreeConv_iff_normalForm s t).mpr h)
  else
    isFalse (fun conv => h ((booleanRingTreeConv_iff_normalForm s t).mp conv))
/-- ★★ the walking free Boolean ring on ℕ (F2[X]/(x²=x), the Zhegalkin algebra) is DECIDED. -/
def fxWalkingBooleanRing_hasNormalFormDecision : Bool := true

-- genuineness smokes
-- THE HEADLINE (F2): x + x is 0 (true) — every element is its own additive inverse
#eval brDecideConv (BrTree.xorOp (BrTree.gen 0) (BrTree.gen 0)) BrTree.zeroOp
-- THE HEADLINE (idempotence): x * x is x (true) — the defining Boolean-ring law
#eval brDecideConv (BrTree.andOp (BrTree.gen 0) (BrTree.gen 0)) (BrTree.gen 0)
-- distributivity over XOR: x * (y + z) is x*y + x*z (true)
#eval brDecideConv (BrTree.andOp (BrTree.gen 0) (BrTree.xorOp (BrTree.gen 1) (BrTree.gen 2)))
  (BrTree.xorOp (BrTree.andOp (BrTree.gen 0) (BrTree.gen 1)) (BrTree.andOp (BrTree.gen 0) (BrTree.gen 2)))
-- additive commutativity: x + y is y + x (true)
#eval brDecideConv (BrTree.xorOp (BrTree.gen 0) (BrTree.gen 1)) (BrTree.xorOp (BrTree.gen 1) (BrTree.gen 0))
-- multiplicative commutativity: x * y is y * x (true)
#eval brDecideConv (BrTree.andOp (BrTree.gen 0) (BrTree.gen 1)) (BrTree.andOp (BrTree.gen 1) (BrTree.gen 0))
-- composite idempotence: (x + 1)^2 is x + 1 (true) — cross terms cancel in F2, x^2 = x
#eval brDecideConv
  (BrTree.andOp (BrTree.xorOp (BrTree.gen 0) BrTree.oneOp) (BrTree.xorOp (BrTree.gen 0) BrTree.oneOp))
  (BrTree.xorOp (BrTree.gen 0) BrTree.oneOp)
-- separation: x is NOT y (false)
#eval brDecideConv (BrTree.gen 0) (BrTree.gen 1)
-- separation: x + y is NOT x (false)
#eval brDecideConv (BrTree.xorOp (BrTree.gen 0) (BrTree.gen 1)) (BrTree.gen 0)

end FX1Poly.Polygraph
