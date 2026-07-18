import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeSemiring.CommutativeSemiringSeed
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # WalkingFieldTwoPolynomial/FieldTwoPolynomialSeed — the walking free COMMUTATIVE ALGEBRA over F2: the ring F2[X], decided by canonical normal form

The NON-idempotent cousin of the Boolean-ring rung (`BooleanRingSeed`).  A **commutative F2-algebra** free on the
colour set `ℕ` is exactly the polynomial ring `F2[X_c : c ∈ ℕ]` — polynomials over the two-element field
`F2 = {0, 1}` in commuting variables, the ring at the heart of coding theory.  Its elements are the finite F2
(XOR) sums of MONOMIALS, where a monomial is a finite MULTISET of variables (variable exponents matter: `x·x`
is the genuine degree-two monomial `x²`, and `x² ≠ x`) and coefficients live in F2 (present/absent).  Two
elements coincide exactly when they carry the same set of present monomials — a COMPLETE invariant, so the word
problem is DECIDED.

## ★ The single change from the Boolean ring: monomials are MULTISETS, not sets

The Boolean-ring sibling imposes `x·x = x`, collapsing variable exponents to 0/1, so a monomial is a squarefree
variable SET (built with the dedup-on-equal `insertManySet`).  Here that idempotence law is DROPPED: F2[X] is the
FREE commutative F2-algebra, with no relation forcing `x² = x`.  A monomial is therefore a variable MULTISET,
built with the imported non-dedup `insertMany` (`ftpMonoMul m n := insertMany n m` is multiset union of
exponents), so `[c]·[c] = [c, c]` is a real degree-two monomial that the ordering (length-first, then lex)
places STRICTLY above `[c]` — dropping a law makes this walker strictly simpler than the Boolean ring, not
harder.

* **Coefficients are F2, carried as `Bool`** (exactly as the Boolean-ring sibling).  Each F2 coefficient is a
  `Bool` and, following the same NO-DROP discipline, cancelling terms are never removed: `ftpCoeffXor` (F2 add =
  `Bool` xor), `ftpCoeffAnd` (F2 mul = `Bool` and), `ftpCoeffIsZero` (absent = `false`).  Because F2 addition is
  its own inverse (`x + x = 0`), NEGATION IS THE IDENTITY — there is no negate layer, and the difference `A − B`
  is simply `A + B`.

`FtpNF := List (List Nat × Bool)` is a list of `(monomial, coeff)` terms sorted strictly by the imported
monomial order `csrCompare` (length-first then lex).  `ftpNormalize` sends `gen c ↦ [([c], true)]`,
`zeroOp ↦ []`, `oneOp ↦ [([], true)]` (the empty monomial is the multiplicative unit),
`xorOp ↦ ftpMergeXor` (coefficient-XOR merge), `andOp ↦ ftpMulConvolve` (the Cauchy convolution: monomial
product = multiset union via `insertMany`, coefficient product = and).

The DECISION is the F2 polynomial equality `ftpNFEq A B := ftpNFAllZero (ftpMergeXor A B)` — two polynomials
agree exactly when their XOR-difference has every coefficient absent.  Its soundness / completeness rest on the
`ftpEvalCross` semantic model (the per-monomial F2 coefficient), whose merge homomorphism makes `ftpNFEq` a
decidable congruence; the crux `ftpMergeXor A A` all-absent (the F2 self-inverse `x + x = 0`) falls out of the
model (each monomial's `c xor c = false`).

The convertibility is the free commutative-F2-algebra presentation: the additive abelian group of exponent 2
(with `xorSelf : a + a ≈ 0`), the commutative multiplicative MONOID (`andAssoc` / `andComm` / `andOne` — and
crucially NO `andIdem`), distributivity, and annihilation.  There is no `andIdemGen`: this is the whole
difference from the Boolean ring.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` in the audit
twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`,
`Int`, `Nat.sub`, `List.append` (`++`), and every `Nat.le`/`Nat.ble` lemma — the ordering is the imported
structural `csrCompare` (over `natBle`), the monomial product is the imported cons-only `insertMany`, and
coefficient arithmetic is the finite `Bool` xor/and kit (no coefficient multiplication beyond `Bool` and). -/

namespace FX1Poly.Polygraph

/-! ## The F2 coefficient algebra as `Bool` (xor / and), all laws by finite case analysis -/

/-- F2 addition on the `Bool` coefficient: exclusive or. -/
def ftpCoeffXor : Bool → Bool → Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

/-- F2 multiplication on the `Bool` coefficient: conjunction. -/
def ftpCoeffAnd : Bool → Bool → Bool
  | false, false => false
  | false, true => false
  | true, false => false
  | true, true => true

/-- A coefficient is zero (absent) exactly when it is `false`. -/
def ftpCoeffIsZero : Bool → Bool
  | false => true
  | true => false

theorem ftpCoeffXorComm (a b : Bool) : ftpCoeffXor a b = ftpCoeffXor b a := by
  cases a <;> cases b <;> rfl
theorem ftpCoeffXorAssoc (a b c : Bool) :
    ftpCoeffXor (ftpCoeffXor a b) c = ftpCoeffXor a (ftpCoeffXor b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem ftpCoeffXorFalseRight (a : Bool) : ftpCoeffXor a false = a := by cases a <;> rfl
theorem ftpCoeffXorFalseLeft (a : Bool) : ftpCoeffXor false a = a := by cases a <;> rfl
theorem ftpCoeffXorRightComm (e d c : Bool) :
    ftpCoeffXor (ftpCoeffXor e d) c = ftpCoeffXor (ftpCoeffXor e c) d := by
  cases e <;> cases d <;> cases c <;> rfl
theorem ftpCoeffXorSwap13 (x y z : Bool) :
    ftpCoeffXor x (ftpCoeffXor y z) = ftpCoeffXor y (ftpCoeffXor x z) := by
  cases x <;> cases y <;> cases z <;> rfl
theorem ftpCoeffAndComm (a b : Bool) : ftpCoeffAnd a b = ftpCoeffAnd b a := by
  cases a <;> cases b <;> rfl
theorem ftpCoeffAndTrueRight (a : Bool) : ftpCoeffAnd a true = a := by cases a <;> rfl
theorem ftpCoeffAndAssoc (a b c : Bool) :
    ftpCoeffAnd (ftpCoeffAnd a b) c = ftpCoeffAnd a (ftpCoeffAnd b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem ftpCoeffAndXorRight (a b c : Bool) :
    ftpCoeffAnd a (ftpCoeffXor b c) = ftpCoeffXor (ftpCoeffAnd a b) (ftpCoeffAnd a c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem ftpCoeffXorAndRight (a b c : Bool) :
    ftpCoeffAnd (ftpCoeffXor a b) c = ftpCoeffXor (ftpCoeffAnd a c) (ftpCoeffAnd b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem ftpCoeffXorSelfZero (a : Bool) : ftpCoeffIsZero (ftpCoeffXor a a) = true := by cases a <;> rfl
theorem ftpCoeffXorZeroValued (a b : Bool)
    (ha : ftpCoeffIsZero a = true) (hb : ftpCoeffIsZero b = true) :
    ftpCoeffIsZero (ftpCoeffXor a b) = true := by
  cases a with
  | true => exact Bool.noConfusion ha
  | false => cases b with
    | true => exact Bool.noConfusion hb
    | false => rfl
theorem ftpCoeffAndZeroValuedLeft (a b : Bool) (ha : ftpCoeffIsZero a = true) :
    ftpCoeffIsZero (ftpCoeffAnd a b) = true := by
  cases a with
  | true => exact Bool.noConfusion ha
  | false => cases b with | true => rfl | false => rfl
theorem ftpCoeffAndZeroValuedRight (a b : Bool) (hb : ftpCoeffIsZero b = true) :
    ftpCoeffIsZero (ftpCoeffAnd a b) = true := by
  rw [ftpCoeffAndComm a b]; exact ftpCoeffAndZeroValuedLeft b a hb
theorem ftpCoeffXorCancelZero (a b : Bool)
    (hsum : ftpCoeffIsZero (ftpCoeffXor a b) = true) (hb : ftpCoeffIsZero b = true) :
    ftpCoeffIsZero a = true := by
  cases b with
  | true => exact Bool.noConfusion hb
  | false => rw [ftpCoeffXorFalseRight a] at hsum; exact hsum

/-! ## The monomial layer: variable MULTISETS via the imported `insertMany`, sorted with repeats (`x·x = [c,c]`) -/

/-- Monomial multiplication is variable-MULTISET union: `insertMany` keeps repeats, so `[c] · [c] = [c, c]`
(degree two), NOT `[c]` — this is the whole difference from the Boolean-ring sibling. -/
def ftpMonoMul (m n : List Nat) : List Nat := insertMany n m
theorem ftpMonoMulNilRight (m : List Nat) : ftpMonoMul m [] = m := rfl
theorem ftpMonoMulAssoc (m n p : List Nat) :
    ftpMonoMul (ftpMonoMul m n) p = ftpMonoMul m (ftpMonoMul n p) := by
  show insertMany p (insertMany n m) = insertMany (insertMany p n) m
  exact (insertManyAssoc p n m).symm
/-- Below-head test for a monomial: `a` does not exceed the head (NON-strict — repeats are allowed). -/
def ftpMonoBelow (a : Nat) : List Nat → Bool
  | [] => true
  | b :: _ => natBle a b
/-- A monomial is a SORTED variable list, repeats allowed (a multiset). -/
def ftpMonoSorted : List Nat → Bool
  | [] => true
  | a :: rest => ftpMonoBelow a rest && ftpMonoSorted rest
theorem ftpMonoBelowNil (a : Nat) : ftpMonoBelow a [] = true := rfl
theorem ftpMonoBelowCons (a b : Nat) (rest : List Nat) : ftpMonoBelow a (b :: rest) = natBle a b := rfl
theorem ftpMonoSortedCons (a : Nat) (rest : List Nat) :
    ftpMonoSorted (a :: rest) = (ftpMonoBelow a rest && ftpMonoSorted rest) := rfl
theorem ftpMonoBelowInsert (a v : Nat) (xs : List Nat)
    (hav : natBle a v = true) (hx : ftpMonoBelow a xs = true) :
    ftpMonoBelow a (insertSorted v xs) = true := by
  cases xs with
  | nil => rw [insertSortedNilEq v, ftpMonoBelowCons a v []]; exact hav
  | cons b rest =>
      have hab : natBle a b = true := by rw [ftpMonoBelowCons a b rest] at hx; exact hx
      cases hvb : natBle v b with
      | true => rw [insertSortedConsTrue v b rest hvb, ftpMonoBelowCons a v (b :: rest)]; exact hav
      | false => rw [insertSortedConsFalse v b rest hvb, ftpMonoBelowCons a b (insertSorted v rest)]; exact hab
theorem ftpInsertSortedPreservesMonoSorted (v : Nat) (xs : List Nat)
    (hx : ftpMonoSorted xs = true) : ftpMonoSorted (insertSorted v xs) = true := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      have hbelow : ftpMonoBelow a rest = true := csrAndTrueLeft _ _ hx
      have hrest : ftpMonoSorted rest = true := csrAndTrueRight _ _ hx
      cases hva : natBle v a with
      | true =>
          rw [insertSortedConsTrue v a rest hva, ftpMonoSortedCons v (a :: rest)]
          exact csrAndIntro _ _ (by rw [ftpMonoBelowCons v a rest]; exact hva) hx
      | false =>
          rw [insertSortedConsFalse v a rest hva, ftpMonoSortedCons a (insertSorted v rest)]
          have hav : natBle a v = true := natBleTotal v a hva
          exact csrAndIntro _ _ (ftpMonoBelowInsert a v rest hav hbelow) (ih hrest)
theorem ftpInsertManyPreservesMonoSorted (ys xs : List Nat)
    (hx : ftpMonoSorted xs = true) : ftpMonoSorted (insertMany ys xs) = true := by
  induction ys with
  | nil => exact hx
  | cons y ys' ih =>
      show ftpMonoSorted (insertSorted y (insertMany ys' xs)) = true
      exact ftpInsertSortedPreservesMonoSorted y (insertMany ys' xs) ih
theorem ftpMonoMulSorted (m n : List Nat) (hm : ftpMonoSorted m = true) :
    ftpMonoSorted (ftpMonoMul m n) = true := ftpInsertManyPreservesMonoSorted n m hm
theorem ftpMonoInsertFront (a : Nat) (rest : List Nat) (h : ftpMonoBelow a rest = true) :
    insertSorted a rest = a :: rest := by
  cases rest with
  | nil => rfl
  | cons b r' =>
      have hab : natBle a b = true := by rw [ftpMonoBelowCons a b r'] at h; exact h
      exact insertSortedConsTrue a b r' hab
theorem ftpMonoFixpoint (xs : List Nat) (h : ftpMonoSorted xs = true) : insertMany xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      have hbelow : ftpMonoBelow a rest = true := csrAndTrueLeft _ _ h
      have hrest : ftpMonoSorted rest = true := csrAndTrueRight _ _ h
      show insertSorted a (insertMany rest []) = a :: rest
      rw [ih hrest, ftpMonoInsertFront a rest hbelow]
theorem ftpMonoMulComm (m n : List Nat) (hm : ftpMonoSorted m = true) (hn : ftpMonoSorted n = true) :
    ftpMonoMul m n = ftpMonoMul n m := by
  show insertMany n m = insertMany m n
  have h := insertManyComm n m []
  rw [ftpMonoFixpoint m hm, ftpMonoFixpoint n hn] at h
  exact h

/-! ## The F2[X] normal form and its coefficient-XOR additive engine (no-drop, F2 coefficients) -/

/-- The normal form: `(monomial, F2-coefficient)` terms, sorted strictly by the imported `csrCompare`. -/
abbrev FtpNF := List (List Nat × Bool)

/-- Insert one term into a sorted normal form, XOR-ing coefficients on an equal monomial (never dropping). -/
def ftpInsertTerm : (List Nat × Bool) → FtpNF → FtpNF
  | term, [] => [term]
  | (m, c), (p, e) :: rest =>
      match csrCompare m p with
      | CsrMonoOrd.eq => (p, ftpCoeffXor e c) :: rest
      | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
      | CsrMonoOrd.gt => (p, e) :: ftpInsertTerm (m, c) rest
theorem ftpInsertTermNil (m : List Nat) (c : Bool) : ftpInsertTerm (m, c) [] = [(m, c)] := rfl
theorem ftpInsertTermEqE (m : List Nat) (c : Bool) (p : List Nat) (e : Bool) (rest : FtpNF)
    (h : csrCompare m p = CsrMonoOrd.eq) :
    ftpInsertTerm (m, c) ((p, e) :: rest) = (p, ftpCoeffXor e c) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, ftpCoeffXor e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: ftpInsertTerm (m, c) rest) = (p, ftpCoeffXor e c) :: rest
  rw [h]
theorem ftpInsertTermLtE (m : List Nat) (c : Bool) (p : List Nat) (e : Bool) (rest : FtpNF)
    (h : csrCompare m p = CsrMonoOrd.lt) :
    ftpInsertTerm (m, c) ((p, e) :: rest) = (m, c) :: (p, e) :: rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, ftpCoeffXor e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: ftpInsertTerm (m, c) rest) = (m, c) :: (p, e) :: rest
  rw [h]
theorem ftpInsertTermGtE (m : List Nat) (c : Bool) (p : List Nat) (e : Bool) (rest : FtpNF)
    (h : csrCompare m p = CsrMonoOrd.gt) :
    ftpInsertTerm (m, c) ((p, e) :: rest) = (p, e) :: ftpInsertTerm (m, c) rest := by
  show (match csrCompare m p with
        | CsrMonoOrd.eq => (p, ftpCoeffXor e c) :: rest
        | CsrMonoOrd.lt => (m, c) :: (p, e) :: rest
        | CsrMonoOrd.gt => (p, e) :: ftpInsertTerm (m, c) rest) = (p, e) :: ftpInsertTerm (m, c) rest
  rw [h]

/-- ★ The crux commutation: two term-insertions commute (permutation-invariance of the XOR merge).
Structurally identical to the ℤ[X] sibling's `fcrInsertTermComm`, with `Bool` coefficient xor. -/
theorem ftpInsertTermComm (m : List Nat) (c : Bool) (n : List Nat) (d : Bool) (P : FtpNF) :
    ftpInsertTerm (m, c) (ftpInsertTerm (n, d) P)
      = ftpInsertTerm (n, d) (ftpInsertTerm (m, c) P) := by
  induction P with
  | nil =>
      cases hmn : csrCompare m n with
      | eq =>
          have hmeqn : m = n := csrCompareEq_of m n hmn
          have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
          rw [ftpInsertTermNil n d, ftpInsertTermNil m c,
              ftpInsertTermEqE m c n d [] hmn, ftpInsertTermEqE n d m c [] hnm, hmeqn,
              ftpCoeffXorComm d c]
      | lt =>
          have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
          rw [ftpInsertTermNil n d, ftpInsertTermNil m c,
              ftpInsertTermLtE m c n d [] hmn, ftpInsertTermGtE n d m c [] hnm, ftpInsertTermNil n d]
      | gt =>
          have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn
          rw [ftpInsertTermNil n d, ftpInsertTermNil m c,
              ftpInsertTermGtE m c n d [] hmn, ftpInsertTermNil m c, ftpInsertTermLtE n d m c [] hnm]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [ftpInsertTermEqE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [ftpInsertTermEqE m c p (ftpCoeffXor e d) rest hmp, ftpInsertTermEqE m c p e rest hmp,
                  ftpInsertTermEqE n d p (ftpCoeffXor e c) rest hnp, ftpCoeffXorRightComm e d c]
          | lt =>
              have hpm : csrCompare p m = CsrMonoOrd.gt := csrCompareSwapLt m p hmp
              have hnm : csrCompare n m = CsrMonoOrd.gt := by rw [hnp_eq]; exact hpm
              rw [ftpInsertTermLtE m c p (ftpCoeffXor e d) rest hmp, ftpInsertTermLtE m c p e rest hmp,
                  ftpInsertTermGtE n d m c ((p, e) :: rest) hnm, ftpInsertTermEqE n d p e rest hnp]
          | gt =>
              rw [ftpInsertTermGtE m c p (ftpCoeffXor e d) rest hmp, ftpInsertTermGtE m c p e rest hmp,
                  ftpInsertTermEqE n d p e (ftpInsertTerm (m, c) rest) hnp]
      | lt =>
          rw [ftpInsertTermLtE n d p e rest hnp]
          cases hmn : csrCompare m n with
          | eq =>
              have hmeqn : m = n := csrCompareEq_of m n hmn
              have hnm : csrCompare n m = CsrMonoOrd.eq := csrCompareOfEq n m hmeqn.symm
              have hmp : csrCompare m p = CsrMonoOrd.lt := by rw [hmeqn]; exact hnp
              rw [ftpInsertTermEqE m c n d ((p, e) :: rest) hmn, ftpInsertTermLtE m c p e rest hmp,
                  ftpInsertTermEqE n d m c ((p, e) :: rest) hnm, hmeqn, ftpCoeffXorComm d c]
          | lt =>
              have hmp : csrCompare m p = CsrMonoOrd.lt := csrCompareTransLt m n p hmn hnp
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [ftpInsertTermLtE m c n d ((p, e) :: rest) hmn, ftpInsertTermLtE m c p e rest hmp,
                  ftpInsertTermGtE n d m c ((p, e) :: rest) hnm, ftpInsertTermLtE n d p e rest hnp]
          | gt =>
              have hmn_gt : csrCompare m n = CsrMonoOrd.gt := hmn
              rw [ftpInsertTermGtE m c n d ((p, e) :: rest) hmn]
              cases hmp : csrCompare m p with
              | eq =>
                  rw [ftpInsertTermEqE m c p e rest hmp,
                      ftpInsertTermLtE n d p (ftpCoeffXor e c) rest hnp]
              | lt =>
                  have hnm : csrCompare n m = CsrMonoOrd.lt := csrCompareSwapGt m n hmn_gt
                  rw [ftpInsertTermLtE m c p e rest hmp,
                      ftpInsertTermLtE n d m c ((p, e) :: rest) hnm]
              | gt =>
                  rw [ftpInsertTermGtE m c p e rest hmp,
                      ftpInsertTermLtE n d p e (ftpInsertTerm (m, c) rest) hnp]
      | gt =>
          rw [ftpInsertTermGtE n d p e rest hnp]
          cases hmp : csrCompare m p with
          | eq =>
              rw [ftpInsertTermEqE m c p e (ftpInsertTerm (n, d) rest) hmp,
                  ftpInsertTermEqE m c p e rest hmp,
                  ftpInsertTermGtE n d p (ftpCoeffXor e c) rest hnp]
          | lt =>
              have hpn : csrCompare p n = CsrMonoOrd.lt := csrCompareSwapGt n p hnp
              have hmn : csrCompare m n = CsrMonoOrd.lt := csrCompareTransLt m p n hmp hpn
              have hnm : csrCompare n m = CsrMonoOrd.gt := csrCompareSwapLt m n hmn
              rw [ftpInsertTermLtE m c p e (ftpInsertTerm (n, d) rest) hmp,
                  ftpInsertTermLtE m c p e rest hmp,
                  ftpInsertTermGtE n d m c ((p, e) :: rest) hnm,
                  ftpInsertTermGtE n d p e rest hnp]
          | gt =>
              rw [ftpInsertTermGtE m c p e (ftpInsertTerm (n, d) rest) hmp,
                  ftpInsertTermGtE m c p e rest hmp,
                  ftpInsertTermGtE n d p e (ftpInsertTerm (m, c) rest) hnp, ih]

/-- The additive XOR merge: insert every term of the first list into the second. -/
def ftpMergeXor : FtpNF → FtpNF → FtpNF
  | [], b => b
  | t :: a', b => ftpInsertTerm t (ftpMergeXor a' b)
theorem ftpMergeXorNilLeft (b : FtpNF) : ftpMergeXor [] b = b := rfl
theorem ftpMergeXorCons (t : List Nat × Bool) (a' b : FtpNF) :
    ftpMergeXor (t :: a') b = ftpInsertTerm t (ftpMergeXor a' b) := rfl
theorem ftpInsertTerm_mergeXor (t : List Nat × Bool) (a b : FtpNF) :
    ftpInsertTerm t (ftpMergeXor a b) = ftpMergeXor a (ftpInsertTerm t b) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      obtain ⟨um, uc⟩ := u
      obtain ⟨tm, tc⟩ := t
      show ftpInsertTerm (tm, tc) (ftpInsertTerm (um, uc) (ftpMergeXor a' b))
        = ftpMergeXor ((um, uc) :: a') (ftpInsertTerm (tm, tc) b)
      rw [ftpMergeXorCons, ftpInsertTermComm tm tc um uc (ftpMergeXor a' b), ih]
/-- Inserting the same monomial twice XORs the two coefficients. -/
theorem ftpInsertTermMergeSame (m : List Nat) (c1 c2 : Bool) (Z : FtpNF) :
    ftpInsertTerm (m, c1) (ftpInsertTerm (m, c2) Z) = ftpInsertTerm (m, ftpCoeffXor c2 c1) Z := by
  induction Z with
  | nil =>
      rw [ftpInsertTermNil m c2, ftpInsertTermEqE m c1 m c2 [] (csrCompareRefl m),
          ftpInsertTermNil m (ftpCoeffXor c2 c1)]
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          rw [ftpInsertTermEqE m c2 p e rest hmp, ftpInsertTermEqE m c1 p (ftpCoeffXor e c2) rest hmp,
              ftpInsertTermEqE m (ftpCoeffXor c2 c1) p e rest hmp, ftpCoeffXorAssoc e c2 c1]
      | lt =>
          rw [ftpInsertTermLtE m c2 p e rest hmp, ftpInsertTermEqE m c1 m c2 ((p, e) :: rest)
                (csrCompareRefl m), ftpInsertTermLtE m (ftpCoeffXor c2 c1) p e rest hmp]
      | gt =>
          rw [ftpInsertTermGtE m c2 p e rest hmp, ftpInsertTermGtE m c1 p e
                (ftpInsertTerm (m, c2) rest) hmp, ftpInsertTermGtE m (ftpCoeffXor c2 c1) p e rest hmp, ih]
/-- Pulling an insertion out of the left list of a merge. -/
theorem ftpMergeXorInsertTermLeft (u : List Nat × Bool) (Y c : FtpNF) :
    ftpMergeXor (ftpInsertTerm u Y) c = ftpInsertTerm u (ftpMergeXor Y c) := by
  obtain ⟨um, uc⟩ := u
  induction Y with
  | nil => rfl
  | cons head Y' ih =>
      obtain ⟨v, ve⟩ := head
      cases huv : csrCompare um v with
      | eq =>
          have hum_eq : um = v := csrCompareEq_of um v huv
          rw [ftpInsertTermEqE um uc v ve Y' huv, ftpMergeXorCons,
              ftpMergeXorCons (v, ve) Y' c, hum_eq,
              ftpInsertTermMergeSame v uc ve (ftpMergeXor Y' c)]
      | lt =>
          rw [ftpInsertTermLtE um uc v ve Y' huv, ftpMergeXorCons, ftpMergeXorCons (v, ve) Y' c]
      | gt =>
          rw [ftpInsertTermGtE um uc v ve Y' huv, ftpMergeXorCons (v, ve) (ftpInsertTerm (um, uc) Y') c,
              ftpMergeXorCons (v, ve) Y' c, ih,
              ftpInsertTermComm v ve um uc (ftpMergeXor Y' c)]
theorem ftpMergeXorAssoc (a b c : FtpNF) :
    ftpMergeXor (ftpMergeXor a b) c = ftpMergeXor a (ftpMergeXor b c) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show ftpMergeXor (ftpInsertTerm u (ftpMergeXor a' b)) c
        = ftpInsertTerm u (ftpMergeXor a' (ftpMergeXor b c))
      rw [ftpMergeXorInsertTermLeft u (ftpMergeXor a' b) c, ih]
theorem ftpMergeXorSwap (a b acc : FtpNF) :
    ftpMergeXor a (ftpMergeXor b acc) = ftpMergeXor b (ftpMergeXor a acc) := by
  induction a with
  | nil => rfl
  | cons u a' ih =>
      show ftpInsertTerm u (ftpMergeXor a' (ftpMergeXor b acc))
        = ftpMergeXor b (ftpInsertTerm u (ftpMergeXor a' acc))
      rw [ih, ftpInsertTerm_mergeXor u b (ftpMergeXor a' acc)]

/-! ## The strict-sortedness invariant on the normal form -/

def ftpBelowHead (m : List Nat) : FtpNF → Bool
  | [] => true
  | (p, _) :: _ =>
      match csrCompare m p with
      | CsrMonoOrd.lt => true
      | CsrMonoOrd.eq => false
      | CsrMonoOrd.gt => false
def ftpNFSorted : FtpNF → Bool
  | [] => true
  | (m, _) :: rest => ftpBelowHead m rest && ftpNFSorted rest
theorem ftpBelowHeadNil (m : List Nat) : ftpBelowHead m [] = true := rfl
theorem ftpBelowHeadConsTrue (m p : List Nat) (e : Bool) (rest : FtpNF)
    (h : csrCompare m p = CsrMonoOrd.lt) : ftpBelowHead m ((p, e) :: rest) = true := by
  show (match csrCompare m p with
        | CsrMonoOrd.lt => true
        | CsrMonoOrd.eq => false
        | CsrMonoOrd.gt => false) = true
  rw [h]
theorem ftpBelowHeadConsLt (m p : List Nat) (e : Bool) (rest : FtpNF)
    (h : ftpBelowHead m ((p, e) :: rest) = true) : csrCompare m p = CsrMonoOrd.lt := by
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
theorem ftpNFSortedCons (m : List Nat) (c : Bool) (rest : FtpNF) :
    ftpNFSorted ((m, c) :: rest) = (ftpBelowHead m rest && ftpNFSorted rest) := rfl
theorem ftpBelowHeadInsert (q m : List Nat) (c : Bool) (B : FtpNF)
    (hq : csrCompare q m = CsrMonoOrd.lt) (hB : ftpBelowHead q B = true) :
    ftpBelowHead q (ftpInsertTerm (m, c) B) = true := by
  cases B with
  | nil => exact ftpBelowHeadConsTrue q m c [] hq
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq => rw [ftpInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [ftpInsertTermLtE m c p e rest hmp]; exact ftpBelowHeadConsTrue q m c ((p, e) :: rest) hq
      | gt =>
          rw [ftpInsertTermGtE m c p e rest hmp]
          exact ftpBelowHeadConsTrue q p e (ftpInsertTerm (m, c) rest) (ftpBelowHeadConsLt q p e rest hB)
theorem ftpInsertPreservesSorted (m : List Nat) (c : Bool) (B : FtpNF)
    (hB : ftpNFSorted B = true) : ftpNFSorted (ftpInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hbelow : ftpBelowHead p rest = true := csrAndTrueLeft _ _ hB
      have hrest : ftpNFSorted rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq => rw [ftpInsertTermEqE m c p e rest hmp]; exact hB
      | lt =>
          rw [ftpInsertTermLtE m c p e rest hmp, ftpNFSortedCons]
          exact csrAndIntro _ _ (ftpBelowHeadConsTrue m p e rest hmp) hB
      | gt =>
          rw [ftpInsertTermGtE m c p e rest hmp, ftpNFSortedCons]
          have hpm : csrCompare p m = CsrMonoOrd.lt := csrCompareSwapGt m p hmp
          exact csrAndIntro _ _
            (ftpBelowHeadInsert p m c rest hpm hbelow) (ih hrest)
theorem ftpInsertFront (m : List Nat) (c : Bool) (B : FtpNF) (h : ftpBelowHead m B = true) :
    ftpInsertTerm (m, c) B = (m, c) :: B := by
  cases B with
  | nil => rfl
  | cons head rest =>
      obtain ⟨p, e⟩ := head
      exact ftpInsertTermLtE m c p e rest (ftpBelowHeadConsLt m p e rest h)
theorem ftpMergeXorNilRight (A : FtpNF) (hA : ftpNFSorted A = true) : ftpMergeXor A [] = A := by
  induction A with
  | nil => rfl
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      have hbelow : ftpBelowHead m a' = true := csrAndTrueLeft _ _ hA
      have hrest : ftpNFSorted a' = true := csrAndTrueRight _ _ hA
      show ftpInsertTerm (m, c) (ftpMergeXor a' []) = (m, c) :: a'
      rw [ih hrest, ftpInsertFront m c a' hbelow]
theorem ftpMergeXorComm (A B : FtpNF) (hA : ftpNFSorted A = true) (hB : ftpNFSorted B = true) :
    ftpMergeXor A B = ftpMergeXor B A := by
  have h := ftpMergeXorSwap A B []
  rw [ftpMergeXorNilRight B hB, ftpMergeXorNilRight A hA] at h
  exact h
theorem ftpMergeXorPreservesSorted (A B : FtpNF) (hB : ftpNFSorted B = true) :
    ftpNFSorted (ftpMergeXor A B) = true := by
  induction A with
  | nil => exact hB
  | cons head a' ih =>
      obtain ⟨m, c⟩ := head
      show ftpNFSorted (ftpInsertTerm (m, c) (ftpMergeXor a' B)) = true
      exact ftpInsertPreservesSorted m c (ftpMergeXor a' B) ih

/-! ## The multiplicative convolution (monomial set-union × coefficient `and`) -/

/-- A single term `(m, c)` times a polynomial: monomial product is the set-union `ftpMonoMul`, coefficient
product is `ftpCoeffAnd`. -/
def ftpTermMul (m : List Nat) (c : Bool) : FtpNF → FtpNF
  | [] => []
  | (n, d) :: rest => ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c rest)
/-- The Cauchy convolution of two polynomials. -/
def ftpMulConvolve : FtpNF → FtpNF → FtpNF
  | [], _ => []
  | (m, c) :: rest, b => ftpMergeXor (ftpTermMul m c b) (ftpMulConvolve rest b)
theorem ftpTermMulNil (m : List Nat) (c : Bool) : ftpTermMul m c [] = [] := rfl
theorem ftpTermMulCons (m : List Nat) (c : Bool) (n : List Nat) (d : Bool) (rest : FtpNF) :
    ftpTermMul m c ((n, d) :: rest) = ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c rest) := rfl
theorem ftpMulConvolveNil (b : FtpNF) : ftpMulConvolve [] b = [] := rfl
theorem ftpMulConvolveCons (m : List Nat) (c : Bool) (rest b : FtpNF) :
    ftpMulConvolve ((m, c) :: rest) b = ftpMergeXor (ftpTermMul m c b) (ftpMulConvolve rest b) := rfl
theorem ftpTermMulSorted (m : List Nat) (c : Bool) (B : FtpNF) :
    ftpNFSorted (ftpTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show ftpNFSorted (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c rest)) = true
      exact ftpInsertPreservesSorted (ftpMonoMul m n) (ftpCoeffAnd c d) (ftpTermMul m c rest) ih
theorem ftpMulConvolveSorted (A B : FtpNF) : ftpNFSorted (ftpMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show ftpNFSorted (ftpMergeXor (ftpTermMul m c B) (ftpMulConvolve rest B)) = true
      exact ftpMergeXorPreservesSorted (ftpTermMul m c B) (ftpMulConvolve rest B) ih
/-- termMul commutes with a single insertion (coefficients distribute via `ftpCoeffAndXorRight`). -/
theorem ftpTermMul_insertTerm (m : List Nat) (c : Bool) (n : List Nat) (d : Bool) (B : FtpNF) :
    ftpTermMul m c (ftpInsertTerm (n, d) B)
      = ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hnp_eq : n = p := csrCompareEq_of n p hnp
          rw [ftpInsertTermEqE n d p e rest hnp, ftpTermMulCons m c p (ftpCoeffXor e d) rest,
              ftpTermMulCons m c p e rest, hnp_eq,
              ftpInsertTermMergeSame (ftpMonoMul m p) (ftpCoeffAnd c d) (ftpCoeffAnd c e)
                (ftpTermMul m c rest), ftpCoeffAndXorRight c e d]
      | lt =>
          rw [ftpInsertTermLtE n d p e rest hnp, ftpTermMulCons m c n d ((p, e) :: rest),
              ftpTermMulCons m c p e rest]
      | gt =>
          rw [ftpInsertTermGtE n d p e rest hnp, ftpTermMulCons m c p e (ftpInsertTerm (n, d) rest),
              ih, ftpTermMulCons m c p e rest,
              ftpInsertTermComm (ftpMonoMul m p) (ftpCoeffAnd c e) (ftpMonoMul m n) (ftpCoeffAnd c d)
                (ftpTermMul m c rest)]
theorem ftpTermMul_merge (m : List Nat) (c : Bool) (B C : FtpNF) :
    ftpTermMul m c (ftpMergeXor B C) = ftpMergeXor (ftpTermMul m c B) (ftpTermMul m c C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show ftpTermMul m c (ftpInsertTerm (n, d) (ftpMergeXor B' C))
        = ftpMergeXor (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c B')) (ftpTermMul m c C)
      rw [ftpTermMul_insertTerm m c n d (ftpMergeXor B' C), ih,
          ftpMergeXorInsertTermLeft (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c B') (ftpTermMul m c C)]
theorem ftpMulConvolveAnnihil (A : FtpNF) : ftpMulConvolve A [] = [] := by
  induction A with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      show ftpMergeXor (ftpTermMul m c []) (ftpMulConvolve rest []) = []
      rw [ftpTermMulNil m c, ftpMergeXorNilLeft, ih]
/-- Rearrange a merge of four sorted NFs, swapping the inner two. -/
theorem ftpMergeXor4Swap (a b c d : FtpNF)
    (hb : ftpNFSorted b = true) (hc : ftpNFSorted c = true) :
    ftpMergeXor (ftpMergeXor a b) (ftpMergeXor c d)
      = ftpMergeXor (ftpMergeXor a c) (ftpMergeXor b d) := by
  rw [ftpMergeXorAssoc a b (ftpMergeXor c d), ← ftpMergeXorAssoc b c d,
      ftpMergeXorComm b c hb hc, ftpMergeXorAssoc c b d, ← ftpMergeXorAssoc a c (ftpMergeXor b d)]
/-- ★ left distributivity: `A · (B + C) = A·B + A·C`. -/
theorem ftpMulConvolve_leftDistrib (A B C : FtpNF) :
    ftpMulConvolve A (ftpMergeXor B C)
      = ftpMergeXor (ftpMulConvolve A B) (ftpMulConvolve A C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show ftpMergeXor (ftpTermMul m c (ftpMergeXor B C)) (ftpMulConvolve A' (ftpMergeXor B C))
        = ftpMergeXor (ftpMergeXor (ftpTermMul m c B) (ftpMulConvolve A' B))
            (ftpMergeXor (ftpTermMul m c C) (ftpMulConvolve A' C))
      rw [ftpTermMul_merge m c B C, ih]
      exact ftpMergeXor4Swap (ftpTermMul m c B) (ftpTermMul m c C) (ftpMulConvolve A' B)
        (ftpMulConvolve A' C) (ftpTermMulSorted m c C) (ftpMulConvolveSorted A' B)
/-- termMul distributes over a coefficient XOR. -/
theorem ftpTermMul_coeffXor (m : List Nat) (c1 c2 : Bool) (Z : FtpNF) :
    ftpTermMul m (ftpCoeffXor c1 c2) Z = ftpMergeXor (ftpTermMul m c1 Z) (ftpTermMul m c2 Z) := by
  induction Z with
  | nil => rfl
  | cons head Z' ih =>
      obtain ⟨n, d⟩ := head
      show ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd (ftpCoeffXor c1 c2) d) (ftpTermMul m (ftpCoeffXor c1 c2) Z')
        = ftpMergeXor (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c1 d) (ftpTermMul m c1 Z'))
            (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c2 d) (ftpTermMul m c2 Z'))
      rw [ftpMergeXorInsertTermLeft (ftpMonoMul m n, ftpCoeffAnd c1 d) (ftpTermMul m c1 Z')
            (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c2 d) (ftpTermMul m c2 Z')),
          ← ftpInsertTerm_mergeXor (ftpMonoMul m n, ftpCoeffAnd c2 d) (ftpTermMul m c1 Z') (ftpTermMul m c2 Z'),
          ftpInsertTermMergeSame (ftpMonoMul m n) (ftpCoeffAnd c1 d) (ftpCoeffAnd c2 d)
            (ftpMergeXor (ftpTermMul m c1 Z') (ftpTermMul m c2 Z')),
          ih, ftpCoeffXorAndRight c1 c2 d, ftpCoeffXorComm (ftpCoeffAnd c1 d) (ftpCoeffAnd c2 d)]
/-- convolving after one insertion into the first argument. -/
theorem ftpConvolve_insertTermLeft (m : List Nat) (c : Bool) (W Z : FtpNF) :
    ftpMulConvolve (ftpInsertTerm (m, c) W) Z
      = ftpMergeXor (ftpTermMul m c Z) (ftpMulConvolve W Z) := by
  induction W with
  | nil => rfl
  | cons head W' ih =>
      obtain ⟨p, g⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [ftpInsertTermEqE m c p g W' hmp, ftpMulConvolveCons p (ftpCoeffXor g c) W' Z,
              ftpMulConvolveCons p g W' Z, hmeqp,
              ftpTermMul_coeffXor p g c Z,
              ftpMergeXorAssoc (ftpTermMul p g Z) (ftpTermMul p c Z) (ftpMulConvolve W' Z),
              ftpMergeXorSwap (ftpTermMul p g Z) (ftpTermMul p c Z) (ftpMulConvolve W' Z)]
      | lt =>
          rw [ftpInsertTermLtE m c p g W' hmp, ftpMulConvolveCons m c ((p, g) :: W') Z]
      | gt =>
          rw [ftpInsertTermGtE m c p g W' hmp,
              ftpMulConvolveCons p g (ftpInsertTerm (m, c) W') Z, ih,
              ftpMulConvolveCons p g W' Z,
              ftpMergeXorSwap (ftpTermMul p g Z) (ftpTermMul m c Z) (ftpMulConvolve W' Z)]
/-- ★ right distributivity: `(X + Y) · Z = X·Z + Y·Z`. -/
theorem ftpMulConvolve_rightDistrib (X Y Z : FtpNF) :
    ftpMulConvolve (ftpMergeXor X Y) Z
      = ftpMergeXor (ftpMulConvolve X Z) (ftpMulConvolve Y Z) := by
  induction X with
  | nil => rfl
  | cons head X' ih =>
      obtain ⟨m, c⟩ := head
      show ftpMulConvolve (ftpInsertTerm (m, c) (ftpMergeXor X' Y)) Z
        = ftpMergeXor (ftpMergeXor (ftpTermMul m c Z) (ftpMulConvolve X' Z)) (ftpMulConvolve Y Z)
      rw [ftpConvolve_insertTermLeft m c (ftpMergeXor X' Y) Z, ih,
          ftpMergeXorAssoc (ftpTermMul m c Z) (ftpMulConvolve X' Z) (ftpMulConvolve Y Z)]
/-- termMul composition: `(m ⊎ n)·(c ∧ d)` applied to `C` equals scaling by `(m,c)` then `(n,d)`. -/
theorem ftpTermMul_compose (m : List Nat) (c : Bool) (n : List Nat) (d : Bool) (C : FtpNF) :
    ftpTermMul (ftpMonoMul m n) (ftpCoeffAnd c d) C = ftpTermMul m c (ftpTermMul n d C) := by
  induction C with
  | nil => rfl
  | cons head C' ih =>
      obtain ⟨p, f⟩ := head
      show ftpInsertTerm (ftpMonoMul (ftpMonoMul m n) p, ftpCoeffAnd (ftpCoeffAnd c d) f)
            (ftpTermMul (ftpMonoMul m n) (ftpCoeffAnd c d) C')
        = ftpTermMul m c (ftpInsertTerm (ftpMonoMul n p, ftpCoeffAnd d f) (ftpTermMul n d C'))
      rw [ftpTermMul_insertTerm m c (ftpMonoMul n p) (ftpCoeffAnd d f) (ftpTermMul n d C'), ih,
          ftpMonoMulAssoc m n p, ftpCoeffAndAssoc c d f]
/-- convolving a termMul equals termMul of a convolve. -/
theorem ftpTermMul_convolve (m : List Nat) (c : Bool) (B C : FtpNF) :
    ftpMulConvolve (ftpTermMul m c B) C = ftpTermMul m c (ftpMulConvolve B C) := by
  induction B with
  | nil => rfl
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show ftpMulConvolve (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c B')) C
        = ftpTermMul m c (ftpMergeXor (ftpTermMul n d C) (ftpMulConvolve B' C))
      rw [ftpConvolve_insertTermLeft (ftpMonoMul m n) (ftpCoeffAnd c d) (ftpTermMul m c B') C, ih,
          ftpTermMul_merge m c (ftpTermMul n d C) (ftpMulConvolve B' C),
          ftpTermMul_compose m c n d C]
/-- ★ associativity of the convolution: `(A·B)·C = A·(B·C)`. -/
theorem ftpMulConvolveAssoc (A B C : FtpNF) :
    ftpMulConvolve (ftpMulConvolve A B) C = ftpMulConvolve A (ftpMulConvolve B C) := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show ftpMulConvolve (ftpMergeXor (ftpTermMul m c B) (ftpMulConvolve A' B)) C
        = ftpMergeXor (ftpTermMul m c (ftpMulConvolve B C)) (ftpMulConvolve A' (ftpMulConvolve B C))
      rw [ftpMulConvolve_rightDistrib (ftpTermMul m c B) (ftpMulConvolve A' B) C, ih,
          ftpTermMul_convolve m c B C]

/-! ## Monomial-sortedness of every term, and convolution commutativity / unit -/

def ftpNFMonoSorted : FtpNF → Bool
  | [] => true
  | (m, _) :: rest => ftpMonoSorted m && ftpNFMonoSorted rest
theorem ftpNFMonoSortedCons (m : List Nat) (c : Bool) (rest : FtpNF) :
    ftpNFMonoSorted ((m, c) :: rest) = (ftpMonoSorted m && ftpNFMonoSorted rest) := rfl
theorem ftpInsertTermMonoSorted (m : List Nat) (c : Bool) (B : FtpNF)
    (hm : ftpMonoSorted m = true) (hB : ftpNFMonoSorted B = true) :
    ftpNFMonoSorted (ftpInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rw [ftpInsertTermNil m c, ftpNFMonoSortedCons]; exact csrAndIntro _ _ hm rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have hp : ftpMonoSorted p = true := csrAndTrueLeft _ _ hB
      have hrest : ftpNFMonoSorted rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq => rw [ftpInsertTermEqE m c p e rest hmp]; exact hB
      | lt => rw [ftpInsertTermLtE m c p e rest hmp, ftpNFMonoSortedCons]; exact csrAndIntro _ _ hm hB
      | gt =>
          rw [ftpInsertTermGtE m c p e rest hmp, ftpNFMonoSortedCons]
          exact csrAndIntro _ _ hp (ih hrest)
theorem ftpMergeXorMonoSorted (A B : FtpNF) (hA : ftpNFMonoSorted A = true)
    (hB : ftpNFMonoSorted B = true) : ftpNFMonoSorted (ftpMergeXor A B) = true := by
  induction A with
  | nil => exact hB
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hm : ftpMonoSorted m = true := csrAndTrueLeft _ _ hA
      have hA' : ftpNFMonoSorted A' = true := csrAndTrueRight _ _ hA
      show ftpNFMonoSorted (ftpInsertTerm (m, c) (ftpMergeXor A' B)) = true
      exact ftpInsertTermMonoSorted m c (ftpMergeXor A' B) hm (ih hA')
theorem ftpTermMulMonoSorted (m : List Nat) (c : Bool) (B : FtpNF) (hm : ftpMonoSorted m = true) :
    ftpNFMonoSorted (ftpTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show ftpNFMonoSorted (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c rest)) = true
      exact ftpInsertTermMonoSorted (ftpMonoMul m n) (ftpCoeffAnd c d) (ftpTermMul m c rest)
        (ftpMonoMulSorted m n hm) ih
theorem ftpMulConvolveMonoSorted (A B : FtpNF) (hA : ftpNFMonoSorted A = true)
    (_hB : ftpNFMonoSorted B = true) : ftpNFMonoSorted (ftpMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hm : ftpMonoSorted m = true := csrAndTrueLeft _ _ hA
      have hA' : ftpNFMonoSorted A' = true := csrAndTrueRight _ _ hA
      show ftpNFMonoSorted (ftpMergeXor (ftpTermMul m c B) (ftpMulConvolve A' B)) = true
      exact ftpMergeXorMonoSorted (ftpTermMul m c B) (ftpMulConvolve A' B)
        (ftpTermMulMonoSorted m c B hm) (ih hA')
/-- termMul equals convolving with a single-term poly (needs sorted monomials for `ftpMonoMul` comm). -/
theorem ftpTermMulEqConvolveSingle (m : List Nat) (c : Bool) (hm : ftpMonoSorted m = true) :
    (B : FtpNF) → ftpNFMonoSorted B = true → ftpTermMul m c B = ftpMulConvolve B [(m, c)]
  | [], _ => rfl
  | (n, d) :: B', hB => by
      have hn : ftpMonoSorted n = true := csrAndTrueLeft _ _ hB
      have hB' : ftpNFMonoSorted B' = true := csrAndTrueRight _ _ hB
      have ih := ftpTermMulEqConvolveSingle m c hm B' hB'
      show ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c B')
        = ftpMergeXor (ftpTermMul n d [(m, c)]) (ftpMulConvolve B' [(m, c)])
      rw [ftpTermMulCons n d m c [], ftpTermMulNil n d,
          ftpMergeXorInsertTermLeft (ftpMonoMul n m, ftpCoeffAnd d c) [] (ftpMulConvolve B' [(m, c)]),
          ftpMergeXorNilLeft, ← ih, ftpMonoMulComm m n hm hn, ftpCoeffAndComm c d]
/-- ★ commutativity of the convolution (needs sorted first arg + sorted monomials). -/
theorem ftpMulConvolveComm : (A B : FtpNF) → ftpNFSorted A = true → ftpNFMonoSorted A = true →
    ftpNFMonoSorted B = true → ftpMulConvolve A B = ftpMulConvolve B A
  | [], B, _, _, _ => (ftpMulConvolveAnnihil B).symm
  | (m, c) :: A', B, hAs, hAm, hBm => by
      have hbelow : ftpBelowHead m A' = true := csrAndTrueLeft _ _ hAs
      have hAs' : ftpNFSorted A' = true := csrAndTrueRight _ _ hAs
      have hm : ftpMonoSorted m = true := csrAndTrueLeft _ _ hAm
      have hAm' : ftpNFMonoSorted A' = true := csrAndTrueRight _ _ hAm
      have ih := ftpMulConvolveComm A' B hAs' hAm' hBm
      show ftpMergeXor (ftpTermMul m c B) (ftpMulConvolve A' B) = ftpMulConvolve B ((m, c) :: A')
      rw [ftpTermMulEqConvolveSingle m c hm B hBm, ih,
          ← ftpMulConvolve_leftDistrib B [(m, c)] A', ftpMergeXorCons (m, c) [] A',
          ftpMergeXorNilLeft, ftpInsertFront m c A' hbelow]
/-- ★ multiplicative unit: `A · [([], true)] = A` for a sorted NF. -/
theorem ftpMulConvolveUnit : (A : FtpNF) → ftpNFSorted A = true → ftpMulConvolve A [([], true)] = A
  | [], _ => rfl
  | (m, c) :: A', hAs => by
      have hbelow : ftpBelowHead m A' = true := csrAndTrueLeft _ _ hAs
      have hAs' : ftpNFSorted A' = true := csrAndTrueRight _ _ hAs
      have ih := ftpMulConvolveUnit A' hAs'
      show ftpMergeXor (ftpTermMul m c [([], true)]) (ftpMulConvolve A' [([], true)]) = (m, c) :: A'
      rw [ftpTermMulCons m c [] true [], ftpTermMulNil m c, ftpMonoMulNilRight m, ftpCoeffAndTrueRight c,
          ftpMergeXorInsertTermLeft (m, c) [] (ftpMulConvolve A' [([], true)]), ftpMergeXorNilLeft,
          ih, ftpInsertFront m c A' hbelow]

/-! ## The all-absent predicate and its closure lemmas -/

/-- Every coefficient is absent (`false`).  The single-list structural check underlying the decision. -/
def ftpNFAllZero : FtpNF → Bool
  | [] => true
  | (_, c) :: rest => ftpCoeffIsZero c && ftpNFAllZero rest
theorem ftpNFAllZeroCons (m : List Nat) (c : Bool) (rest : FtpNF) :
    ftpNFAllZero ((m, c) :: rest) = (ftpCoeffIsZero c && ftpNFAllZero rest) := rfl
theorem ftpInsertTermAllZero (m : List Nat) (c : Bool) (B : FtpNF)
    (hc : ftpCoeffIsZero c = true) (hB : ftpNFAllZero B = true) :
    ftpNFAllZero (ftpInsertTerm (m, c) B) = true := by
  induction B with
  | nil => rw [ftpInsertTermNil m c, ftpNFAllZeroCons]; exact csrAndIntro _ _ hc rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      have he : ftpCoeffIsZero e = true := csrAndTrueLeft _ _ hB
      have hrest : ftpNFAllZero rest = true := csrAndTrueRight _ _ hB
      cases hmp : csrCompare m p with
      | eq =>
          rw [ftpInsertTermEqE m c p e rest hmp, ftpNFAllZeroCons]
          exact csrAndIntro _ _ (ftpCoeffXorZeroValued e c he hc) hrest
      | lt =>
          rw [ftpInsertTermLtE m c p e rest hmp, ftpNFAllZeroCons]
          exact csrAndIntro _ _ hc hB
      | gt =>
          rw [ftpInsertTermGtE m c p e rest hmp, ftpNFAllZeroCons]
          exact csrAndIntro _ _ he (ih hrest)
theorem ftpMergeXorAllZero (A B : FtpNF) (hA : ftpNFAllZero A = true) (hB : ftpNFAllZero B = true) :
    ftpNFAllZero (ftpMergeXor A B) = true := by
  induction A with
  | nil => exact hB
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hc : ftpCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hA' : ftpNFAllZero A' = true := csrAndTrueRight _ _ hA
      show ftpNFAllZero (ftpInsertTerm (m, c) (ftpMergeXor A' B)) = true
      exact ftpInsertTermAllZero m c (ftpMergeXor A' B) hc (ih hA')

/-! ## The `ftpEvalCross` semantic model: the per-monomial F2 coefficient -/

/-- The coefficient contributed by a term at a queried monomial: `d` on a match, `false` otherwise. -/
def ftpCondCoeff : Bool → Bool → Bool
  | true, d => d
  | false, _ => false
theorem ftpCondCoeffTrue (d : Bool) : ftpCondCoeff true d = d := rfl
theorem ftpCondCoeffFalse (d : Bool) : ftpCondCoeff false d = false := rfl
theorem ftpCondCoeffZero (b : Bool) (c : Bool) (hc : ftpCoeffIsZero c = true) :
    ftpCoeffIsZero (ftpCondCoeff b c) = true := by
  cases b with
  | true => exact hc
  | false => rfl
/-- A monomial `m` distinct from `q` (witnessed by `csrCompare m q = lt`) has `csrNatListEq m q = false`. -/
theorem ftpMonoEqFalseOfLt (m q : List Nat) (h : csrCompare m q = CsrMonoOrd.lt) :
    csrNatListEq m q = false := by
  cases hb : csrNatListEq m q with
  | false => rfl
  | true =>
      have hmq : m = q := csrNatListEq_eq m q hb
      rw [csrCompareOfEq m q hmq] at h
      exact CsrMonoOrd.noConfusion h
/-- The per-monomial F2 coefficient of a normal form. -/
def ftpEvalCross (m : List Nat) : FtpNF → Bool
  | [] => false
  | (p, c) :: rest => ftpCoeffXor (ftpCondCoeff (csrNatListEq m p) c) (ftpEvalCross m rest)
theorem ftpEvalCrossNil (m : List Nat) : ftpEvalCross m [] = false := rfl
theorem ftpEvalCrossCons (m p : List Nat) (c : Bool) (rest : FtpNF) :
    ftpEvalCross m ((p, c) :: rest) = ftpCoeffXor (ftpCondCoeff (csrNatListEq m p) c) (ftpEvalCross m rest) :=
  rfl
theorem ftpEvalCross_insertTerm (m n : List Nat) (d : Bool) (B : FtpNF) :
    ftpEvalCross m (ftpInsertTerm (n, d) B)
      = ftpCoeffXor (ftpCondCoeff (csrNatListEq m n) d) (ftpEvalCross m B) := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hnp : csrCompare n p with
      | eq =>
          have hn_eq : n = p := csrCompareEq_of n p hnp
          rw [ftpInsertTermEqE n d p e rest hnp, ftpEvalCrossCons, ftpEvalCrossCons, hn_eq]
          cases hmp : csrNatListEq m p with
          | true =>
              rw [ftpCondCoeffTrue, ftpCondCoeffTrue, ftpCondCoeffTrue,
                  ftpCoeffXorAssoc e d (ftpEvalCross m rest), ftpCoeffXorSwap13 e d (ftpEvalCross m rest)]
          | false =>
              rw [ftpCondCoeffFalse, ftpCondCoeffFalse, ftpCondCoeffFalse,
                  ftpCoeffXorFalseLeft, ftpCoeffXorFalseLeft]
      | lt =>
          rw [ftpInsertTermLtE n d p e rest hnp, ftpEvalCrossCons]
      | gt =>
          rw [ftpInsertTermGtE n d p e rest hnp, ftpEvalCrossCons, ih, ftpEvalCrossCons]
          exact ftpCoeffXorSwap13 (ftpCondCoeff (csrNatListEq m p) e)
            (ftpCondCoeff (csrNatListEq m n) d) (ftpEvalCross m rest)
theorem ftpEvalCross_mergeXor (m : List Nat) (A B : FtpNF) :
    ftpEvalCross m (ftpMergeXor A B) = ftpCoeffXor (ftpEvalCross m A) (ftpEvalCross m B) := by
  induction A with
  | nil => rw [ftpMergeXorNilLeft, ftpEvalCrossNil, ftpCoeffXorFalseLeft]
  | cons head A' ih =>
      obtain ⟨p, c⟩ := head
      show ftpEvalCross m (ftpInsertTerm (p, c) (ftpMergeXor A' B))
        = ftpCoeffXor (ftpCoeffXor (ftpCondCoeff (csrNatListEq m p) c) (ftpEvalCross m A')) (ftpEvalCross m B)
      rw [ftpEvalCross_insertTerm m p c (ftpMergeXor A' B), ih,
          ftpCoeffXorAssoc (ftpCondCoeff (csrNatListEq m p) c) (ftpEvalCross m A') (ftpEvalCross m B)]
theorem ftpAllZero_evalZero (m : List Nat) (W : FtpNF) (hW : ftpNFAllZero W = true) :
    ftpCoeffIsZero (ftpEvalCross m W) = true := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      have hc : ftpCoeffIsZero c = true := csrAndTrueLeft _ _ hW
      have hrest : ftpNFAllZero rest = true := csrAndTrueRight _ _ hW
      rw [ftpEvalCrossCons]
      exact ftpCoeffXorZeroValued _ _ (ftpCondCoeffZero (csrNatListEq m p) c hc) (ih hrest)
theorem ftpEvalBelowZero (m : List Nat) (W : FtpNF) (hbelow : ftpBelowHead m W = true)
    (hsorted : ftpNFSorted W = true) : ftpEvalCross m W = false := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨q, e⟩ := head
      have hmq : csrCompare m q = CsrMonoOrd.lt := ftpBelowHeadConsLt m q e rest hbelow
      have hmqEq : csrNatListEq m q = false := ftpMonoEqFalseOfLt m q hmq
      have hqbelow : ftpBelowHead q rest = true := csrAndTrueLeft _ _ hsorted
      have hrest : ftpNFSorted rest = true := csrAndTrueRight _ _ hsorted
      have hmrest : ftpBelowHead m rest = true := by
        cases rest with
        | nil => rfl
        | cons head2 rest2 =>
            obtain ⟨r, f⟩ := head2
            have hqr : csrCompare q r = CsrMonoOrd.lt := ftpBelowHeadConsLt q r f rest2 hqbelow
            exact ftpBelowHeadConsTrue m r f rest2 (csrCompareTransLt m q r hmq hqr)
      rw [ftpEvalCrossCons, hmqEq, ftpCondCoeffFalse, ftpCoeffXorFalseLeft, ih hmrest hrest]
/-- The extensionality that inverts `ftpAllZero_evalZero` on sorted NFs. -/
theorem ftpSortedEvalZero_allZero (W : FtpNF) (hsorted : ftpNFSorted W = true)
    (hzero : ∀ m, ftpCoeffIsZero (ftpEvalCross m W) = true) : ftpNFAllZero W = true := by
  induction W with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨p, c⟩ := head
      have hbelow : ftpBelowHead p rest = true := csrAndTrueLeft _ _ hsorted
      have hrest : ftpNFSorted rest = true := csrAndTrueRight _ _ hsorted
      have hevalPrest : ftpEvalCross p rest = false := ftpEvalBelowZero p rest hbelow hrest
      have hc : ftpCoeffIsZero c = true := by
        have h := hzero p
        rw [ftpEvalCrossCons, csrNatListEqRefl p, ftpCondCoeffTrue, hevalPrest, ftpCoeffXorFalseRight] at h
        exact h
      have hrestZero : ∀ mm, ftpCoeffIsZero (ftpEvalCross mm rest) = true := by
        intro mm
        cases hmp : csrNatListEq mm p with
        | true =>
            have hmeqp : mm = p := csrNatListEq_eq mm p hmp
            rw [hmeqp, hevalPrest]; rfl
        | false =>
            have h := hzero mm
            rw [ftpEvalCrossCons, hmp, ftpCondCoeffFalse, ftpCoeffXorFalseLeft] at h
            exact h
      rw [ftpNFAllZeroCons]
      exact csrAndIntro _ _ hc (ih hrest hrestZero)
/-- ★ The all-absent cancellation: if `mergeXor X Z` and `Z` are both all-absent (with `X` sorted), so is `X`. -/
theorem ftpMergeXorAllZeroCancel (X Z : FtpNF) (hX : ftpNFSorted X = true)
    (hXZ : ftpNFAllZero (ftpMergeXor X Z) = true) (hZ : ftpNFAllZero Z = true) :
    ftpNFAllZero X = true := by
  apply ftpSortedEvalZero_allZero X hX
  intro m
  have hmerge : ftpCoeffIsZero (ftpEvalCross m (ftpMergeXor X Z)) = true := ftpAllZero_evalZero m _ hXZ
  rw [ftpEvalCross_mergeXor m X Z] at hmerge
  exact ftpCoeffXorCancelZero (ftpEvalCross m X) (ftpEvalCross m Z) hmerge (ftpAllZero_evalZero m Z hZ)
/-- ★ The F2 self-inverse: a polynomial XOR itself is all-absent (`x + x = 0`), read off `ftpEvalCross`. -/
theorem ftpMergeXorSelfAllZero (A : FtpNF) (hA : ftpNFSorted A = true) :
    ftpNFAllZero (ftpMergeXor A A) = true := by
  apply ftpSortedEvalZero_allZero _ (ftpMergeXorPreservesSorted A A hA)
  intro m
  rw [ftpEvalCross_mergeXor m A A]
  exact ftpCoeffXorSelfZero (ftpEvalCross m A)

/-! ## Multiplying by an all-absent polynomial (for the multiplicative congruence) -/

theorem ftpTermMulCoeffZeroAllZero (m : List Nat) (c : Bool) (hc : ftpCoeffIsZero c = true) (B : FtpNF) :
    ftpNFAllZero (ftpTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      show ftpNFAllZero (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c rest)) = true
      exact ftpInsertTermAllZero _ _ _ (ftpCoeffAndZeroValuedLeft c d hc) ih
theorem ftpTermMulRightAllZero (m : List Nat) (c : Bool) (B : FtpNF) (hB : ftpNFAllZero B = true) :
    ftpNFAllZero (ftpTermMul m c B) = true := by
  induction B with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨n, d⟩ := head
      have hd : ftpCoeffIsZero d = true := csrAndTrueLeft _ _ hB
      have hrest : ftpNFAllZero rest = true := csrAndTrueRight _ _ hB
      show ftpNFAllZero (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c rest)) = true
      exact ftpInsertTermAllZero _ _ _ (ftpCoeffAndZeroValuedRight c d hd) (ih hrest)
theorem ftpMulConvolveLeftAllZero (A B : FtpNF) (hA : ftpNFAllZero A = true) :
    ftpNFAllZero (ftpMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      have hc : ftpCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hA' : ftpNFAllZero A' = true := csrAndTrueRight _ _ hA
      show ftpNFAllZero (ftpMergeXor (ftpTermMul m c B) (ftpMulConvolve A' B)) = true
      exact ftpMergeXorAllZero _ _ (ftpTermMulCoeffZeroAllZero m c hc B) (ih hA')
theorem ftpMulConvolveRightAllZero (A B : FtpNF) (hB : ftpNFAllZero B = true) :
    ftpNFAllZero (ftpMulConvolve A B) = true := by
  induction A with
  | nil => rfl
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show ftpNFAllZero (ftpMergeXor (ftpTermMul m c B) (ftpMulConvolve A' B)) = true
      exact ftpMergeXorAllZero _ _ (ftpTermMulRightAllZero m c B hB) ih

/-! ## The decision equivalence `ftpNFEq` and its equivalence + congruence structure -/

/-- The F2 polynomial equality: two normal forms agree exactly when their XOR-difference is all-absent.
Because F2 negation is the identity (`−B = B`), the difference is simply `A + B`. -/
def ftpNFEq (A B : FtpNF) : Bool := ftpNFAllZero (ftpMergeXor A B)
/-- ★ `ftpNFEq` is reflexive on a sorted NF — this IS the F2 self-inverse. -/
theorem ftpNFEqRefl (A : FtpNF) (hA : ftpNFSorted A = true) : ftpNFEq A A = true :=
  ftpMergeXorSelfAllZero A hA
/-- Literal-equal (sorted) normal forms are `ftpNFEq`. -/
theorem ftpNFEqOfEq (A B : FtpNF) (hB : ftpNFSorted B = true) (h : A = B) : ftpNFEq A B = true := by
  rw [h]; exact ftpNFEqRefl B hB
/-- `ftpNFEq` is symmetric on sorted NFs (via merge commutativity). -/
theorem ftpNFEqSymm (A B : FtpNF) (hA : ftpNFSorted A = true) (hB : ftpNFSorted B = true)
    (h : ftpNFEq A B = true) : ftpNFEq B A = true := by
  show ftpNFAllZero (ftpMergeXor B A) = true
  rw [ftpMergeXorComm B A hB hA]; exact h
/-- ★ `ftpNFEq` is transitive on sorted NFs — routed through the all-absent cancellation. -/
theorem ftpNFEqTrans (A B C : FtpNF) (_hA : ftpNFSorted A = true) (hB : ftpNFSorted B = true)
    (hC : ftpNFSorted C = true) (hAB : ftpNFEq A B = true) (hBC : ftpNFEq B C = true) :
    ftpNFEq A C = true := by
  have hrearr : ftpMergeXor (ftpMergeXor A B) (ftpMergeXor B C)
              = ftpMergeXor (ftpMergeXor A C) (ftpMergeXor B B) := by
    rw [ftpMergeXor4Swap A B B C hB hB, ftpMergeXor4Swap A C B B hC hB,
        ftpMergeXorComm B C hB hC]
  have hall : ftpNFAllZero (ftpMergeXor (ftpMergeXor A C) (ftpMergeXor B B)) = true := by
    rw [← hrearr]; exact ftpMergeXorAllZero _ _ hAB hBC
  exact ftpMergeXorAllZeroCancel (ftpMergeXor A C) (ftpMergeXor B B)
    (ftpMergeXorPreservesSorted A C hC) hall (ftpMergeXorSelfAllZero B hB)
/-- ★ `ftpNFEq` respects the additive merge. -/
theorem ftpNFEqMergeCongr (A A' B B' : FtpNF) (hA' : ftpNFSorted A' = true) (hB : ftpNFSorted B = true)
    (hAA' : ftpNFEq A A' = true) (hBB' : ftpNFEq B B' = true) :
    ftpNFEq (ftpMergeXor A B) (ftpMergeXor A' B') = true := by
  show ftpNFAllZero (ftpMergeXor (ftpMergeXor A B) (ftpMergeXor A' B')) = true
  rw [ftpMergeXor4Swap A B A' B' hB hA']
  exact ftpMergeXorAllZero _ _ hAA' hBB'
/-- ★ `ftpNFEq` respects the multiplicative convolution. -/
theorem ftpNFEqMulCongr (A A' B B' : FtpNF) (hAA' : ftpNFEq A A' = true) (hBB' : ftpNFEq B B' = true) :
    ftpNFEq (ftpMulConvolve A B) (ftpMulConvolve A' B') = true := by
  have step1 : ftpNFEq (ftpMulConvolve A B) (ftpMulConvolve A' B) = true := by
    show ftpNFAllZero (ftpMergeXor (ftpMulConvolve A B) (ftpMulConvolve A' B)) = true
    rw [← ftpMulConvolve_rightDistrib A A' B]
    exact ftpMulConvolveLeftAllZero (ftpMergeXor A A') B hAA'
  have step2 : ftpNFEq (ftpMulConvolve A' B) (ftpMulConvolve A' B') = true := by
    show ftpNFAllZero (ftpMergeXor (ftpMulConvolve A' B) (ftpMulConvolve A' B')) = true
    rw [← ftpMulConvolve_leftDistrib A' B B']
    exact ftpMulConvolveRightAllZero A' (ftpMergeXor B B') hBB'
  exact ftpNFEqTrans (ftpMulConvolve A B) (ftpMulConvolve A' B) (ftpMulConvolve A' B')
    (ftpMulConvolveSorted A B) (ftpMulConvolveSorted A' B) (ftpMulConvolveSorted A' B') step1 step2
/-- An all-absent (sorted) NF is `ftpNFEq` to the empty NF. -/
theorem ftpNFEqNil (X : FtpNF) (hX : ftpNFSorted X = true) (hall : ftpNFAllZero X = true) :
    ftpNFEq X [] = true := by
  show ftpNFAllZero (ftpMergeXor X []) = true
  rw [ftpMergeXorNilRight X hX]; exact hall

/-! ## The free field-two-polynomial tree carrier and its normal form -/

/-- ★ The free F2[X] tree carrier: colour-tagged generators, the additive unit `0`, the multiplicative
unit `1`, F2 addition `xorOp`, and ring multiplication `andOp`.  There is no negation constructor — in F2 the
additive inverse of `x` is `x` itself. -/
inductive FtpTree where
  /-- a colour-tagged generator (variable). -/
  | gen (colour : Nat)
  /-- the additive unit `0` (F2 zero, `⊥`). -/
  | zeroOp
  /-- the multiplicative unit `1` (F2 one, the empty monomial `⊤`). -/
  | oneOp
  /-- F2 addition (XOR). -/
  | xorOp : FtpTree → FtpTree → FtpTree
  /-- ring multiplication (AND). -/
  | andOp : FtpTree → FtpTree → FtpTree

/-- ★ normalize a tree to its F2[X] normal form (sorted MULTISET monomials with repeats, F2 coefficients). -/
def ftpNormalize : FtpTree → FtpNF
  | .gen colour => [([colour], true)]
  | .zeroOp => []
  | .oneOp => [([], true)]
  | .xorOp l r => ftpMergeXor (ftpNormalize l) (ftpNormalize r)
  | .andOp l r => ftpMulConvolve (ftpNormalize l) (ftpNormalize r)

theorem ftpNormalize_zero_smoke : ftpNormalize FtpTree.zeroOp = [] := rfl
theorem ftpNormalize_one_smoke : ftpNormalize FtpTree.oneOp = [([], true)] := rfl
theorem ftpNormalize_gen_smoke : ftpNormalize (FtpTree.gen 2) = [([2], true)] := rfl
theorem ftpNormalizeSorted (t : FtpTree) : ftpNFSorted (ftpNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | xorOp l r _ ihr => exact ftpMergeXorPreservesSorted (ftpNormalize l) (ftpNormalize r) ihr
  | andOp l r _ _ => exact ftpMulConvolveSorted (ftpNormalize l) (ftpNormalize r)
theorem ftpNormalizeMonoSorted (t : FtpTree) : ftpNFMonoSorted (ftpNormalize t) = true := by
  induction t with
  | gen c => rfl
  | zeroOp => rfl
  | oneOp => rfl
  | xorOp l r ihl ihr => exact ftpMergeXorMonoSorted (ftpNormalize l) (ftpNormalize r) ihl ihr
  | andOp l r ihl ihr => exact ftpMulConvolveMonoSorted (ftpNormalize l) (ftpNormalize r) ihl ihr
/-! ## The field-two-polynomial tree convertibility -/

/-- ★ The free convertibility of the `{+, ·, 0, 1}` signature over colour-tagged generators, closed under the
commutative-F2-algebra laws: the additive ABELIAN GROUP OF EXPONENT 2 (associativity, commutativity, right unit,
and the F2 self-inverse `xorSelf : a + a ≈ 0`), the commutative multiplicative MONOID (associativity,
commutativity, right unit) — and crucially NO idempotence law, so `x · x` is the genuine degree-two monomial
`x²` and `x² ≉ x` — distributivity and right-annihilation, the full congruences `xorCongr` / `andCongr`, and
`refl` / `symm` / `trans`.  This presents the FREE commutative F2-algebra `F2[X_c : c ∈ ℕ]`, the polynomial
ring over the two-element field. -/
inductive FieldTwoPolyTreeConv : FtpTree → FtpTree → Prop where
  /-- **Additive associativity** `(a + b) + c ≈ a + (b + c)`. -/
  | xorAssoc (a b c : FtpTree) :
      FieldTwoPolyTreeConv (FtpTree.xorOp (FtpTree.xorOp a b) c) (FtpTree.xorOp a (FtpTree.xorOp b c))
  /-- **Additive commutativity** `a + b ≈ b + a`. -/
  | xorComm (a b : FtpTree) : FieldTwoPolyTreeConv (FtpTree.xorOp a b) (FtpTree.xorOp b a)
  /-- **Additive right unit** `a + 0 ≈ a`. -/
  | xorZero (a : FtpTree) : FieldTwoPolyTreeConv (FtpTree.xorOp a FtpTree.zeroOp) a
  /-- ★ **The F2 self-inverse** `a + a ≈ 0` — every element is its own additive inverse. -/
  | xorSelf (a : FtpTree) : FieldTwoPolyTreeConv (FtpTree.xorOp a a) FtpTree.zeroOp
  /-- **Multiplicative associativity** `(a · b) · c ≈ a · (b · c)`. -/
  | andAssoc (a b c : FtpTree) :
      FieldTwoPolyTreeConv (FtpTree.andOp (FtpTree.andOp a b) c) (FtpTree.andOp a (FtpTree.andOp b c))
  /-- **Multiplicative commutativity** `a · b ≈ b · a`. -/
  | andComm (a b : FtpTree) : FieldTwoPolyTreeConv (FtpTree.andOp a b) (FtpTree.andOp b a)
  /-- **Multiplicative right unit** `a · 1 ≈ a`. -/
  | andOne (a : FtpTree) : FieldTwoPolyTreeConv (FtpTree.andOp a FtpTree.oneOp) a
  /-- **Left distributivity** `a · (b + c) ≈ a·b + a·c`. -/
  | distribLeft (a b c : FtpTree) :
      FieldTwoPolyTreeConv (FtpTree.andOp a (FtpTree.xorOp b c))
        (FtpTree.xorOp (FtpTree.andOp a b) (FtpTree.andOp a c))
  /-- **Right annihilation** `a · 0 ≈ 0`. -/
  | annihilRight (a : FtpTree) : FieldTwoPolyTreeConv (FtpTree.andOp a FtpTree.zeroOp) FtpTree.zeroOp
  /-- **Additive congruence** — into both summands. -/
  | xorCongr {leftOld leftNew rightOld rightNew : FtpTree} :
      FieldTwoPolyTreeConv leftOld leftNew → FieldTwoPolyTreeConv rightOld rightNew →
      FieldTwoPolyTreeConv (FtpTree.xorOp leftOld rightOld) (FtpTree.xorOp leftNew rightNew)
  /-- **Multiplicative congruence** — into both factors. -/
  | andCongr {leftOld leftNew rightOld rightNew : FtpTree} :
      FieldTwoPolyTreeConv leftOld leftNew → FieldTwoPolyTreeConv rightOld rightNew →
      FieldTwoPolyTreeConv (FtpTree.andOp leftOld rightOld) (FtpTree.andOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (t : FtpTree) : FieldTwoPolyTreeConv t t
  /-- Symmetry. -/
  | symm {s t : FtpTree} : FieldTwoPolyTreeConv s t → FieldTwoPolyTreeConv t s
  /-- Transitivity. -/
  | trans {s t u : FtpTree} : FieldTwoPolyTreeConv s t → FieldTwoPolyTreeConv t u → FieldTwoPolyTreeConv s u

/-! ## Soundness: convertible ⟹ `ftpNFEq` normal forms -/

/-- ★ Soundness — convertible trees have `ftpNFEq` normal forms.  Every core ring law is a LITERAL normal-form
equality (`ftpNFEqOfEq` off the merge / convolve algebra); the F2 self-inverse falls to `ftpMergeXorSelfAllZero`
(`ftpNFEqNil`); generator idempotence to `ftpNormalizeAndIdemGen`; the congruences / equivalence to the `ftpNFEq`
structure. -/
theorem ftpNormalize_respects {s t : FtpTree} (conv : FieldTwoPolyTreeConv s t) :
    ftpNFEq (ftpNormalize s) (ftpNormalize t) = true := by
  induction conv with
  | xorAssoc a b c =>
      exact ftpNFEqOfEq _ _
        (ftpMergeXorPreservesSorted _ _ (ftpMergeXorPreservesSorted _ _ (ftpNormalizeSorted c)))
        (ftpMergeXorAssoc (ftpNormalize a) (ftpNormalize b) (ftpNormalize c))
  | xorComm a b =>
      exact ftpNFEqOfEq _ _
        (ftpMergeXorPreservesSorted _ _ (ftpNormalizeSorted a))
        (ftpMergeXorComm (ftpNormalize a) (ftpNormalize b) (ftpNormalizeSorted a) (ftpNormalizeSorted b))
  | xorZero a =>
      exact ftpNFEqOfEq _ _ (ftpNormalizeSorted a)
        (ftpMergeXorNilRight (ftpNormalize a) (ftpNormalizeSorted a))
  | xorSelf a =>
      exact ftpNFEqNil _
        (ftpMergeXorPreservesSorted _ _ (ftpNormalizeSorted a))
        (ftpMergeXorSelfAllZero (ftpNormalize a) (ftpNormalizeSorted a))
  | andAssoc a b c =>
      exact ftpNFEqOfEq _ _ (ftpMulConvolveSorted _ _)
        (ftpMulConvolveAssoc (ftpNormalize a) (ftpNormalize b) (ftpNormalize c))
  | andComm a b =>
      exact ftpNFEqOfEq _ _ (ftpMulConvolveSorted _ _)
        (ftpMulConvolveComm (ftpNormalize a) (ftpNormalize b)
          (ftpNormalizeSorted a) (ftpNormalizeMonoSorted a) (ftpNormalizeMonoSorted b))
  | andOne a =>
      exact ftpNFEqOfEq _ _ (ftpNormalizeSorted a)
        (ftpMulConvolveUnit (ftpNormalize a) (ftpNormalizeSorted a))
  | distribLeft a b c =>
      exact ftpNFEqOfEq _ _
        (ftpMergeXorPreservesSorted _ _ (ftpMulConvolveSorted _ _))
        (ftpMulConvolve_leftDistrib (ftpNormalize a) (ftpNormalize b) (ftpNormalize c))
  | annihilRight a =>
      exact ftpNFEqOfEq _ _ rfl (ftpMulConvolveAnnihil (ftpNormalize a))
  | @xorCongr lo ln ro rn _ _ ihl ihr =>
      exact ftpNFEqMergeCongr (ftpNormalize lo) (ftpNormalize ln) (ftpNormalize ro) (ftpNormalize rn)
        (ftpNormalizeSorted ln) (ftpNormalizeSorted ro) ihl ihr
  | @andCongr lo ln ro rn _ _ ihl ihr =>
      exact ftpNFEqMulCongr (ftpNormalize lo) (ftpNormalize ln) (ftpNormalize ro) (ftpNormalize rn) ihl ihr
  | refl t => exact ftpNFEqRefl (ftpNormalize t) (ftpNormalizeSorted t)
  | @symm s t _ ih =>
      exact ftpNFEqSymm (ftpNormalize s) (ftpNormalize t)
        (ftpNormalizeSorted s) (ftpNormalizeSorted t) ih
  | @trans s t u _ _ ih1 ih2 =>
      exact ftpNFEqTrans (ftpNormalize s) (ftpNormalize t) (ftpNormalize u)
        (ftpNormalizeSorted s) (ftpNormalizeSorted t) (ftpNormalizeSorted u) ih1 ih2

/-! ## Derived convertibility lemmas (for the rebuild reification) -/

theorem ftpConvXorZeroLeft (a : FtpTree) : FieldTwoPolyTreeConv (FtpTree.xorOp FtpTree.zeroOp a) a :=
  (FieldTwoPolyTreeConv.xorComm FtpTree.zeroOp a).trans (FieldTwoPolyTreeConv.xorZero a)
theorem ftpConvAndOneLeft (a : FtpTree) : FieldTwoPolyTreeConv (FtpTree.andOp FtpTree.oneOp a) a :=
  (FieldTwoPolyTreeConv.andComm FtpTree.oneOp a).trans (FieldTwoPolyTreeConv.andOne a)
theorem ftpConvAnnihilLeft (a : FtpTree) :
    FieldTwoPolyTreeConv (FtpTree.andOp FtpTree.zeroOp a) FtpTree.zeroOp :=
  (FieldTwoPolyTreeConv.andComm FtpTree.zeroOp a).trans (FieldTwoPolyTreeConv.annihilRight a)
theorem ftpConvDistribRight (a b c : FtpTree) :
    FieldTwoPolyTreeConv (FtpTree.andOp (FtpTree.xorOp a b) c)
      (FtpTree.xorOp (FtpTree.andOp a c) (FtpTree.andOp b c)) :=
  (FieldTwoPolyTreeConv.andComm (FtpTree.xorOp a b) c).trans
    ((FieldTwoPolyTreeConv.distribLeft c a b).trans
      (FieldTwoPolyTreeConv.xorCongr (FieldTwoPolyTreeConv.andComm c a) (FieldTwoPolyTreeConv.andComm c b)))
theorem ftpConvXorSwap13 (x y z : FtpTree) :
    FieldTwoPolyTreeConv (FtpTree.xorOp x (FtpTree.xorOp y z)) (FtpTree.xorOp y (FtpTree.xorOp x z)) :=
  (FieldTwoPolyTreeConv.symm (FieldTwoPolyTreeConv.xorAssoc x y z)).trans
    ((FieldTwoPolyTreeConv.xorCongr (FieldTwoPolyTreeConv.xorComm x y) (FieldTwoPolyTreeConv.refl z)).trans
      (FieldTwoPolyTreeConv.xorAssoc y x z))
theorem ftpConvAndSwap13 (x y z : FtpTree) :
    FieldTwoPolyTreeConv (FtpTree.andOp x (FtpTree.andOp y z)) (FtpTree.andOp y (FtpTree.andOp x z)) :=
  (FieldTwoPolyTreeConv.symm (FieldTwoPolyTreeConv.andAssoc x y z)).trans
    ((FieldTwoPolyTreeConv.andCongr (FieldTwoPolyTreeConv.andComm x y) (FieldTwoPolyTreeConv.refl z)).trans
      (FieldTwoPolyTreeConv.andAssoc y x z))

/-! ## The monomial tree and its multiplicative reification -/

def ftpMonoToTree : List Nat → FtpTree
  | [] => FtpTree.oneOp
  | c :: rest => FtpTree.andOp (FtpTree.gen c) (ftpMonoToTree rest)
/-- ★ Reifying an insert into the sorted MULTISET monomial: `monoToTree (insertSorted v xs) ≈ gen v · monoToTree xs`.
Unlike the Boolean-ring sibling there is NO dedup branch — repeats survive, so no idempotence is ever consumed. -/
theorem ftpMonoToTreeInsertSorted (v : Nat) (xs : List Nat) :
    FieldTwoPolyTreeConv (ftpMonoToTree (insertSorted v xs))
      (FtpTree.andOp (FtpTree.gen v) (ftpMonoToTree xs)) := by
  induction xs with
  | nil => exact FieldTwoPolyTreeConv.refl _
  | cons head rest ih =>
      cases hvh : natBle v head with
      | true =>
          rw [insertSortedConsTrue v head rest hvh]
          exact FieldTwoPolyTreeConv.refl _
      | false =>
          rw [insertSortedConsFalse v head rest hvh]
          exact (FieldTwoPolyTreeConv.andCongr (FieldTwoPolyTreeConv.refl (FtpTree.gen head)) ih).trans
            (ftpConvAndSwap13 (FtpTree.gen head) (FtpTree.gen v) (ftpMonoToTree rest))
theorem ftpMonoToTreeInsertMany : (n m : List Nat) →
    FieldTwoPolyTreeConv (ftpMonoToTree (insertMany n m))
      (FtpTree.andOp (ftpMonoToTree n) (ftpMonoToTree m))
  | [], m => (ftpConvAndOneLeft (ftpMonoToTree m)).symm
  | a :: n', m => by
      show FieldTwoPolyTreeConv (ftpMonoToTree (insertSorted a (insertMany n' m)))
        (FtpTree.andOp (FtpTree.andOp (FtpTree.gen a) (ftpMonoToTree n')) (ftpMonoToTree m))
      exact (ftpMonoToTreeInsertSorted a (insertMany n' m)).trans
        ((FieldTwoPolyTreeConv.andCongr (FieldTwoPolyTreeConv.refl (FtpTree.gen a))
            (ftpMonoToTreeInsertMany n' m)).trans
          (FieldTwoPolyTreeConv.symm
            (FieldTwoPolyTreeConv.andAssoc (FtpTree.gen a) (ftpMonoToTree n') (ftpMonoToTree m))))
theorem ftpMonoToTreeMonoMul (m n : List Nat) :
    FieldTwoPolyTreeConv (ftpMonoToTree (ftpMonoMul m n))
      (FtpTree.andOp (ftpMonoToTree m) (ftpMonoToTree n)) := by
  show FieldTwoPolyTreeConv (ftpMonoToTree (insertMany n m))
    (FtpTree.andOp (ftpMonoToTree m) (ftpMonoToTree n))
  exact (ftpMonoToTreeInsertMany n m).trans
    (FieldTwoPolyTreeConv.andComm (ftpMonoToTree n) (ftpMonoToTree m))

/-! ## The term tree (an F2 coefficient applied to a monomial) and its reification -/

/-- The tree of a single term `(mono, c)`: the monomial tree when present, `0` when absent. -/
def ftpTermToTree (mono : List Nat) : Bool → FtpTree
  | false => FtpTree.zeroOp
  | true => ftpMonoToTree mono
/-- The term tree distributes over coefficient XOR (four finite `Bool` cases; the `true, true` case is the F2
self-inverse `x + x ≈ 0`). -/
theorem ftpTermToTreeXor (m : List Nat) (e c : Bool) :
    FieldTwoPolyTreeConv (ftpTermToTree m (ftpCoeffXor e c))
      (FtpTree.xorOp (ftpTermToTree m e) (ftpTermToTree m c)) := by
  cases e with
  | false => cases c with
    | false => exact (FieldTwoPolyTreeConv.xorZero FtpTree.zeroOp).symm
    | true => exact (ftpConvXorZeroLeft (ftpMonoToTree m)).symm
  | true => cases c with
    | false => exact (FieldTwoPolyTreeConv.xorZero (ftpMonoToTree m)).symm
    | true => exact (FieldTwoPolyTreeConv.xorSelf (ftpMonoToTree m)).symm
/-- The term-product reification: `termToTree (m ⊎ n) (c1 ∧ c2) ≈ (termToTree m c1) · (termToTree n c2)`
(four finite `Bool` cases; the present-present case is `ftpMonoToTreeMonoMul`). -/
theorem ftpTermToTreeMul (m : List Nat) (c1 : Bool) (n : List Nat) (c2 : Bool) :
    FieldTwoPolyTreeConv (ftpTermToTree (ftpMonoMul m n) (ftpCoeffAnd c1 c2))
      (FtpTree.andOp (ftpTermToTree m c1) (ftpTermToTree n c2)) := by
  cases c1 with
  | true => cases c2 with
    | true => exact ftpMonoToTreeMonoMul m n
    | false => exact (FieldTwoPolyTreeConv.annihilRight (ftpMonoToTree m)).symm
  | false => cases c2 with
    | true => exact (ftpConvAnnihilLeft (ftpMonoToTree n)).symm
    | false => exact (FieldTwoPolyTreeConv.annihilRight FtpTree.zeroOp).symm
/-- An absent term tree is convertible to `0`. -/
theorem ftpTermToTreeZero (m : List Nat) (c : Bool) (hc : ftpCoeffIsZero c = true) :
    FieldTwoPolyTreeConv (ftpTermToTree m c) FtpTree.zeroOp := by
  cases c with
  | false => exact FieldTwoPolyTreeConv.refl FtpTree.zeroOp
  | true => exact Bool.noConfusion hc

/-! ## The normal-form rebuild `ftpCombOfNF` and its convertibility algebra -/

/-- Rebuild a canonical tree from a normal form (XOR-fold the term trees). -/
def ftpCombOfNF : FtpNF → FtpTree
  | [] => FtpTree.zeroOp
  | (m, c) :: rest => FtpTree.xorOp (ftpTermToTree m c) (ftpCombOfNF rest)
theorem ftpCombOfNFCons (m : List Nat) (c : Bool) (rest : FtpNF) :
    ftpCombOfNF ((m, c) :: rest) = FtpTree.xorOp (ftpTermToTree m c) (ftpCombOfNF rest) := rfl
theorem ftpCombInsertTerm (m : List Nat) (c : Bool) (A : FtpNF) :
    FieldTwoPolyTreeConv (ftpCombOfNF (ftpInsertTerm (m, c) A))
      (FtpTree.xorOp (ftpTermToTree m c) (ftpCombOfNF A)) := by
  induction A with
  | nil => exact FieldTwoPolyTreeConv.refl _
  | cons head rest ih =>
      obtain ⟨p, e⟩ := head
      cases hmp : csrCompare m p with
      | eq =>
          have hmeqp : m = p := csrCompareEq_of m p hmp
          rw [ftpInsertTermEqE m c p e rest hmp, ftpCombOfNFCons p (ftpCoeffXor e c) rest,
              ftpCombOfNFCons p e rest, hmeqp]
          exact (FieldTwoPolyTreeConv.xorCongr (ftpTermToTreeXor p e c)
              (FieldTwoPolyTreeConv.refl (ftpCombOfNF rest))).trans
            ((FieldTwoPolyTreeConv.xorAssoc (ftpTermToTree p e) (ftpTermToTree p c) (ftpCombOfNF rest)).trans
              (ftpConvXorSwap13 (ftpTermToTree p e) (ftpTermToTree p c) (ftpCombOfNF rest)))
      | lt =>
          rw [ftpInsertTermLtE m c p e rest hmp, ftpCombOfNFCons m c ((p, e) :: rest)]
          exact FieldTwoPolyTreeConv.refl _
      | gt =>
          rw [ftpInsertTermGtE m c p e rest hmp, ftpCombOfNFCons p e (ftpInsertTerm (m, c) rest),
              ftpCombOfNFCons p e rest]
          exact (FieldTwoPolyTreeConv.xorCongr (FieldTwoPolyTreeConv.refl (ftpTermToTree p e)) ih).trans
            (ftpConvXorSwap13 (ftpTermToTree p e) (ftpTermToTree m c) (ftpCombOfNF rest))
theorem ftpCombMergeXor (A B : FtpNF) :
    FieldTwoPolyTreeConv (ftpCombOfNF (ftpMergeXor A B))
      (FtpTree.xorOp (ftpCombOfNF A) (ftpCombOfNF B)) := by
  induction A with
  | nil => exact (ftpConvXorZeroLeft (ftpCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show FieldTwoPolyTreeConv (ftpCombOfNF (ftpInsertTerm (m, c) (ftpMergeXor A' B)))
        (FtpTree.xorOp (FtpTree.xorOp (ftpTermToTree m c) (ftpCombOfNF A')) (ftpCombOfNF B))
      exact ((ftpCombInsertTerm m c (ftpMergeXor A' B)).trans
          (FieldTwoPolyTreeConv.xorCongr (FieldTwoPolyTreeConv.refl (ftpTermToTree m c)) ih)).trans
        (FieldTwoPolyTreeConv.symm
          (FieldTwoPolyTreeConv.xorAssoc (ftpTermToTree m c) (ftpCombOfNF A') (ftpCombOfNF B)))
theorem ftpCombTermMul (m : List Nat) (c : Bool) (B : FtpNF) :
    FieldTwoPolyTreeConv (ftpCombOfNF (ftpTermMul m c B))
      (FtpTree.andOp (ftpTermToTree m c) (ftpCombOfNF B)) := by
  induction B with
  | nil => exact (FieldTwoPolyTreeConv.annihilRight (ftpTermToTree m c)).symm
  | cons head B' ih =>
      obtain ⟨n, d⟩ := head
      show FieldTwoPolyTreeConv (ftpCombOfNF (ftpInsertTerm (ftpMonoMul m n, ftpCoeffAnd c d) (ftpTermMul m c B')))
        (FtpTree.andOp (ftpTermToTree m c) (FtpTree.xorOp (ftpTermToTree n d) (ftpCombOfNF B')))
      exact ((ftpCombInsertTerm (ftpMonoMul m n) (ftpCoeffAnd c d) (ftpTermMul m c B')).trans
          (FieldTwoPolyTreeConv.xorCongr (ftpTermToTreeMul m c n d) ih)).trans
        (FieldTwoPolyTreeConv.symm
          (FieldTwoPolyTreeConv.distribLeft (ftpTermToTree m c) (ftpTermToTree n d) (ftpCombOfNF B')))
theorem ftpCombMulConvolve (A B : FtpNF) :
    FieldTwoPolyTreeConv (ftpCombOfNF (ftpMulConvolve A B))
      (FtpTree.andOp (ftpCombOfNF A) (ftpCombOfNF B)) := by
  induction A with
  | nil => exact (ftpConvAnnihilLeft (ftpCombOfNF B)).symm
  | cons head A' ih =>
      obtain ⟨m, c⟩ := head
      show FieldTwoPolyTreeConv (ftpCombOfNF (ftpMergeXor (ftpTermMul m c B) (ftpMulConvolve A' B)))
        (FtpTree.andOp (FtpTree.xorOp (ftpTermToTree m c) (ftpCombOfNF A')) (ftpCombOfNF B))
      exact ((ftpCombMergeXor (ftpTermMul m c B) (ftpMulConvolve A' B)).trans
          (FieldTwoPolyTreeConv.xorCongr (ftpCombTermMul m c B) ih)).trans
        (FieldTwoPolyTreeConv.symm (ftpConvDistribRight (ftpTermToTree m c) (ftpCombOfNF A') (ftpCombOfNF B)))
/-- An all-absent rebuild reduces to `0`. -/
theorem ftpCombAllZero (A : FtpNF) (hA : ftpNFAllZero A = true) :
    FieldTwoPolyTreeConv (ftpCombOfNF A) FtpTree.zeroOp := by
  induction A with
  | nil => exact FieldTwoPolyTreeConv.refl FtpTree.zeroOp
  | cons head rest ih =>
      obtain ⟨m, c⟩ := head
      have hc : ftpCoeffIsZero c = true := csrAndTrueLeft _ _ hA
      have hrest : ftpNFAllZero rest = true := csrAndTrueRight _ _ hA
      show FieldTwoPolyTreeConv (FtpTree.xorOp (ftpTermToTree m c) (ftpCombOfNF rest)) FtpTree.zeroOp
      exact (FieldTwoPolyTreeConv.xorCongr (ftpTermToTreeZero m c hc) (ih hrest)).trans
        (FieldTwoPolyTreeConv.xorZero FtpTree.zeroOp)

/-! ## Reification: every tree is convertible to the rebuild of its own normal form -/

/-- ★ Every tree is convertible to the rebuild of its own normal form. -/
theorem ftpTreeReifies (t : FtpTree) : FieldTwoPolyTreeConv t (ftpCombOfNF (ftpNormalize t)) := by
  induction t with
  | gen c =>
      show FieldTwoPolyTreeConv (FtpTree.gen c) (FtpTree.xorOp (ftpTermToTree [c] true) FtpTree.zeroOp)
      have hgen : FieldTwoPolyTreeConv (FtpTree.gen c) (ftpMonoToTree [c]) :=
        (FieldTwoPolyTreeConv.andOne (FtpTree.gen c)).symm
      exact hgen.trans (FieldTwoPolyTreeConv.symm (FieldTwoPolyTreeConv.xorZero (ftpMonoToTree [c])))
  | zeroOp => exact FieldTwoPolyTreeConv.refl FtpTree.zeroOp
  | oneOp =>
      show FieldTwoPolyTreeConv FtpTree.oneOp (FtpTree.xorOp (ftpTermToTree [] true) FtpTree.zeroOp)
      exact (FieldTwoPolyTreeConv.xorZero (ftpMonoToTree [])).symm
  | xorOp l r ihl ihr =>
      show FieldTwoPolyTreeConv (FtpTree.xorOp l r)
        (ftpCombOfNF (ftpMergeXor (ftpNormalize l) (ftpNormalize r)))
      exact (FieldTwoPolyTreeConv.xorCongr ihl ihr).trans
        (FieldTwoPolyTreeConv.symm (ftpCombMergeXor (ftpNormalize l) (ftpNormalize r)))
  | andOp l r ihl ihr =>
      show FieldTwoPolyTreeConv (FtpTree.andOp l r)
        (ftpCombOfNF (ftpMulConvolve (ftpNormalize l) (ftpNormalize r)))
      exact (FieldTwoPolyTreeConv.andCongr ihl ihr).trans
        (FieldTwoPolyTreeConv.symm (ftpCombMulConvolve (ftpNormalize l) (ftpNormalize r)))

/-! ## Completeness: `ftpNFEq` normal forms give convertible trees -/

/-- If `x + y ≈ 0` then `x ≈ y` — in F2 the additive inverse of `y` is `y`, so `x + y ≈ 0` forces `x ≈ y`. -/
theorem ftpConvOfXorZero (x y : FtpTree)
    (h : FieldTwoPolyTreeConv (FtpTree.xorOp x y) FtpTree.zeroOp) : FieldTwoPolyTreeConv x y :=
  (FieldTwoPolyTreeConv.xorZero x).symm.trans
    ((FieldTwoPolyTreeConv.xorCongr (FieldTwoPolyTreeConv.refl x)
        (FieldTwoPolyTreeConv.symm (FieldTwoPolyTreeConv.xorSelf y))).trans
      ((FieldTwoPolyTreeConv.symm (FieldTwoPolyTreeConv.xorAssoc x y y)).trans
        ((FieldTwoPolyTreeConv.xorCongr h (FieldTwoPolyTreeConv.refl y)).trans
          (ftpConvXorZeroLeft y))))
/-- The rebuilds of `ftpNFEq` normal forms are convertible. -/
theorem ftpCombOfNFEqConv (A B : FtpNF) (h : ftpNFEq A B = true) :
    FieldTwoPolyTreeConv (ftpCombOfNF A) (ftpCombOfNF B) := by
  apply ftpConvOfXorZero (ftpCombOfNF A) (ftpCombOfNF B)
  have hall : FieldTwoPolyTreeConv (ftpCombOfNF (ftpMergeXor A B)) FtpTree.zeroOp :=
    ftpCombAllZero (ftpMergeXor A B) h
  exact (FieldTwoPolyTreeConv.symm (ftpCombMergeXor A B)).trans hall
/-- ★ Completeness — `ftpNFEq` normal forms give convertible trees. -/
theorem ftpConv_of_normalizeEq {s t : FtpTree} (h : ftpNFEq (ftpNormalize s) (ftpNormalize t) = true) :
    FieldTwoPolyTreeConv s t :=
  (ftpTreeReifies s).trans
    ((ftpCombOfNFEqConv (ftpNormalize s) (ftpNormalize t) h).trans (FieldTwoPolyTreeConv.symm (ftpTreeReifies t)))

/-! ## The decision -/

/-- ★★ the decision procedure: convertible iff the F2 polynomial XOR-difference is all-absent. -/
def ftpDecideConv (s t : FtpTree) : Bool := ftpNFEq (ftpNormalize s) (ftpNormalize t)
/-- ★★ THE DECISION: convertibility ⟺ equal F2[X] normal form (multiset monomials, F2 coefficients). -/
theorem fieldTwoPolyTreeConv_iff_normalForm (s t : FtpTree) :
    FieldTwoPolyTreeConv s t ↔ ftpDecideConv s t = true := by
  constructor
  · intro conv
    exact ftpNormalize_respects conv
  · intro hdec
    exact ftpConv_of_normalizeEq hdec
/-- ★ decidability, via the biconditional (no `propext`). -/
instance instDecidableFieldTwoPolyTreeConv (s t : FtpTree) : Decidable (FieldTwoPolyTreeConv s t) :=
  if h : ftpDecideConv s t = true then
    isTrue ((fieldTwoPolyTreeConv_iff_normalForm s t).mpr h)
  else
    isFalse (fun conv => h ((fieldTwoPolyTreeConv_iff_normalForm s t).mp conv))
/-- ★★ the walking free commutative F2-algebra on ℕ (the polynomial ring F2[X], NON-idempotent) is DECIDED. -/
def fxWalkingFieldTwoPolynomial_hasNormalFormDecision : Bool := true

-- genuineness smokes
-- THE HEADLINE (F2): x + x is 0 (true) -- every element is its own additive inverse
#eval ftpDecideConv (FtpTree.xorOp (FtpTree.gen 0) (FtpTree.gen 0)) FtpTree.zeroOp
-- THE HEADLINE (NON-idempotent): x * x is NOT x (false) -- x^2 is a genuine degree-2 monomial, x^2 != x
#eval ftpDecideConv (FtpTree.andOp (FtpTree.gen 0) (FtpTree.gen 0)) (FtpTree.gen 0)
-- x * x is x * x (true) -- reflexive on the degree-2 monomial
#eval ftpDecideConv (FtpTree.andOp (FtpTree.gen 0) (FtpTree.gen 0)) (FtpTree.andOp (FtpTree.gen 0) (FtpTree.gen 0))
-- distributivity over XOR: x * (y + z) is x*y + x*z (true)
#eval ftpDecideConv (FtpTree.andOp (FtpTree.gen 0) (FtpTree.xorOp (FtpTree.gen 1) (FtpTree.gen 2)))
  (FtpTree.xorOp (FtpTree.andOp (FtpTree.gen 0) (FtpTree.gen 1)) (FtpTree.andOp (FtpTree.gen 0) (FtpTree.gen 2)))
-- multiplicative commutativity: x * y is y * x (true)
#eval ftpDecideConv (FtpTree.andOp (FtpTree.gen 0) (FtpTree.gen 1)) (FtpTree.andOp (FtpTree.gen 1) (FtpTree.gen 0))
-- F2 binomial square: (x + 1)^2 is x*x + 1 (true) -- the 2x cross term cancels in F2, but x^2 != x
#eval ftpDecideConv
  (FtpTree.andOp (FtpTree.xorOp (FtpTree.gen 0) FtpTree.oneOp) (FtpTree.xorOp (FtpTree.gen 0) FtpTree.oneOp))
  (FtpTree.xorOp (FtpTree.andOp (FtpTree.gen 0) (FtpTree.gen 0)) FtpTree.oneOp)
-- additive commutativity: x + y is y + x (true)
#eval ftpDecideConv (FtpTree.xorOp (FtpTree.gen 0) (FtpTree.gen 1)) (FtpTree.xorOp (FtpTree.gen 1) (FtpTree.gen 0))
-- separation: x is NOT y (false)
#eval ftpDecideConv (FtpTree.gen 0) (FtpTree.gen 1)

end FX1Poly.Polygraph
