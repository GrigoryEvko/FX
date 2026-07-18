import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeSemiring.CommutativeSemiringSeed
import FX1Poly.ComputerAlgebra.Number.NatModularReduction
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # WalkingModularRing/ModularRingSeed — the walking free COMMUTATIVE RING over ℤ/n: the (ℤ/n)[X] decision

The modular successor of the ℕ[X] commutative-semiring rung
(`WalkingCommutativeSemiring/CommutativeSemiringSeed`).  Adjoin the single characteristic law `nTimesOne`
(`mrModulus` copies of `1` added together are `≈ 0`) and the walker becomes the free **commutative ring
over ℤ/n** on the colour set `ℕ` — the polynomial ring `(ℤ/n)[X_c : c ∈ ℕ]`.  We fix `mrModulus := 6`, a
NON-PRIME with the zero divisors `2·3 ≡ 0`, demonstrating `(ℤ/6)[X]` is not an integral domain.

## Architecture — base-normalize then reduce (clean reuse of the ℕ[X] tower)

`(ℤ/n)[X]` is the quotient of `ℕ[X]` by the coefficient congruence `n ≡ 0`.  The normal form is the ℕ[X]
normal form with coefficients reduced into `[0, n)` via the imported structural counting divider
`natRemainder _ mrModulus` (`Nat.mod` LEAKS `propext`), and the terms that vanish mod `n` DROPPED:

* `mrBaseNormalize : MrTree → CsrNF` reuses the imported `csrMergeAdd` / `csrMulConvolve` engine unchanged.
* `mrReduce : CsrNF → CsrNF` reduces every coefficient and drops the zeros.
* `mrNormalize t := mrReduce (mrBaseNormalize t)`.

The modular difficulty is isolated into ONE homomorphism family (`mrReduceInsertReduce` / `mrReduceMergeHom`
/ `mrReduceTermMulRightHom` / `mrReduceConvolveHom`): reduction commutes with merge and convolution up to
re-reduction, built purely from the imported `natRemainder` push lemmas.  Soundness's eleven non-congruence
cases are `congrArg mrReduce` of the imported ℕ[X] identities; the two congruence cases use the homomorphisms;
`nTimesOne` is `natRemainderSelf mrModulus mrModulus = 0`.  Completeness reifies through fresh `mr`-prefixed
copies of the ℕ[X] reification tower plus the modular collapse `mrScaleTreeCharN` (`mrModulus · X ≈ 0`).

Raw Lean 4 + Init; convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` in the audit
twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`;
no `List.append` (`++`), no `Int`, no `Nat.sub`/`Nat.mod`/`Nat.div`, no `Nat.le`/`Nat.ble` lemma, no
`Nat.mul_assoc`/`Nat.add_mul`. -/

namespace FX1Poly.Polygraph

open FX1Poly.ComputerAlgebra

/-! ## The modulus (a non-prime with zero divisors `2·3 ≡ 0`) -/

/-- The fixed coefficient modulus.  `6` is composite with zero divisors, so `(ℤ/6)[X]` is not a domain. -/
def mrModulus : Nat := 6

/-- `0 < mrModulus`, built from the `Nat.le` constructors (no library lemma). -/
theorem mrModulusPos : 0 < mrModulus :=
  Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step Nat.le.refl))))

/-! ## Clean coefficient arithmetic from the imported `natRemainder` kit -/

/-- Reducing an already-reduced coefficient is a no-op. -/
theorem mrRemIdem (value : Nat) :
    natRemainder (natRemainder value mrModulus) mrModulus = natRemainder value mrModulus :=
  natRemainderOfLt (natRemainderIsBounded mrModulusPos)

/-- `natRemainder 0 = 0`. -/
theorem mrRemZero : natRemainder 0 mrModulus = 0 := natRemainderOfLt mrModulusPos

/-- The modular add step, reducing the RIGHT summand. -/
theorem mrRemAddPushRight (leftValue rightValue : Nat) :
    natRemainder (leftValue + natRemainder rightValue mrModulus) mrModulus =
      natRemainder (leftValue + rightValue) mrModulus :=
  (congrArg (fun summed => natRemainder summed mrModulus)
      (Nat.add_comm leftValue (natRemainder rightValue mrModulus))).trans
    ((natRemainderAddPush rightValue leftValue mrModulus mrModulusPos).trans
      (congrArg (fun summed => natRemainder summed mrModulus) (Nat.add_comm rightValue leftValue)))

/-- The modular mul step, reducing the RIGHT factor. -/
theorem mrRemMulPushRight (leftValue rightValue : Nat) :
    natRemainder (leftValue * natRemainder rightValue mrModulus) mrModulus =
      natRemainder (leftValue * rightValue) mrModulus :=
  (congrArg (fun scaled => natRemainder scaled mrModulus)
      (Nat.mul_comm leftValue (natRemainder rightValue mrModulus))).trans
    ((natRemainderMulPush rightValue leftValue mrModulus mrModulusPos).trans
      (congrArg (fun scaled => natRemainder scaled mrModulus) (Nat.mul_comm rightValue leftValue)))

/-- Adding a coefficient that vanishes mod `n` leaves the reduction unchanged. -/
theorem mrRemAddZeroModRight (baseValue extraValue : Nat)
    (hZero : natRemainder extraValue mrModulus = 0) :
    natRemainder (baseValue + extraValue) mrModulus = natRemainder baseValue mrModulus :=
  let reconstruction : extraValue = mrModulus * natQuotient extraValue mrModulus :=
    (natRemainderReconstructs extraValue mrModulus).trans
      ((congrArg (mrModulus * natQuotient extraValue mrModulus + ·) hZero).trans
        (Nat.add_zero (mrModulus * natQuotient extraValue mrModulus)))
  (congrArg (fun packed => natRemainder (baseValue + packed) mrModulus) reconstruction).trans
    (natRemainderAddMultiple baseValue mrModulus (natQuotient extraValue mrModulus) mrModulusPos)

/-- A factor that vanishes mod `n` annihilates the product mod `n`. -/
theorem mrRemMulZeroMod (leftValue rightValue : Nat) (hZero : natRemainder leftValue mrModulus = 0) :
    natRemainder (leftValue * rightValue) mrModulus = 0 :=
  (natRemainderMulPush leftValue rightValue mrModulus mrModulusPos).symm.trans
    ((congrArg (fun z => natRemainder (z * rightValue) mrModulus) hZero).trans
      ((congrArg (fun z => natRemainder z mrModulus) (Nat.zero_mul rightValue)).trans mrRemZero))

/-! ## The coefficient-reduction pass over normal forms -/

/-- Reduce every coefficient into `[0, mrModulus)` and drop the terms that vanish. -/
def mrReduce : CsrNF → CsrNF
  | [] => []
  | (mono, coeff) :: rest =>
      match Nat.beq (natRemainder coeff mrModulus) 0 with
      | true => mrReduce rest
      | false => (mono, natRemainder coeff mrModulus) :: mrReduce rest

theorem mrReduceNil : mrReduce [] = [] := rfl
theorem mrReduceConsZero (mono : List Nat) (coeff : Nat) (rest : CsrNF)
    (hZero : Nat.beq (natRemainder coeff mrModulus) 0 = true) :
    mrReduce ((mono, coeff) :: rest) = mrReduce rest := by
  show (match Nat.beq (natRemainder coeff mrModulus) 0 with
        | true => mrReduce rest
        | false => (mono, natRemainder coeff mrModulus) :: mrReduce rest) = mrReduce rest
  rw [hZero]
theorem mrReduceConsNonzero (mono : List Nat) (coeff : Nat) (rest : CsrNF)
    (hNonzero : Nat.beq (natRemainder coeff mrModulus) 0 = false) :
    mrReduce ((mono, coeff) :: rest) = (mono, natRemainder coeff mrModulus) :: mrReduce rest := by
  show (match Nat.beq (natRemainder coeff mrModulus) 0 with
        | true => mrReduce rest
        | false => (mono, natRemainder coeff mrModulus) :: mrReduce rest)
      = (mono, natRemainder coeff mrModulus) :: mrReduce rest
  rw [hNonzero]

theorem mrBeqZeroEq (value : Nat) (hBeq : Nat.beq (natRemainder value mrModulus) 0 = true) :
    natRemainder value mrModulus = 0 :=
  csrNatEqOfBeq (natRemainder value mrModulus) 0 hBeq
theorem mrBeqZeroOf (value : Nat) (hEq : natRemainder value mrModulus = 0) :
    Nat.beq (natRemainder value mrModulus) 0 = true := by rw [hEq]; rfl

/-- Idempotence: reducing a reduced normal form is a no-op. -/
theorem mrReduceIdem : (normalForm : CsrNF) → mrReduce (mrReduce normalForm) = mrReduce normalForm
  | [] => rfl
  | (mono, coeff) :: rest => by
      cases hb : Nat.beq (natRemainder coeff mrModulus) 0 with
      | true => rw [mrReduceConsZero mono coeff rest hb]; exact mrReduceIdem rest
      | false =>
          rw [mrReduceConsNonzero mono coeff rest hb]
          have hself : Nat.beq (natRemainder (natRemainder coeff mrModulus) mrModulus) 0 = false := by
            rw [mrRemIdem coeff]; exact hb
          rw [mrReduceConsNonzero mono (natRemainder coeff mrModulus) (mrReduce rest) hself,
              mrRemIdem coeff, mrReduceIdem rest]

/-! ## `mrReduce` preserves the sortedness invariants -/

/-- Below-head transports along a `lt` step. -/
theorem mrBelowHeadStep (mono pivot : List Nat) (rest : CsrNF)
    (hlt : csrCompare mono pivot = CsrMonoOrd.lt) (hBelowP : csrBelowHead pivot rest = true) :
    csrBelowHead mono rest = true := by
  cases rest with
  | nil => rfl
  | cons head restTail =>
      obtain ⟨pivot2, coeff2⟩ := head
      exact csrBelowHeadConsTrue mono pivot2 coeff2 restTail
        (csrCompareTransLt mono pivot pivot2 hlt (csrBelowHeadConsLt pivot pivot2 coeff2 restTail hBelowP))

theorem mrReduceBelowHead (mono : List Nat) : (normalForm : CsrNF) →
    csrBelowHead mono normalForm = true → csrNFSorted normalForm = true →
    csrBelowHead mono (mrReduce normalForm) = true
  | [], _, _ => rfl
  | (pivot, coeff) :: rest, hBelow, hSorted => by
      have hlt : csrCompare mono pivot = CsrMonoOrd.lt := csrBelowHeadConsLt mono pivot coeff rest hBelow
      have hBelowP : csrBelowHead pivot rest = true := csrAndTrueLeft _ _ hSorted
      have hRest : csrNFSorted rest = true := csrAndTrueRight _ _ hSorted
      cases hb : Nat.beq (natRemainder coeff mrModulus) 0 with
      | true =>
          rw [mrReduceConsZero pivot coeff rest hb]
          exact mrReduceBelowHead mono rest (mrBelowHeadStep mono pivot rest hlt hBelowP) hRest
      | false =>
          rw [mrReduceConsNonzero pivot coeff rest hb]
          exact csrBelowHeadConsTrue mono pivot (natRemainder coeff mrModulus) (mrReduce rest) hlt

theorem mrReduceSorted : (normalForm : CsrNF) →
    csrNFSorted normalForm = true → csrNFSorted (mrReduce normalForm) = true
  | [], _ => rfl
  | (mono, coeff) :: rest, hSorted => by
      have hBelow : csrBelowHead mono rest = true := csrAndTrueLeft _ _ hSorted
      have hRest : csrNFSorted rest = true := csrAndTrueRight _ _ hSorted
      cases hb : Nat.beq (natRemainder coeff mrModulus) 0 with
      | true => rw [mrReduceConsZero mono coeff rest hb]; exact mrReduceSorted rest hRest
      | false =>
          rw [mrReduceConsNonzero mono coeff rest hb, csrNFSortedCons]
          exact csrAndIntro _ _ (mrReduceBelowHead mono rest hBelow hRest) (mrReduceSorted rest hRest)

/-! ## Reduction absorbs an inserted term that vanishes mod `n` -/

theorem mrReduceInsertZero (mono : List Nat) (coeff : Nat) (hZero : natRemainder coeff mrModulus = 0) :
    (target : CsrNF) → mrReduce (csrInsertTerm (mono, coeff) target) = mrReduce target
  | [] => by
      rw [csrInsertTermNil mono coeff, mrReduceConsZero mono coeff [] (mrBeqZeroOf coeff hZero)]
  | (pivot, existing) :: rest => by
      cases hc : csrCompare mono pivot with
      | eq =>
          rw [csrInsertTermEqE mono coeff pivot existing rest hc]
          have hcoeff : natRemainder (existing + coeff) mrModulus = natRemainder existing mrModulus :=
            mrRemAddZeroModRight existing coeff hZero
          cases he : Nat.beq (natRemainder existing mrModulus) 0 with
          | true =>
              have he' : Nat.beq (natRemainder (existing + coeff) mrModulus) 0 = true := by
                rw [hcoeff]; exact he
              rw [mrReduceConsZero pivot (existing + coeff) rest he',
                  mrReduceConsZero pivot existing rest he]
          | false =>
              have he' : Nat.beq (natRemainder (existing + coeff) mrModulus) 0 = false := by
                rw [hcoeff]; exact he
              rw [mrReduceConsNonzero pivot (existing + coeff) rest he',
                  mrReduceConsNonzero pivot existing rest he, hcoeff]
      | lt =>
          rw [csrInsertTermLtE mono coeff pivot existing rest hc,
              mrReduceConsZero mono coeff ((pivot, existing) :: rest) (mrBeqZeroOf coeff hZero)]
      | gt =>
          rw [csrInsertTermGtE mono coeff pivot existing rest hc]
          cases he : Nat.beq (natRemainder existing mrModulus) 0 with
          | true =>
              rw [mrReduceConsZero pivot existing (csrInsertTerm (mono, coeff) rest) he,
                  mrReduceConsZero pivot existing rest he]
              exact mrReduceInsertZero mono coeff hZero rest
          | false =>
              rw [mrReduceConsNonzero pivot existing (csrInsertTerm (mono, coeff) rest) he,
                  mrReduceConsNonzero pivot existing rest he, mrReduceInsertZero mono coeff hZero rest]

/-! ## The crux: reduction commutes with insertion (reduce the coeff and the tail) -/

theorem mrReduceInsertReduce (mono : List Nat) (coeff : Nat) :
    (target : CsrNF) → csrNFSorted target = true →
    mrReduce (csrInsertTerm (mono, coeff) target)
      = mrReduce (csrInsertTerm (mono, natRemainder coeff mrModulus) (mrReduce target))
  | [], _ => by
      rw [csrInsertTermNil mono coeff]
      show mrReduce [(mono, coeff)]
        = mrReduce (csrInsertTerm (mono, natRemainder coeff mrModulus) [])
      rw [csrInsertTermNil mono (natRemainder coeff mrModulus)]
      cases hb : Nat.beq (natRemainder coeff mrModulus) 0 with
      | true =>
          have hrc : Nat.beq (natRemainder (natRemainder coeff mrModulus) mrModulus) 0 = true := by
            rw [mrRemIdem coeff]; exact hb
          rw [mrReduceConsZero mono coeff [] hb, mrReduceConsZero mono (natRemainder coeff mrModulus) [] hrc]
      | false =>
          have hrc : Nat.beq (natRemainder (natRemainder coeff mrModulus) mrModulus) 0 = false := by
            rw [mrRemIdem coeff]; exact hb
          rw [mrReduceConsNonzero mono coeff [] hb,
              mrReduceConsNonzero mono (natRemainder coeff mrModulus) [] hrc, mrRemIdem coeff]
  | (pivot, existing) :: rest, hSorted => by
      have hBelowP : csrBelowHead pivot rest = true := csrAndTrueLeft _ _ hSorted
      have hRest : csrNFSorted rest = true := csrAndTrueRight _ _ hSorted
      cases hc : csrCompare mono pivot with
      | eq =>
          have hmp : mono = pivot := csrCompareEq_of mono pivot hc
          rw [csrInsertTermEqE mono coeff pivot existing rest hc]
          cases he : Nat.beq (natRemainder existing mrModulus) 0 with
          | true =>
              have hexist0 : natRemainder existing mrModulus = 0 := mrBeqZeroEq existing he
              have hsum : natRemainder (existing + coeff) mrModulus = natRemainder coeff mrModulus :=
                (congrArg (fun z => natRemainder z mrModulus) (Nat.add_comm existing coeff)).trans
                  (mrRemAddZeroModRight coeff existing hexist0)
              rw [mrReduceConsZero pivot existing rest he]
              have hbelow : csrBelowHead mono (mrReduce rest) = true := by
                rw [hmp]; exact mrReduceBelowHead pivot rest hBelowP hRest
              rw [csrInsertFront mono (natRemainder coeff mrModulus) (mrReduce rest) hbelow]
              cases hrc : Nat.beq (natRemainder coeff mrModulus) 0 with
              | true =>
                  have hsum' : Nat.beq (natRemainder (existing + coeff) mrModulus) 0 = true := by
                    rw [hsum]; exact hrc
                  have hrc2 : Nat.beq (natRemainder (natRemainder coeff mrModulus) mrModulus) 0 = true := by
                    rw [mrRemIdem coeff]; exact hrc
                  rw [mrReduceConsZero pivot (existing + coeff) rest hsum',
                      mrReduceConsZero mono (natRemainder coeff mrModulus) (mrReduce rest) hrc2,
                      mrReduceIdem rest]
              | false =>
                  have hsum' : Nat.beq (natRemainder (existing + coeff) mrModulus) 0 = false := by
                    rw [hsum]; exact hrc
                  have hrc2 : Nat.beq (natRemainder (natRemainder coeff mrModulus) mrModulus) 0 = false := by
                    rw [mrRemIdem coeff]; exact hrc
                  rw [mrReduceConsNonzero pivot (existing + coeff) rest hsum',
                      mrReduceConsNonzero mono (natRemainder coeff mrModulus) (mrReduce rest) hrc2,
                      mrReduceIdem rest, hsum, mrRemIdem coeff, hmp]
          | false =>
              rw [mrReduceConsNonzero pivot existing rest he]
              have hpivotcmp : csrCompare mono pivot = CsrMonoOrd.eq := hc
              rw [csrInsertTermEqE mono (natRemainder coeff mrModulus) pivot (natRemainder existing mrModulus)
                    (mrReduce rest) hpivotcmp]
              have hsum : natRemainder (natRemainder existing mrModulus + natRemainder coeff mrModulus) mrModulus
                  = natRemainder (existing + coeff) mrModulus :=
                (mrRemAddPushRight (natRemainder existing mrModulus) coeff).trans
                  (natRemainderAddPush existing coeff mrModulus mrModulusPos)
              cases hsc : Nat.beq (natRemainder (existing + coeff) mrModulus) 0 with
              | true =>
                  have h1 : Nat.beq (natRemainder (existing + coeff) mrModulus) 0 = true := hsc
                  have h2 : Nat.beq
                      (natRemainder (natRemainder existing mrModulus + natRemainder coeff mrModulus) mrModulus)
                      0 = true := by rw [hsum]; exact hsc
                  rw [mrReduceConsZero pivot (existing + coeff) rest h1,
                      mrReduceConsZero pivot (natRemainder existing mrModulus + natRemainder coeff mrModulus)
                        (mrReduce rest) h2, mrReduceIdem rest]
              | false =>
                  have h1 : Nat.beq (natRemainder (existing + coeff) mrModulus) 0 = false := hsc
                  have h2 : Nat.beq
                      (natRemainder (natRemainder existing mrModulus + natRemainder coeff mrModulus) mrModulus)
                      0 = false := by rw [hsum]; exact hsc
                  rw [mrReduceConsNonzero pivot (existing + coeff) rest h1,
                      mrReduceConsNonzero pivot (natRemainder existing mrModulus + natRemainder coeff mrModulus)
                        (mrReduce rest) h2, mrReduceIdem rest, hsum]
      | lt =>
          rw [csrInsertTermLtE mono coeff pivot existing rest hc]
          cases he : Nat.beq (natRemainder existing mrModulus) 0 with
          | true =>
              rw [mrReduceConsZero pivot existing rest he]
              have hbelow : csrBelowHead mono (mrReduce rest) = true :=
                mrReduceBelowHead mono rest (mrBelowHeadStep mono pivot rest hc hBelowP) hRest
              rw [csrInsertFront mono (natRemainder coeff mrModulus) (mrReduce rest) hbelow]
              cases hrc : Nat.beq (natRemainder coeff mrModulus) 0 with
              | true =>
                  have hrc2 : Nat.beq (natRemainder (natRemainder coeff mrModulus) mrModulus) 0 = true := by
                    rw [mrRemIdem coeff]; exact hrc
                  rw [mrReduceConsZero mono coeff ((pivot, existing) :: rest) hrc,
                      mrReduceConsZero mono (natRemainder coeff mrModulus) (mrReduce rest) hrc2,
                      mrReduceConsZero pivot existing rest he, mrReduceIdem rest]
              | false =>
                  have hrc2 : Nat.beq (natRemainder (natRemainder coeff mrModulus) mrModulus) 0 = false := by
                    rw [mrRemIdem coeff]; exact hrc
                  rw [mrReduceConsNonzero mono coeff ((pivot, existing) :: rest) hrc,
                      mrReduceConsNonzero mono (natRemainder coeff mrModulus) (mrReduce rest) hrc2,
                      mrReduceConsZero pivot existing rest he, mrRemIdem coeff, mrReduceIdem rest]
          | false =>
              rw [mrReduceConsNonzero pivot existing rest he]
              rw [csrInsertTermLtE mono (natRemainder coeff mrModulus) pivot
                    (natRemainder existing mrModulus) (mrReduce rest) hc]
              cases hrc : Nat.beq (natRemainder coeff mrModulus) 0 with
              | true =>
                  have hrc2 : Nat.beq (natRemainder (natRemainder coeff mrModulus) mrModulus) 0 = true := by
                    rw [mrRemIdem coeff]; exact hrc
                  have hee : Nat.beq (natRemainder (natRemainder existing mrModulus) mrModulus) 0 = false := by
                    rw [mrRemIdem existing]; exact he
                  rw [mrReduceConsZero mono coeff ((pivot, existing) :: rest) hrc,
                      mrReduceConsZero mono (natRemainder coeff mrModulus)
                        ((pivot, natRemainder existing mrModulus) :: mrReduce rest) hrc2,
                      mrReduceConsNonzero pivot existing rest he,
                      mrReduceConsNonzero pivot (natRemainder existing mrModulus) (mrReduce rest) hee,
                      mrRemIdem existing, mrReduceIdem rest]
              | false =>
                  have hrc2 : Nat.beq (natRemainder (natRemainder coeff mrModulus) mrModulus) 0 = false := by
                    rw [mrRemIdem coeff]; exact hrc
                  have hee : Nat.beq (natRemainder (natRemainder existing mrModulus) mrModulus) 0 = false := by
                    rw [mrRemIdem existing]; exact he
                  rw [mrReduceConsNonzero mono coeff ((pivot, existing) :: rest) hrc,
                      mrReduceConsNonzero mono (natRemainder coeff mrModulus)
                        ((pivot, natRemainder existing mrModulus) :: mrReduce rest) hrc2,
                      mrReduceConsNonzero pivot existing rest he,
                      mrReduceConsNonzero pivot (natRemainder existing mrModulus) (mrReduce rest) hee,
                      mrRemIdem coeff, mrRemIdem existing, mrReduceIdem rest]
      | gt =>
          rw [csrInsertTermGtE mono coeff pivot existing rest hc]
          cases he : Nat.beq (natRemainder existing mrModulus) 0 with
          | true =>
              rw [mrReduceConsZero pivot existing (csrInsertTerm (mono, coeff) rest) he,
                  mrReduceConsZero pivot existing rest he]
              exact mrReduceInsertReduce mono coeff rest hRest
          | false =>
              have hgt : csrCompare mono pivot = CsrMonoOrd.gt := hc
              rw [mrReduceConsNonzero pivot existing (csrInsertTerm (mono, coeff) rest) he,
                  mrReduceConsNonzero pivot existing rest he]
              have hee : Nat.beq (natRemainder (natRemainder existing mrModulus) mrModulus) 0 = false := by
                rw [mrRemIdem existing]; exact he
              rw [csrInsertTermGtE mono (natRemainder coeff mrModulus) pivot
                    (natRemainder existing mrModulus) (mrReduce rest) hgt,
                  mrReduceConsNonzero pivot (natRemainder existing mrModulus)
                    (csrInsertTerm (mono, natRemainder coeff mrModulus) (mrReduce rest)) hee,
                  mrRemIdem existing, mrReduceInsertReduce mono coeff rest hRest]

/-! ## Reduction is a homomorphism for the merge -/

theorem mrReduceMergeHom : (leftForm rightForm : CsrNF) →
    csrNFSorted rightForm = true →
    mrReduce (csrMergeAdd leftForm rightForm)
      = mrReduce (csrMergeAdd (mrReduce leftForm) (mrReduce rightForm))
  | [], rightForm, _ => by
      show mrReduce rightForm = mrReduce (csrMergeAdd [] (mrReduce rightForm))
      rw [csrMergeAddNilLeft (mrReduce rightForm), mrReduceIdem rightForm]
  | (mono, coeff) :: leftTail, rightForm, hRight => by
      have hMergeSorted : csrNFSorted (csrMergeAdd leftTail rightForm) = true :=
        csrMergeAddPreservesSorted leftTail rightForm hRight
      have hReducedRightSorted : csrNFSorted (mrReduce rightForm) = true := mrReduceSorted rightForm hRight
      have hMergeReducedSorted :
          csrNFSorted (csrMergeAdd (mrReduce leftTail) (mrReduce rightForm)) = true :=
        csrMergeAddPreservesSorted (mrReduce leftTail) (mrReduce rightForm) hReducedRightSorted
      have ih : mrReduce (csrMergeAdd leftTail rightForm)
          = mrReduce (csrMergeAdd (mrReduce leftTail) (mrReduce rightForm)) :=
        mrReduceMergeHom leftTail rightForm hRight
      -- LHS = mrReduce (csrInsertTerm (mono, natRemainder coeff) (mrReduce (merge (reduce leftTail) (reduce rightForm))))
      rw [csrMergeAddCons (mono, coeff) leftTail rightForm,
          mrReduceInsertReduce mono coeff (csrMergeAdd leftTail rightForm) hMergeSorted, ih]
      cases hb : Nat.beq (natRemainder coeff mrModulus) 0 with
      | true =>
          rw [mrReduceConsZero mono coeff leftTail hb]
          have hz' : natRemainder (natRemainder coeff mrModulus) mrModulus = 0 :=
            (mrRemIdem coeff).trans (mrBeqZeroEq coeff hb)
          rw [mrReduceInsertZero mono (natRemainder coeff mrModulus) hz'
                (mrReduce (csrMergeAdd (mrReduce leftTail) (mrReduce rightForm))),
              mrReduceIdem (csrMergeAdd (mrReduce leftTail) (mrReduce rightForm))]
      | false =>
          rw [mrReduceConsNonzero mono coeff leftTail hb,
              csrMergeAddCons (mono, natRemainder coeff mrModulus) (mrReduce leftTail) (mrReduce rightForm),
              mrReduceInsertReduce mono (natRemainder coeff mrModulus)
                (csrMergeAdd (mrReduce leftTail) (mrReduce rightForm)) hMergeReducedSorted,
              mrRemIdem coeff]

/-! ## Reduction is a homomorphism for term-scaling and the convolution -/

/-- A scalar that vanishes mod `n` makes the whole term-scaling vanish. -/
theorem mrReduceTermMulZero (mono : List Nat) (coeff : Nat)
    (hZero : natRemainder coeff mrModulus = 0) :
    (rightForm : CsrNF) → mrReduce (csrTermMul mono coeff rightForm) = []
  | [] => rfl
  | (innerMono, innerCoeff) :: rest => by
      rw [csrTermMulCons mono coeff innerMono innerCoeff rest,
          mrReduceInsertZero (csrMonoMul mono innerMono) (coeff * innerCoeff)
            (mrRemMulZeroMod coeff innerCoeff hZero) (csrTermMul mono coeff rest),
          mrReduceTermMulZero mono coeff hZero rest]

/-- Reduction commutes with term-scaling after reducing the SCALAR. -/
theorem mrReduceTermMulScalar (mono : List Nat) (coeff : Nat) :
    (rightForm : CsrNF) →
    mrReduce (csrTermMul mono coeff rightForm)
      = mrReduce (csrTermMul mono (natRemainder coeff mrModulus) rightForm)
  | [] => rfl
  | (innerMono, innerCoeff) :: rest => by
      have ih : mrReduce (csrTermMul mono coeff rest)
          = mrReduce (csrTermMul mono (natRemainder coeff mrModulus) rest) :=
        mrReduceTermMulScalar mono coeff rest
      rw [csrTermMulCons mono coeff innerMono innerCoeff rest,
          csrTermMulCons mono (natRemainder coeff mrModulus) innerMono innerCoeff rest,
          mrReduceInsertReduce (csrMonoMul mono innerMono) (coeff * innerCoeff)
            (csrTermMul mono coeff rest) (csrTermMulSorted mono coeff rest),
          mrReduceInsertReduce (csrMonoMul mono innerMono) (natRemainder coeff mrModulus * innerCoeff)
            (csrTermMul mono (natRemainder coeff mrModulus) rest)
            (csrTermMulSorted mono (natRemainder coeff mrModulus) rest), ih]
      have hcoeff : natRemainder (coeff * innerCoeff) mrModulus
          = natRemainder (natRemainder coeff mrModulus * innerCoeff) mrModulus :=
        (natRemainderMulPush coeff innerCoeff mrModulus mrModulusPos).symm
      rw [hcoeff]

/-- Reduction commutes with term-scaling after reducing the polynomial argument. -/
theorem mrReduceTermMulRightHom (mono : List Nat) (coeff : Nat) :
    (rightForm : CsrNF) →
    mrReduce (csrTermMul mono coeff rightForm)
      = mrReduce (csrTermMul mono coeff (mrReduce rightForm))
  | [] => rfl
  | (innerMono, innerCoeff) :: rest => by
      have ih : mrReduce (csrTermMul mono coeff rest)
          = mrReduce (csrTermMul mono coeff (mrReduce rest)) := mrReduceTermMulRightHom mono coeff rest
      rw [csrTermMulCons mono coeff innerMono innerCoeff rest,
          mrReduceInsertReduce (csrMonoMul mono innerMono) (coeff * innerCoeff)
            (csrTermMul mono coeff rest) (csrTermMulSorted mono coeff rest), ih]
      cases hd : Nat.beq (natRemainder innerCoeff mrModulus) 0 with
      | true =>
          rw [mrReduceConsZero innerMono innerCoeff rest hd]
          have hz : natRemainder (coeff * innerCoeff) mrModulus = 0 :=
            (congrArg (fun z => natRemainder z mrModulus) (Nat.mul_comm coeff innerCoeff)).trans
              (mrRemMulZeroMod innerCoeff coeff (mrBeqZeroEq innerCoeff hd))
          have hz' : natRemainder (natRemainder (coeff * innerCoeff) mrModulus) mrModulus = 0 :=
            (mrRemIdem (coeff * innerCoeff)).trans hz
          rw [mrReduceInsertZero (csrMonoMul mono innerMono) (natRemainder (coeff * innerCoeff) mrModulus)
                hz' (mrReduce (csrTermMul mono coeff (mrReduce rest))),
              mrReduceIdem (csrTermMul mono coeff (mrReduce rest))]
      | false =>
          rw [mrReduceConsNonzero innerMono innerCoeff rest hd,
              csrTermMulCons mono coeff innerMono (natRemainder innerCoeff mrModulus) (mrReduce rest),
              mrReduceInsertReduce (csrMonoMul mono innerMono) (coeff * natRemainder innerCoeff mrModulus)
                (csrTermMul mono coeff (mrReduce rest)) (csrTermMulSorted mono coeff (mrReduce rest)),
              mrRemMulPushRight coeff innerCoeff]

theorem mrReduceConvolveHom : (leftForm rightForm : CsrNF) →
    csrNFSorted rightForm = true →
    mrReduce (csrMulConvolve leftForm rightForm)
      = mrReduce (csrMulConvolve (mrReduce leftForm) (mrReduce rightForm))
  | [], _, _ => rfl
  | (mono, coeff) :: leftTail, rightForm, hRight => by
      have ih : mrReduce (csrMulConvolve leftTail rightForm)
          = mrReduce (csrMulConvolve (mrReduce leftTail) (mrReduce rightForm)) :=
        mrReduceConvolveHom leftTail rightForm hRight
      rw [csrMulConvolveCons mono coeff leftTail rightForm,
          mrReduceMergeHom (csrTermMul mono coeff rightForm) (csrMulConvolve leftTail rightForm)
            (csrMulConvolveSorted leftTail rightForm),
          mrReduceTermMulRightHom mono coeff rightForm, ih]
      -- LHS = mrReduce (merge (mrReduce (termMul mono coeff (reduce right)))
      --                        (mrReduce (convolve (reduce leftTail) (reduce right))))
      cases hb : Nat.beq (natRemainder coeff mrModulus) 0 with
      | true =>
          rw [mrReduceConsZero mono coeff leftTail hb,
              mrReduceTermMulZero mono coeff (mrBeqZeroEq coeff hb) (mrReduce rightForm),
              csrMergeAddNilLeft,
              mrReduceIdem (csrMulConvolve (mrReduce leftTail) (mrReduce rightForm))]
      | false =>
          rw [mrReduceConsNonzero mono coeff leftTail hb,
              csrMulConvolveCons mono (natRemainder coeff mrModulus) (mrReduce leftTail) (mrReduce rightForm),
              mrReduceMergeHom (csrTermMul mono (natRemainder coeff mrModulus) (mrReduce rightForm))
                (csrMulConvolve (mrReduce leftTail) (mrReduce rightForm))
                (csrMulConvolveSorted (mrReduce leftTail) (mrReduce rightForm)),
              mrReduceTermMulScalar mono coeff (mrReduce rightForm)]

/-! ## The tree carrier and the base (ℕ[X]) normalizer -/

/-- ★ the free commutative-ring-over-ℤ/n tree carrier. -/
inductive MrTree where
  /-- a colour-tagged generator (variable). -/
  | gen (colour : Nat)
  /-- the additive unit `0`. -/
  | zeroOp
  /-- the multiplicative unit `1`. -/
  | oneOp
  /-- binary addition. -/
  | addOp : MrTree → MrTree → MrTree
  /-- binary multiplication. -/
  | mulOp : MrTree → MrTree → MrTree

/-- The ℕ[X] normal form of a tree — reuses the imported `csrMergeAdd` / `csrMulConvolve` engine. -/
def mrBaseNormalize : MrTree → CsrNF
  | .gen colour => [([colour], 1)]
  | .zeroOp => []
  | .oneOp => [([], 1)]
  | .addOp leftTree rightTree => csrMergeAdd (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)
  | .mulOp leftTree rightTree => csrMulConvolve (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)

theorem mrBaseNormalizeSorted : (tree : MrTree) → csrNFSorted (mrBaseNormalize tree) = true
  | .gen _ => rfl
  | .zeroOp => rfl
  | .oneOp => rfl
  | .addOp leftTree rightTree =>
      csrMergeAddPreservesSorted (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)
        (mrBaseNormalizeSorted rightTree)
  | .mulOp leftTree rightTree =>
      csrMulConvolveSorted (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)

theorem mrBaseNormalizeMonoSorted : (tree : MrTree) → csrNFMonoSorted (mrBaseNormalize tree) = true
  | .gen _ => rfl
  | .zeroOp => rfl
  | .oneOp => rfl
  | .addOp leftTree rightTree =>
      csrMergeAddMonoSorted (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)
        (mrBaseNormalizeMonoSorted leftTree) (mrBaseNormalizeMonoSorted rightTree)
  | .mulOp leftTree rightTree =>
      csrMulConvolveMonoSorted (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)
        (mrBaseNormalizeMonoSorted leftTree) (mrBaseNormalizeMonoSorted rightTree)

/-- ★ the modular normal form: reduce the ℕ[X] normal form mod `mrModulus`. -/
def mrNormalize (tree : MrTree) : CsrNF := mrReduce (mrBaseNormalize tree)

theorem mrNormalize_zero_smoke : mrNormalize MrTree.zeroOp = [] := rfl
theorem mrNormalize_one_smoke : mrNormalize MrTree.oneOp = [([], 1)] := rfl

/-! ## Characteristic-`n` data: `mrModulus` copies of `1` -/

/-- `count` copies of `oneOp` added together. -/
def mrSumOfOnes : Nat → MrTree
  | 0 => MrTree.zeroOp
  | Nat.succ k => MrTree.addOp MrTree.oneOp (mrSumOfOnes k)

/-- The constant polynomial `count · 1` as a normal form. -/
def mrConstNF : Nat → CsrNF
  | 0 => []
  | Nat.succ k => [([], Nat.succ k)]

theorem mrInsertOneConstNF : (count : Nat) →
    csrInsertTerm ([], 1) (mrConstNF count) = mrConstNF (Nat.succ count)
  | 0 => rfl
  | Nat.succ j => by
      show csrInsertTerm ([], 1) [([], Nat.succ j)] = [([], Nat.succ (Nat.succ j))]
      rw [csrInsertTermEqE [] 1 [] (Nat.succ j) [] (csrCompareRefl [])]

theorem mrBaseNormalizeSumOfOnes : (count : Nat) → mrBaseNormalize (mrSumOfOnes count) = mrConstNF count
  | 0 => rfl
  | Nat.succ j => by
      show csrMergeAdd (mrBaseNormalize MrTree.oneOp) (mrBaseNormalize (mrSumOfOnes j)) = mrConstNF (Nat.succ j)
      rw [mrBaseNormalizeSumOfOnes j]
      show csrMergeAdd [([], 1)] (mrConstNF j) = mrConstNF (Nat.succ j)
      rw [csrMergeAddCons ([], 1) [] (mrConstNF j), csrMergeAddNilLeft (mrConstNF j), mrInsertOneConstNF j]

/-- The characteristic collapse at the normal-form level: `mrModulus · 1` reduces to `[]`. -/
theorem mrReduceSingletonModulus : mrReduce [([], mrModulus)] = [] := by
  have hself : natRemainder mrModulus mrModulus = 0 := natRemainderSelf mrModulusPos
  rw [mrReduceConsZero [] mrModulus [] (mrBeqZeroOf mrModulus hself), mrReduceNil]

/-! ## Modular-ring convertibility (the ℕ[X] semiring laws PLUS the characteristic law) -/

/-- ★ commutative-ring-over-ℤ/n convertibility. -/
inductive ModularRingTreeConv : MrTree → MrTree → Prop where
  | addAssoc (a b c : MrTree) :
      ModularRingTreeConv (MrTree.addOp (MrTree.addOp a b) c) (MrTree.addOp a (MrTree.addOp b c))
  | addComm (a b : MrTree) : ModularRingTreeConv (MrTree.addOp a b) (MrTree.addOp b a)
  | addZero (a : MrTree) : ModularRingTreeConv (MrTree.addOp a MrTree.zeroOp) a
  | mulAssoc (a b c : MrTree) :
      ModularRingTreeConv (MrTree.mulOp (MrTree.mulOp a b) c) (MrTree.mulOp a (MrTree.mulOp b c))
  | mulComm (a b : MrTree) : ModularRingTreeConv (MrTree.mulOp a b) (MrTree.mulOp b a)
  | mulOne (a : MrTree) : ModularRingTreeConv (MrTree.mulOp a MrTree.oneOp) a
  | distribLeft (a b c : MrTree) :
      ModularRingTreeConv (MrTree.mulOp a (MrTree.addOp b c))
        (MrTree.addOp (MrTree.mulOp a b) (MrTree.mulOp a c))
  | annihilRight (a : MrTree) : ModularRingTreeConv (MrTree.mulOp a MrTree.zeroOp) MrTree.zeroOp
  | addCongr {leftOld leftNew rightOld rightNew : MrTree} :
      ModularRingTreeConv leftOld leftNew → ModularRingTreeConv rightOld rightNew →
      ModularRingTreeConv (MrTree.addOp leftOld rightOld) (MrTree.addOp leftNew rightNew)
  | mulCongr {leftOld leftNew rightOld rightNew : MrTree} :
      ModularRingTreeConv leftOld leftNew → ModularRingTreeConv rightOld rightNew →
      ModularRingTreeConv (MrTree.mulOp leftOld rightOld) (MrTree.mulOp leftNew rightNew)
  | refl (t : MrTree) : ModularRingTreeConv t t
  | symm {s t : MrTree} : ModularRingTreeConv s t → ModularRingTreeConv t s
  | trans {s t u : MrTree} : ModularRingTreeConv s t → ModularRingTreeConv t u → ModularRingTreeConv s u
  /-- ★ the characteristic law: `mrModulus` copies of `1` are `≈ 0`. -/
  | nTimesOne : ModularRingTreeConv (mrSumOfOnes mrModulus) MrTree.zeroOp

/-! ## Soundness -/

/-- The additive congruence at normal-form level, via the merge homomorphism. -/
theorem mrNormalizeAddCongr {leftOld leftNew rightOld rightNew : MrTree}
    (hLeft : mrNormalize leftOld = mrNormalize leftNew)
    (hRight : mrNormalize rightOld = mrNormalize rightNew) :
    mrNormalize (MrTree.addOp leftOld rightOld) = mrNormalize (MrTree.addOp leftNew rightNew) := by
  show mrReduce (csrMergeAdd (mrBaseNormalize leftOld) (mrBaseNormalize rightOld))
     = mrReduce (csrMergeAdd (mrBaseNormalize leftNew) (mrBaseNormalize rightNew))
  rw [mrReduceMergeHom (mrBaseNormalize leftOld) (mrBaseNormalize rightOld)
        (mrBaseNormalizeSorted rightOld),
      mrReduceMergeHom (mrBaseNormalize leftNew) (mrBaseNormalize rightNew)
        (mrBaseNormalizeSorted rightNew),
      show mrReduce (mrBaseNormalize leftOld) = mrReduce (mrBaseNormalize leftNew) from hLeft,
      show mrReduce (mrBaseNormalize rightOld) = mrReduce (mrBaseNormalize rightNew) from hRight]

/-- The multiplicative congruence at normal-form level, via the convolution homomorphism. -/
theorem mrNormalizeMulCongr {leftOld leftNew rightOld rightNew : MrTree}
    (hLeft : mrNormalize leftOld = mrNormalize leftNew)
    (hRight : mrNormalize rightOld = mrNormalize rightNew) :
    mrNormalize (MrTree.mulOp leftOld rightOld) = mrNormalize (MrTree.mulOp leftNew rightNew) := by
  show mrReduce (csrMulConvolve (mrBaseNormalize leftOld) (mrBaseNormalize rightOld))
     = mrReduce (csrMulConvolve (mrBaseNormalize leftNew) (mrBaseNormalize rightNew))
  rw [mrReduceConvolveHom (mrBaseNormalize leftOld) (mrBaseNormalize rightOld)
        (mrBaseNormalizeSorted rightOld),
      mrReduceConvolveHom (mrBaseNormalize leftNew) (mrBaseNormalize rightNew)
        (mrBaseNormalizeSorted rightNew),
      show mrReduce (mrBaseNormalize leftOld) = mrReduce (mrBaseNormalize leftNew) from hLeft,
      show mrReduce (mrBaseNormalize rightOld) = mrReduce (mrBaseNormalize rightNew) from hRight]

/-- ★ soundness: convertible trees have equal modular normal form. -/
theorem mrNormalize_respects {s t : MrTree} (conv : ModularRingTreeConv s t) :
    mrNormalize s = mrNormalize t := by
  induction conv with
  | addAssoc a b c =>
      show mrReduce (csrMergeAdd (csrMergeAdd (mrBaseNormalize a) (mrBaseNormalize b)) (mrBaseNormalize c))
         = mrReduce (csrMergeAdd (mrBaseNormalize a) (csrMergeAdd (mrBaseNormalize b) (mrBaseNormalize c)))
      exact congrArg mrReduce (csrMergeAddAssoc (mrBaseNormalize a) (mrBaseNormalize b) (mrBaseNormalize c))
  | addComm a b =>
      show mrReduce (csrMergeAdd (mrBaseNormalize a) (mrBaseNormalize b))
         = mrReduce (csrMergeAdd (mrBaseNormalize b) (mrBaseNormalize a))
      exact congrArg mrReduce (csrMergeAddComm (mrBaseNormalize a) (mrBaseNormalize b)
        (mrBaseNormalizeSorted a) (mrBaseNormalizeSorted b))
  | addZero a =>
      show mrReduce (csrMergeAdd (mrBaseNormalize a) []) = mrReduce (mrBaseNormalize a)
      exact congrArg mrReduce (csrMergeAddNilRight (mrBaseNormalize a) (mrBaseNormalizeSorted a))
  | mulAssoc a b c =>
      show mrReduce (csrMulConvolve (csrMulConvolve (mrBaseNormalize a) (mrBaseNormalize b)) (mrBaseNormalize c))
         = mrReduce (csrMulConvolve (mrBaseNormalize a) (csrMulConvolve (mrBaseNormalize b) (mrBaseNormalize c)))
      exact congrArg mrReduce (csrMulConvolveAssoc (mrBaseNormalize a) (mrBaseNormalize b) (mrBaseNormalize c))
  | mulComm a b =>
      show mrReduce (csrMulConvolve (mrBaseNormalize a) (mrBaseNormalize b))
         = mrReduce (csrMulConvolve (mrBaseNormalize b) (mrBaseNormalize a))
      exact congrArg mrReduce (csrMulConvolveComm (mrBaseNormalize a) (mrBaseNormalize b)
        (mrBaseNormalizeSorted a) (mrBaseNormalizeMonoSorted a) (mrBaseNormalizeMonoSorted b))
  | mulOne a =>
      show mrReduce (csrMulConvolve (mrBaseNormalize a) [([], 1)]) = mrReduce (mrBaseNormalize a)
      exact congrArg mrReduce (csrMulConvolveUnit (mrBaseNormalize a) (mrBaseNormalizeSorted a))
  | distribLeft a b c =>
      show mrReduce (csrMulConvolve (mrBaseNormalize a) (csrMergeAdd (mrBaseNormalize b) (mrBaseNormalize c)))
         = mrReduce (csrMergeAdd (csrMulConvolve (mrBaseNormalize a) (mrBaseNormalize b))
             (csrMulConvolve (mrBaseNormalize a) (mrBaseNormalize c)))
      exact congrArg mrReduce
        (csrMulConvolve_leftDistrib (mrBaseNormalize a) (mrBaseNormalize b) (mrBaseNormalize c))
  | annihilRight a =>
      show mrReduce (csrMulConvolve (mrBaseNormalize a) []) = mrReduce []
      exact congrArg mrReduce (csrMulConvolveAnnihil (mrBaseNormalize a))
  | addCongr _ _ ihl ihr => exact mrNormalizeAddCongr ihl ihr
  | mulCongr _ _ ihl ihr => exact mrNormalizeMulCongr ihl ihr
  | refl t => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | nTimesOne =>
      show mrReduce (mrBaseNormalize (mrSumOfOnes mrModulus)) = mrReduce (mrBaseNormalize MrTree.zeroOp)
      rw [mrBaseNormalizeSumOfOnes mrModulus]
      exact mrReduceSingletonModulus

/-! ## The reification tower (fresh `mr`-prefixed copies over `ModularRingTreeConv`) -/

theorem mrConvAddZeroLeft (a : MrTree) : ModularRingTreeConv (MrTree.addOp MrTree.zeroOp a) a :=
  (ModularRingTreeConv.addComm MrTree.zeroOp a).trans (ModularRingTreeConv.addZero a)
theorem mrConvMulOneLeft (a : MrTree) : ModularRingTreeConv (MrTree.mulOp MrTree.oneOp a) a :=
  (ModularRingTreeConv.mulComm MrTree.oneOp a).trans (ModularRingTreeConv.mulOne a)
theorem mrConvAnnihilLeft (a : MrTree) :
    ModularRingTreeConv (MrTree.mulOp MrTree.zeroOp a) MrTree.zeroOp :=
  (ModularRingTreeConv.mulComm MrTree.zeroOp a).trans (ModularRingTreeConv.annihilRight a)
theorem mrConvDistribRight (a b c : MrTree) :
    ModularRingTreeConv (MrTree.mulOp (MrTree.addOp a b) c)
      (MrTree.addOp (MrTree.mulOp a c) (MrTree.mulOp b c)) :=
  (ModularRingTreeConv.mulComm (MrTree.addOp a b) c).trans
    ((ModularRingTreeConv.distribLeft c a b).trans
      (ModularRingTreeConv.addCongr (ModularRingTreeConv.mulComm c a) (ModularRingTreeConv.mulComm c b)))
theorem mrConvAddSwap13 (x y z : MrTree) :
    ModularRingTreeConv (MrTree.addOp x (MrTree.addOp y z)) (MrTree.addOp y (MrTree.addOp x z)) :=
  (ModularRingTreeConv.symm (ModularRingTreeConv.addAssoc x y z)).trans
    ((ModularRingTreeConv.addCongr (ModularRingTreeConv.addComm x y) (ModularRingTreeConv.refl z)).trans
      (ModularRingTreeConv.addAssoc y x z))
theorem mrConvMulSwap13 (x y z : MrTree) :
    ModularRingTreeConv (MrTree.mulOp x (MrTree.mulOp y z)) (MrTree.mulOp y (MrTree.mulOp x z)) :=
  (ModularRingTreeConv.symm (ModularRingTreeConv.mulAssoc x y z)).trans
    ((ModularRingTreeConv.mulCongr (ModularRingTreeConv.mulComm x y) (ModularRingTreeConv.refl z)).trans
      (ModularRingTreeConv.mulAssoc y x z))

def mrScaleTree (mono : MrTree) : Nat → MrTree
  | 0 => MrTree.zeroOp
  | Nat.succ k => MrTree.addOp mono (mrScaleTree mono k)
theorem mrScaleTreeCongr {mono1 mono2 : MrTree} (h : ModularRingTreeConv mono1 mono2) (count : Nat) :
    ModularRingTreeConv (mrScaleTree mono1 count) (mrScaleTree mono2 count) := by
  induction count with
  | zero => exact ModularRingTreeConv.refl MrTree.zeroOp
  | succ k ih => exact ModularRingTreeConv.addCongr h ih
theorem mrScaleAdd (mono : MrTree) (leftCount rightCount : Nat) :
    ModularRingTreeConv (mrScaleTree mono (leftCount + rightCount))
      (MrTree.addOp (mrScaleTree mono leftCount) (mrScaleTree mono rightCount)) := by
  induction rightCount with
  | zero => exact (ModularRingTreeConv.addZero (mrScaleTree mono leftCount)).symm
  | succ k ih =>
      exact (ModularRingTreeConv.addCongr (ModularRingTreeConv.refl mono) ih).trans
        (mrConvAddSwap13 mono (mrScaleTree mono leftCount) (mrScaleTree mono k))
theorem mrScaleTreeMulLeft (p q : MrTree) (count : Nat) :
    ModularRingTreeConv (mrScaleTree (MrTree.mulOp p q) count) (MrTree.mulOp (mrScaleTree p count) q) := by
  induction count with
  | zero => exact (mrConvAnnihilLeft q).symm
  | succ k ih =>
      exact (ModularRingTreeConv.addCongr (ModularRingTreeConv.refl (MrTree.mulOp p q)) ih).trans
        (mrConvDistribRight p (mrScaleTree p k) q).symm
theorem mrScaleTreeMulRight (p q : MrTree) (count : Nat) :
    ModularRingTreeConv (mrScaleTree (MrTree.mulOp p q) count) (MrTree.mulOp p (mrScaleTree q count)) := by
  induction count with
  | zero => exact (ModularRingTreeConv.annihilRight p).symm
  | succ k ih =>
      exact (ModularRingTreeConv.addCongr (ModularRingTreeConv.refl (MrTree.mulOp p q)) ih).trans
        (ModularRingTreeConv.distribLeft p q (mrScaleTree q k)).symm
theorem mrScaleTreeMulCoeff (baseTree : MrTree) (leftCount rightCount : Nat) :
    ModularRingTreeConv (mrScaleTree baseTree (leftCount * rightCount))
      (mrScaleTree (mrScaleTree baseTree rightCount) leftCount) := by
  induction leftCount with
  | zero => rw [Nat.zero_mul rightCount]; exact ModularRingTreeConv.refl MrTree.zeroOp
  | succ k ih =>
      rw [Nat.succ_mul k rightCount]
      exact (mrScaleAdd baseTree (k * rightCount) rightCount).trans
        ((ModularRingTreeConv.addCongr ih (ModularRingTreeConv.refl (mrScaleTree baseTree rightCount))).trans
          (ModularRingTreeConv.addComm (mrScaleTree (mrScaleTree baseTree rightCount) k)
            (mrScaleTree baseTree rightCount)))

def mrMonoToTree : List Nat → MrTree
  | [] => MrTree.oneOp
  | colour :: rest => MrTree.mulOp (MrTree.gen colour) (mrMonoToTree rest)
theorem mrMonoToTreeInsertSorted (value : Nat) (xs : List Nat) :
    ModularRingTreeConv (mrMonoToTree (insertSorted value xs))
      (MrTree.mulOp (MrTree.gen value) (mrMonoToTree xs)) := by
  induction xs with
  | nil => exact ModularRingTreeConv.refl (MrTree.mulOp (MrTree.gen value) MrTree.oneOp)
  | cons headColour rest ih =>
      cases hva : natBle value headColour with
      | true =>
          rw [insertSortedConsTrue value headColour rest hva]
          exact ModularRingTreeConv.refl _
      | false =>
          rw [insertSortedConsFalse value headColour rest hva]
          show ModularRingTreeConv (MrTree.mulOp (MrTree.gen headColour) (mrMonoToTree (insertSorted value rest)))
            (MrTree.mulOp (MrTree.gen value) (MrTree.mulOp (MrTree.gen headColour) (mrMonoToTree rest)))
          exact (ModularRingTreeConv.mulCongr (ModularRingTreeConv.refl (MrTree.gen headColour)) ih).trans
            (mrConvMulSwap13 (MrTree.gen headColour) (MrTree.gen value) (mrMonoToTree rest))
theorem mrMonoToTreeInsertMany (source target : List Nat) :
    ModularRingTreeConv (mrMonoToTree (insertMany source target))
      (MrTree.mulOp (mrMonoToTree source) (mrMonoToTree target)) := by
  induction source with
  | nil => exact (mrConvMulOneLeft (mrMonoToTree target)).symm
  | cons headColour sourceTail ih =>
      show ModularRingTreeConv (mrMonoToTree (insertSorted headColour (insertMany sourceTail target)))
        (MrTree.mulOp (MrTree.mulOp (MrTree.gen headColour) (mrMonoToTree sourceTail)) (mrMonoToTree target))
      exact (mrMonoToTreeInsertSorted headColour (insertMany sourceTail target)).trans
        ((ModularRingTreeConv.mulCongr (ModularRingTreeConv.refl (MrTree.gen headColour)) ih).trans
          (ModularRingTreeConv.symm
            (ModularRingTreeConv.mulAssoc (MrTree.gen headColour) (mrMonoToTree sourceTail)
              (mrMonoToTree target))))
theorem mrMonoToTreeMonoMul (leftMono rightMono : List Nat) :
    ModularRingTreeConv (mrMonoToTree (csrMonoMul leftMono rightMono))
      (MrTree.mulOp (mrMonoToTree leftMono) (mrMonoToTree rightMono)) := by
  show ModularRingTreeConv (mrMonoToTree (insertMany rightMono leftMono))
    (MrTree.mulOp (mrMonoToTree leftMono) (mrMonoToTree rightMono))
  exact (mrMonoToTreeInsertMany rightMono leftMono).trans
    (ModularRingTreeConv.mulComm (mrMonoToTree rightMono) (mrMonoToTree leftMono))

def mrTermToTree (mono : List Nat) (coeff : Nat) : MrTree := mrScaleTree (mrMonoToTree mono) coeff
theorem mrTermToTreeMul (leftMono : List Nat) (leftCoeff : Nat) (rightMono : List Nat) (rightCoeff : Nat) :
    ModularRingTreeConv (mrTermToTree (csrMonoMul leftMono rightMono) (leftCoeff * rightCoeff))
      (MrTree.mulOp (mrTermToTree leftMono leftCoeff) (mrTermToTree rightMono rightCoeff)) := by
  show ModularRingTreeConv (mrScaleTree (mrMonoToTree (csrMonoMul leftMono rightMono)) (leftCoeff * rightCoeff))
    (MrTree.mulOp (mrScaleTree (mrMonoToTree leftMono) leftCoeff) (mrScaleTree (mrMonoToTree rightMono) rightCoeff))
  exact (mrScaleTreeCongr (mrMonoToTreeMonoMul leftMono rightMono) (leftCoeff * rightCoeff)).trans
    ((mrScaleTreeMulCoeff (MrTree.mulOp (mrMonoToTree leftMono) (mrMonoToTree rightMono)) leftCoeff rightCoeff).trans
      ((mrScaleTreeCongr (mrScaleTreeMulRight (mrMonoToTree leftMono) (mrMonoToTree rightMono) rightCoeff)
          leftCoeff).trans
        (mrScaleTreeMulLeft (mrMonoToTree leftMono) (mrScaleTree (mrMonoToTree rightMono) rightCoeff) leftCoeff)))

/-- rebuild a canonical tree from a normal form. -/
def mrCombOfNF : CsrNF → MrTree
  | [] => MrTree.zeroOp
  | (mono, coeff) :: rest => MrTree.addOp (mrTermToTree mono coeff) (mrCombOfNF rest)
theorem mrCombOfNFCons (mono : List Nat) (coeff : Nat) (rest : CsrNF) :
    mrCombOfNF ((mono, coeff) :: rest) = MrTree.addOp (mrTermToTree mono coeff) (mrCombOfNF rest) := rfl

theorem mrCombInsertTerm (mono : List Nat) (coeff : Nat) (target : CsrNF) :
    ModularRingTreeConv (mrCombOfNF (csrInsertTerm (mono, coeff) target))
      (MrTree.addOp (mrTermToTree mono coeff) (mrCombOfNF target)) := by
  induction target with
  | nil => exact ModularRingTreeConv.refl _
  | cons head rest ih =>
      obtain ⟨pivot, existing⟩ := head
      cases hmp : csrCompare mono pivot with
      | eq =>
          have hmeqp : mono = pivot := csrCompareEq_of mono pivot hmp
          rw [csrInsertTermEqE mono coeff pivot existing rest hmp, mrCombOfNFCons pivot (existing + coeff) rest,
              mrCombOfNFCons pivot existing rest, hmeqp]
          exact (ModularRingTreeConv.addCongr (mrScaleAdd (mrMonoToTree pivot) existing coeff)
              (ModularRingTreeConv.refl (mrCombOfNF rest))).trans
            ((ModularRingTreeConv.addAssoc (mrTermToTree pivot existing) (mrTermToTree pivot coeff)
                (mrCombOfNF rest)).trans
              (mrConvAddSwap13 (mrTermToTree pivot existing) (mrTermToTree pivot coeff) (mrCombOfNF rest)))
      | lt =>
          rw [csrInsertTermLtE mono coeff pivot existing rest hmp, mrCombOfNFCons mono coeff ((pivot, existing) :: rest)]
          exact ModularRingTreeConv.refl _
      | gt =>
          rw [csrInsertTermGtE mono coeff pivot existing rest hmp,
              mrCombOfNFCons pivot existing (csrInsertTerm (mono, coeff) rest), mrCombOfNFCons pivot existing rest]
          exact (ModularRingTreeConv.addCongr (ModularRingTreeConv.refl (mrTermToTree pivot existing)) ih).trans
            (mrConvAddSwap13 (mrTermToTree pivot existing) (mrTermToTree mono coeff) (mrCombOfNF rest))

theorem mrCombMergeAdd (leftForm rightForm : CsrNF) :
    ModularRingTreeConv (mrCombOfNF (csrMergeAdd leftForm rightForm))
      (MrTree.addOp (mrCombOfNF leftForm) (mrCombOfNF rightForm)) := by
  induction leftForm with
  | nil => exact (mrConvAddZeroLeft (mrCombOfNF rightForm)).symm
  | cons head leftTail ih =>
      obtain ⟨mono, coeff⟩ := head
      show ModularRingTreeConv (mrCombOfNF (csrInsertTerm (mono, coeff) (csrMergeAdd leftTail rightForm)))
        (MrTree.addOp (MrTree.addOp (mrTermToTree mono coeff) (mrCombOfNF leftTail)) (mrCombOfNF rightForm))
      exact ((mrCombInsertTerm mono coeff (csrMergeAdd leftTail rightForm)).trans
          (ModularRingTreeConv.addCongr (ModularRingTreeConv.refl (mrTermToTree mono coeff)) ih)).trans
        (ModularRingTreeConv.symm
          (ModularRingTreeConv.addAssoc (mrTermToTree mono coeff) (mrCombOfNF leftTail) (mrCombOfNF rightForm)))

theorem mrCombTermMul (mono : List Nat) (coeff : Nat) (rightForm : CsrNF) :
    ModularRingTreeConv (mrCombOfNF (csrTermMul mono coeff rightForm))
      (MrTree.mulOp (mrTermToTree mono coeff) (mrCombOfNF rightForm)) := by
  induction rightForm with
  | nil => exact (ModularRingTreeConv.annihilRight (mrTermToTree mono coeff)).symm
  | cons head rightTail ih =>
      obtain ⟨innerMono, innerCoeff⟩ := head
      show ModularRingTreeConv (mrCombOfNF (csrInsertTerm (csrMonoMul mono innerMono, coeff * innerCoeff)
          (csrTermMul mono coeff rightTail)))
        (MrTree.mulOp (mrTermToTree mono coeff) (MrTree.addOp (mrTermToTree innerMono innerCoeff)
          (mrCombOfNF rightTail)))
      exact ((mrCombInsertTerm (csrMonoMul mono innerMono) (coeff * innerCoeff) (csrTermMul mono coeff rightTail)).trans
          (ModularRingTreeConv.addCongr (mrTermToTreeMul mono coeff innerMono innerCoeff) ih)).trans
        (ModularRingTreeConv.symm
          (ModularRingTreeConv.distribLeft (mrTermToTree mono coeff) (mrTermToTree innerMono innerCoeff)
            (mrCombOfNF rightTail)))

theorem mrCombMulConvolve (leftForm rightForm : CsrNF) :
    ModularRingTreeConv (mrCombOfNF (csrMulConvolve leftForm rightForm))
      (MrTree.mulOp (mrCombOfNF leftForm) (mrCombOfNF rightForm)) := by
  induction leftForm with
  | nil => exact (mrConvAnnihilLeft (mrCombOfNF rightForm)).symm
  | cons head leftTail ih =>
      obtain ⟨mono, coeff⟩ := head
      show ModularRingTreeConv (mrCombOfNF (csrMergeAdd (csrTermMul mono coeff rightForm)
          (csrMulConvolve leftTail rightForm)))
        (MrTree.mulOp (MrTree.addOp (mrTermToTree mono coeff) (mrCombOfNF leftTail)) (mrCombOfNF rightForm))
      exact ((mrCombMergeAdd (csrTermMul mono coeff rightForm) (csrMulConvolve leftTail rightForm)).trans
          (ModularRingTreeConv.addCongr (mrCombTermMul mono coeff rightForm) ih)).trans
        (ModularRingTreeConv.symm
          (mrConvDistribRight (mrTermToTree mono coeff) (mrCombOfNF leftTail) (mrCombOfNF rightForm)))

/-- ★ every tree reifies to the rebuild of its ℕ[X] normal form (pre-reduction). -/
theorem mrBaseReifies (tree : MrTree) :
    ModularRingTreeConv tree (mrCombOfNF (mrBaseNormalize tree)) := by
  induction tree with
  | gen colour =>
      show ModularRingTreeConv (MrTree.gen colour) (MrTree.addOp (mrTermToTree [colour] 1) MrTree.zeroOp)
      have hgen : ModularRingTreeConv (MrTree.gen colour) (mrTermToTree [colour] 1) :=
        (ModularRingTreeConv.symm (ModularRingTreeConv.mulOne (MrTree.gen colour))).trans
          (ModularRingTreeConv.symm
            (ModularRingTreeConv.addZero (MrTree.mulOp (MrTree.gen colour) MrTree.oneOp)))
      exact hgen.trans (ModularRingTreeConv.symm (ModularRingTreeConv.addZero (mrTermToTree [colour] 1)))
  | zeroOp => exact ModularRingTreeConv.refl MrTree.zeroOp
  | oneOp =>
      show ModularRingTreeConv MrTree.oneOp (MrTree.addOp (mrTermToTree [] 1) MrTree.zeroOp)
      exact (ModularRingTreeConv.symm (ModularRingTreeConv.addZero MrTree.oneOp)).trans
        (ModularRingTreeConv.symm (ModularRingTreeConv.addZero (mrTermToTree [] 1)))
  | addOp leftTree rightTree ihl ihr =>
      show ModularRingTreeConv (MrTree.addOp leftTree rightTree)
        (mrCombOfNF (csrMergeAdd (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)))
      exact (ModularRingTreeConv.addCongr ihl ihr).trans
        (ModularRingTreeConv.symm (mrCombMergeAdd (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)))
  | mulOp leftTree rightTree ihl ihr =>
      show ModularRingTreeConv (MrTree.mulOp leftTree rightTree)
        (mrCombOfNF (csrMulConvolve (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)))
      exact (ModularRingTreeConv.mulCongr ihl ihr).trans
        (ModularRingTreeConv.symm (mrCombMulConvolve (mrBaseNormalize leftTree) (mrBaseNormalize rightTree)))

/-! ## The modular collapse: `mrModulus · X ≈ 0`, and reduction is a convertibility -/

theorem mrScaleTreeEqMulSum (baseTree : MrTree) : (count : Nat) →
    ModularRingTreeConv (mrScaleTree baseTree count) (MrTree.mulOp baseTree (mrSumOfOnes count))
  | 0 => (ModularRingTreeConv.annihilRight baseTree).symm
  | Nat.succ k => by
      show ModularRingTreeConv (MrTree.addOp baseTree (mrScaleTree baseTree k))
        (MrTree.mulOp baseTree (MrTree.addOp MrTree.oneOp (mrSumOfOnes k)))
      exact (ModularRingTreeConv.addCongr (ModularRingTreeConv.refl baseTree)
          (mrScaleTreeEqMulSum baseTree k)).trans
        ((ModularRingTreeConv.addCongr (ModularRingTreeConv.mulOne baseTree).symm
            (ModularRingTreeConv.refl (MrTree.mulOp baseTree (mrSumOfOnes k)))).trans
          (ModularRingTreeConv.distribLeft baseTree MrTree.oneOp (mrSumOfOnes k)).symm)

/-- ★ characteristic collapse: `mrModulus` copies of any tree are `≈ 0`. -/
theorem mrScaleTreeCharN (baseTree : MrTree) :
    ModularRingTreeConv (mrScaleTree baseTree mrModulus) MrTree.zeroOp :=
  (mrScaleTreeEqMulSum baseTree mrModulus).trans
    ((ModularRingTreeConv.mulCongr (ModularRingTreeConv.refl baseTree) ModularRingTreeConv.nTimesOne).trans
      (ModularRingTreeConv.annihilRight baseTree))

theorem mrScaleMultipleZero (baseTree : MrTree) (multiple : Nat) :
    ModularRingTreeConv (mrScaleTree baseTree (mrModulus * multiple)) MrTree.zeroOp :=
  (mrScaleTreeMulCoeff baseTree mrModulus multiple).trans (mrScaleTreeCharN (mrScaleTree baseTree multiple))

/-- ★ reducing a coefficient mod `n` is a convertibility of the scaled tree. -/
theorem mrScaleReduce (baseTree : MrTree) (coeff : Nat) :
    ModularRingTreeConv (mrScaleTree baseTree coeff)
      (mrScaleTree baseTree (natRemainder coeff mrModulus)) := by
  have hrec : coeff = mrModulus * natQuotient coeff mrModulus + natRemainder coeff mrModulus :=
    natRemainderReconstructs coeff mrModulus
  rw [show mrScaleTree baseTree coeff
        = mrScaleTree baseTree (mrModulus * natQuotient coeff mrModulus + natRemainder coeff mrModulus)
      from congrArg (mrScaleTree baseTree) hrec]
  exact (mrScaleAdd baseTree (mrModulus * natQuotient coeff mrModulus) (natRemainder coeff mrModulus)).trans
    ((ModularRingTreeConv.addCongr (mrScaleMultipleZero baseTree (natQuotient coeff mrModulus))
        (ModularRingTreeConv.refl (mrScaleTree baseTree (natRemainder coeff mrModulus)))).trans
      (mrConvAddZeroLeft (mrScaleTree baseTree (natRemainder coeff mrModulus))))

/-- ★ the rebuild of a normal form is convertible to the rebuild of its reduction. -/
theorem mrReduceReifies : (normalForm : CsrNF) →
    ModularRingTreeConv (mrCombOfNF normalForm) (mrCombOfNF (mrReduce normalForm))
  | [] => ModularRingTreeConv.refl MrTree.zeroOp
  | (mono, coeff) :: rest => by
      have ih := mrReduceReifies rest
      cases hb : Nat.beq (natRemainder coeff mrModulus) 0 with
      | true =>
          rw [mrReduceConsZero mono coeff rest hb]
          show ModularRingTreeConv (MrTree.addOp (mrTermToTree mono coeff) (mrCombOfNF rest))
            (mrCombOfNF (mrReduce rest))
          have hzero : ModularRingTreeConv (mrTermToTree mono coeff) MrTree.zeroOp :=
            (mrScaleReduce (mrMonoToTree mono) coeff).trans (by
              rw [mrBeqZeroEq coeff hb]; exact ModularRingTreeConv.refl MrTree.zeroOp)
          exact (ModularRingTreeConv.addCongr hzero ih).trans (mrConvAddZeroLeft (mrCombOfNF (mrReduce rest)))
      | false =>
          rw [mrReduceConsNonzero mono coeff rest hb]
          show ModularRingTreeConv (MrTree.addOp (mrTermToTree mono coeff) (mrCombOfNF rest))
            (MrTree.addOp (mrTermToTree mono (natRemainder coeff mrModulus)) (mrCombOfNF (mrReduce rest)))
          exact ModularRingTreeConv.addCongr (mrScaleReduce (mrMonoToTree mono) coeff) ih

/-- ★ every tree reifies to the rebuild of its modular normal form. -/
theorem mrTreeReifies (tree : MrTree) :
    ModularRingTreeConv tree (mrCombOfNF (mrNormalize tree)) :=
  (mrBaseReifies tree).trans (mrReduceReifies (mrBaseNormalize tree))

/-- ★ completeness: equal modular normal forms give convertible trees. -/
theorem mrConv_of_normalizeEq {s t : MrTree} (h : mrNormalize s = mrNormalize t) :
    ModularRingTreeConv s t := by
  have hcomb : mrCombOfNF (mrNormalize s) = mrCombOfNF (mrNormalize t) := congrArg mrCombOfNF h
  exact (mrTreeReifies s).trans (hcomb ▸ (mrTreeReifies t).symm)

/-! ## The decision -/

/-- structural equality of modular normal forms. -/
def mrNFEq : CsrNF → CsrNF → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | (m1, c1) :: r1, (m2, c2) :: r2 => (csrNatListEq m1 m2 && Nat.beq c1 c2) && mrNFEq r1 r2
theorem mrNFEqRefl (form : CsrNF) : mrNFEq form form = true := by
  induction form with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨mono, coeff⟩ := head
      show ((csrNatListEq mono mono && Nat.beq coeff coeff) && mrNFEq rest rest) = true
      exact csrAndIntro _ _ (csrAndIntro _ _ (csrNatListEqRefl mono) (csrNatBeqRefl coeff)) ih
theorem mrNFEq_eq (leftForm rightForm : CsrNF) : mrNFEq leftForm rightForm = true → leftForm = rightForm := by
  induction leftForm generalizing rightForm with
  | nil =>
      cases rightForm with
      | nil => intro _; rfl
      | cons head rest => intro h; exact Bool.noConfusion h
  | cons head leftTail ih =>
      obtain ⟨m1, c1⟩ := head
      cases rightForm with
      | nil => intro h; exact Bool.noConfusion h
      | cons head2 rightTail =>
          obtain ⟨m2, c2⟩ := head2
          intro h
          have hpair : (csrNatListEq m1 m2 && Nat.beq c1 c2) = true := csrAndTrueLeft _ _ h
          have hrest : mrNFEq leftTail rightTail = true := csrAndTrueRight _ _ h
          have hm : m1 = m2 := csrNatListEq_eq m1 m2 (csrAndTrueLeft _ _ hpair)
          have hc : c1 = c2 := csrNatEqOfBeq c1 c2 (csrAndTrueRight _ _ hpair)
          rw [hm, hc, ih rightTail hrest]

/-- ★★ the decision procedure. -/
def mrDecideConv (s t : MrTree) : Bool := mrNFEq (mrNormalize s) (mrNormalize t)

/-- ★★ THE DECISION: convertibility ⟺ equal modular normal form. -/
theorem modularRingTreeConv_iff_normalForm (s t : MrTree) :
    ModularRingTreeConv s t ↔ mrDecideConv s t = true := by
  constructor
  · intro conv
    show mrNFEq (mrNormalize s) (mrNormalize t) = true
    rw [mrNormalize_respects conv]; exact mrNFEqRefl (mrNormalize t)
  · intro hdec
    exact mrConv_of_normalizeEq (mrNFEq_eq (mrNormalize s) (mrNormalize t) hdec)

/-- ★ decidability, via the biconditional (no `propext`). -/
instance mrDecidableConv (s t : MrTree) : Decidable (ModularRingTreeConv s t) :=
  if h : mrDecideConv s t = true then
    isTrue ((modularRingTreeConv_iff_normalForm s t).mpr h)
  else
    isFalse (fun conv => h ((modularRingTreeConv_iff_normalForm s t).mp conv))

/-- ★★ the walking free commutative ring over ℤ/6 is DECIDED. -/
def fxWalkingModularRing_hasNormalFormDecision : Bool := true

-- genuineness smokes (mrModulus = 6)
-- `6 · x ≈ 0` (characteristic six) → true
#eval mrDecideConv
  (MrTree.addOp (MrTree.gen 0) (MrTree.addOp (MrTree.gen 0) (MrTree.addOp (MrTree.gen 0)
    (MrTree.addOp (MrTree.gen 0) (MrTree.addOp (MrTree.gen 0) (MrTree.gen 0)))))) MrTree.zeroOp
-- the zero divisor `(1+1)·(1+1+1) = 2·3 ≡ 0` → true
#eval mrDecideConv
  (MrTree.mulOp (MrTree.addOp MrTree.oneOp MrTree.oneOp)
    (MrTree.addOp MrTree.oneOp (MrTree.addOp MrTree.oneOp MrTree.oneOp))) MrTree.zeroOp
-- distributivity `x·(y+z) = x·y + x·z` → true
#eval mrDecideConv (MrTree.mulOp (MrTree.gen 0) (MrTree.addOp (MrTree.gen 1) (MrTree.gen 2)))
  (MrTree.addOp (MrTree.mulOp (MrTree.gen 0) (MrTree.gen 1)) (MrTree.mulOp (MrTree.gen 0) (MrTree.gen 2)))
-- commutativity `x·y = y·x` → true
#eval mrDecideConv (MrTree.mulOp (MrTree.gen 0) (MrTree.gen 1)) (MrTree.mulOp (MrTree.gen 1) (MrTree.gen 0))
-- `x + x ≠ x` (coefficient 2 ≢ 1 mod 6) → false
#eval mrDecideConv (MrTree.addOp (MrTree.gen 0) (MrTree.gen 0)) (MrTree.gen 0)
-- `(1+1+1+1+1+1)·x ≈ 0` (six times x) → true
#eval mrDecideConv
  (MrTree.mulOp (MrTree.addOp MrTree.oneOp (MrTree.addOp MrTree.oneOp (MrTree.addOp MrTree.oneOp
    (MrTree.addOp MrTree.oneOp (MrTree.addOp MrTree.oneOp MrTree.oneOp))))) (MrTree.gen 0)) MrTree.zeroOp
-- `x ≠ y` → false
#eval mrDecideConv (MrTree.gen 0) (MrTree.gen 1)

end FX1Poly.Polygraph
