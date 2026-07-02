import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity

/-! # FX1Poly/ComputerAlgebra/Number/IntOrderCore — the order core via additive witnesses
    (FLOAT-1 brick 7)

Init's entire symbolic Int order corpus (`le_refl`/`le_trans`/`le_antisymm`/...) is
propext-dirty; this module hand-rolls the core.  The technique is the ADDITIVE WITNESS:

  * `leftValue ≤ rightValue` unfolds DEFINITIONALLY to
    `Int.NonNeg (rightValue + -leftValue)` (probed 2026-07-02, `rfl`), and `Int.NonNeg`
    is a single-constructor inductive, so destruction is one clean match
    (`intNonNegDest`).
  * `intLessEqualIntro`/`intLessEqualDest` convert between `≤` and the witness form
    `rightValue = leftValue + Int.ofNat difference` through the brick-1..3 additive-group
    kit — after which every order law is WITNESS ARITHMETIC: reflexivity is the witness
    `0`, transitivity ADDS witnesses (`ofNat` addition is definitional), antisymmetry
    cancels them (`intAddLeftCancel` + `natAddEqZeroLeft`).
  * `<` needs no separate treatment: `leftValue < rightValue` IS
    `leftValue + 1 ≤ rightValue` definitionally (`intLessThanAsSuccLessEqual`).

## Zero-axiom

Single-constructor match on `Int.NonNeg`, `congrArg`/`Eq.trans` witness arithmetic over
the brick-1..3 kit, one `Eq.rec` transport (`▸`) in each `OfEq` rewriting helper.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/Number/IntOrderCore.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The witness interface -/

/-- `Int.NonNeg` destruction — single-constructor match, the value IS an `ofNat`. -/
theorem intNonNegDest : ∀ {value : Int}, Int.NonNeg value →
    ∃ witness : Nat, value = Int.ofNat witness
  | _, .mk witness => ⟨witness, rfl⟩

/-- Rewrite the right endpoint of a `≤`. -/
theorem intLessEqualOfEqRight {leftValue middleValue rightValue : Int}
    (isLessEqual : leftValue ≤ middleValue) (areEqual : middleValue = rightValue) :
    leftValue ≤ rightValue := areEqual ▸ isLessEqual

/-- Rewrite the left endpoint of a `≤`. -/
theorem intLessEqualOfEqLeft {leftValue middleValue rightValue : Int}
    (areEqual : leftValue = middleValue) (isLessEqual : middleValue ≤ rightValue) :
    leftValue ≤ rightValue := areEqual.symm ▸ isLessEqual

/-- **Witness introduction**: adding an `ofNat` moves up.  The `≤` unfolds to
`NonNeg ((base + ofNat difference) + -base)`, which the additive-group kit collapses to
`NonNeg (ofNat difference)` — the constructor. -/
theorem intLessEqualIntro (base : Int) (difference : Nat) :
    base ≤ base + Int.ofNat difference :=
  let cancelEquation : (base + Int.ofNat difference) + -base = Int.ofNat difference :=
    (congrArg (· + -base) (intAddComm base (Int.ofNat difference))).trans
      ((intAddAssoc (Int.ofNat difference) base (-base)).trans
        ((congrArg (Int.ofNat difference + ·) (intAddRightNeg base)).trans
          (intAddZero (Int.ofNat difference))))
  show Int.NonNeg ((base + Int.ofNat difference) + -base) from
    cancelEquation.symm ▸ Int.NonNeg.mk difference

/-- **Witness destruction**: `leftValue ≤ rightValue` yields the additive witness
`rightValue = leftValue + ofNat difference`, recovered from the `NonNeg` payload by
adding `leftValue` back on the right. -/
theorem intLessEqualDest {leftValue rightValue : Int} (isLessEqual : leftValue ≤ rightValue) :
    ∃ difference : Nat, rightValue = leftValue + Int.ofNat difference :=
  match intNonNegDest (show Int.NonNeg (rightValue + -leftValue) from isLessEqual) with
  | ⟨difference, differenceEquation⟩ =>
      ⟨difference,
        (intAddZero rightValue).symm.trans
          ((congrArg (rightValue + ·) (intAddLeftNeg leftValue).symm).trans
            ((intAddAssoc rightValue (-leftValue) leftValue).symm.trans
              ((congrArg (· + leftValue) differenceEquation).trans
                (intAddComm (Int.ofNat difference) leftValue))))⟩

/-- `<` is succ-`≤` DEFINITIONALLY — the pin that lets every `<` fact reuse the `≤` kit
(Init's `Int.lt_iff_add_one_le` is clean but this is stronger: propositional identity
by `rfl`). -/
theorem intLessThanAsSuccLessEqual (leftValue rightValue : Int) :
    (leftValue < rightValue) = (leftValue + 1 ≤ rightValue) := rfl

/-! ## The order laws as witness arithmetic -/

/-- Reflexivity — the witness is `0` (Init's `Int.le_refl` is propext-dirty). -/
theorem intLessEqualRefl (value : Int) : value ≤ value :=
  intLessEqualOfEqRight (intLessEqualIntro value 0) (intAddZero value)

/-- Transitivity — witnesses ADD (`ofNat` addition is definitional on the constructor)
(Init's `Int.le_trans` is propext-dirty). -/
theorem intLessEqualTrans {lowValue middleValue highValue : Int}
    (isLowMiddle : lowValue ≤ middleValue) (isMiddleHigh : middleValue ≤ highValue) :
    lowValue ≤ highValue :=
  match intLessEqualDest isLowMiddle, intLessEqualDest isMiddleHigh with
  | ⟨firstDifference, firstEquation⟩, ⟨secondDifference, secondEquation⟩ =>
      intLessEqualOfEqRight
        (intLessEqualIntro lowValue (firstDifference + secondDifference))
        (((intAddAssoc lowValue (Int.ofNat firstDifference)
              (Int.ofNat secondDifference)).symm.trans
            (congrArg (· + Int.ofNat secondDifference) firstEquation.symm)).trans
          secondEquation.symm)

/-- A Nat sum vanishes only if its left summand does — the right-summand split is
definitional (`left + 0` reduces to `left`; `left + (k+1)` reduces to a `succ`, refuted
by `noConfusion`). -/
theorem natAddEqZeroLeft : ∀ {leftValue rightValue : Nat},
    leftValue + rightValue = 0 → leftValue = 0
  | _, 0, sumEquation => sumEquation
  | _, _ + 1, sumEquation => Nat.noConfusion sumEquation

/-- Left cancellation for addition — add `-base` on the left through the additive-group
kit (Init's `Int.add_left_cancel` is propext-dirty). -/
theorem intAddLeftCancel {base leftAddend rightAddend : Int}
    (sumsAreEqual : base + leftAddend = base + rightAddend) : leftAddend = rightAddend :=
  (intZeroAdd leftAddend).symm.trans
    ((congrArg (· + leftAddend) (intAddLeftNeg base).symm).trans
      ((intAddAssoc (-base) base leftAddend).trans
        ((congrArg (-base + ·) sumsAreEqual).trans
          ((intAddAssoc (-base) base rightAddend).symm.trans
            ((congrArg (· + rightAddend) (intAddLeftNeg base)).trans
              (intZeroAdd rightAddend))))))

/-- Antisymmetry — the two witnesses cancel: their `ofNat` sum equals `0` by left
cancellation, so both are zero by `natAddEqZeroLeft` (Init's `Int.le_antisymm` is
propext-dirty). -/
theorem intLessEqualAntisymm {leftValue rightValue : Int}
    (isForward : leftValue ≤ rightValue) (isBackward : rightValue ≤ leftValue) :
    leftValue = rightValue :=
  match intLessEqualDest isForward, intLessEqualDest isBackward with
  | ⟨forwardDifference, forwardEquation⟩, ⟨backwardDifference, backwardEquation⟩ =>
      let selfEquation : leftValue =
          leftValue + (Int.ofNat forwardDifference + Int.ofNat backwardDifference) :=
        backwardEquation.trans
          ((congrArg (· + Int.ofNat backwardDifference) forwardEquation).trans
            (intAddAssoc leftValue (Int.ofNat forwardDifference)
              (Int.ofNat backwardDifference)))
      let witnessSumIsZero : Int.ofNat 0 = Int.ofNat (forwardDifference + backwardDifference) :=
        intAddLeftCancel ((intAddZero leftValue).trans selfEquation)
      let forwardIsZero : forwardDifference = 0 :=
        natAddEqZeroLeft (Int.ofNat.inj witnessSumIsZero).symm
      (forwardEquation.trans
        ((congrArg (fun difference => leftValue + Int.ofNat difference) forwardIsZero).trans
          (intAddZero leftValue))).symm

end FX1Poly.ComputerAlgebra
