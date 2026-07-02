import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat

/-! # FX1Poly/ComputerAlgebra/Number/IntAddAssociativity — the mixed-sign add bridges + assoc
    (FLOAT-1 brick 3)

Init's `Int.add_assoc` is propext-dirty; this module hand-rolls it.  The route is the classic
one, rebuilt on the brick-2 `subNatNat` kit:

  * The four MIXED-SIGN ADD BRIDGES push an `ofNat` / `negSucc` summand into a `subNatNat`:
    `intOfNatAddSubNatNat`, `intSubNatNatAddOfNat`, `intNegSuccAddSubNatNat`,
    `intSubNatNatAddNegSucc`.  The two primaries are double structural recursions whose
    step case is exactly `intSubNatNatSuccSucc`; the other two are one-line corollaries
    through `intAddComm`.
  * `intAddAssoc` is then an eight-way constructor bash: every mixed case collapses to a
    bridge (both sides of the association land on the SAME `subNatNat` call), and the two
    pure-sign cases are `congrArg` over `Nat.add_assoc`.

## Zero-axiom

Structural recursion + `congrArg`/`Eq.trans` chains over clean Nat lemmas (`Nat.add_comm`,
`Nat.add_assoc`, `Nat.succ_add`, `Nat.zero_add`) and the brick-2 kit.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/IntAddAssociativity.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-- **Bridge 1**: an `ofNat` head summand enters the left side of a `subNatNat`.  Double
structural recursion; the `(0, right+1)` base is definitional and the step is the
`intSubNatNatSuccSucc` workhorse on both sides. -/
theorem intOfNatAddSubNatNat (headValue : Nat) : ∀ leftValue rightValue : Nat,
    Int.ofNat headValue + Int.subNatNat leftValue rightValue =
      Int.subNatNat (headValue + leftValue) rightValue
  | leftValue, 0 =>
      (congrArg (Int.ofNat headValue + ·) (intSubNatNatZeroRight leftValue)).trans
        (intSubNatNatZeroRight (headValue + leftValue)).symm
  | 0, _ + 1 => rfl
  | leftValue + 1, rightValue + 1 =>
      (congrArg (Int.ofNat headValue + ·) (intSubNatNatSuccSucc leftValue rightValue)).trans
        ((intOfNatAddSubNatNat headValue leftValue rightValue).trans
          (intSubNatNatSuccSucc (headValue + leftValue) rightValue).symm)

/-- **Bridge 2**: an `ofNat` tail summand enters the left side of a `subNatNat` — a
corollary of bridge 1 through `intAddComm`. -/
theorem intSubNatNatAddOfNat (leftValue rightValue tailValue : Nat) :
    Int.subNatNat leftValue rightValue + Int.ofNat tailValue =
      Int.subNatNat (leftValue + tailValue) rightValue :=
  (intAddComm (Int.subNatNat leftValue rightValue) (Int.ofNat tailValue)).trans
    ((intOfNatAddSubNatNat tailValue leftValue rightValue).trans
      (congrArg (Int.subNatNat · rightValue) (Nat.add_comm tailValue leftValue)))

/-- **Bridge 3**: a `negSucc` head summand enters the right side of a `subNatNat`.  Same
double-recursion shape as bridge 1, with `Nat.succ_add` shuffles in the negative bases. -/
theorem intNegSuccAddSubNatNat (headPredecessor : Nat) : ∀ leftValue rightValue : Nat,
    Int.negSucc headPredecessor + Int.subNatNat leftValue rightValue =
      Int.subNatNat leftValue (rightValue + (headPredecessor + 1))
  | leftValue, 0 =>
      (congrArg (Int.negSucc headPredecessor + ·) (intSubNatNatZeroRight leftValue)).trans
        (congrArg (Int.subNatNat leftValue) (Nat.zero_add (headPredecessor + 1))).symm
  | 0, rightValue + 1 =>
      congrArg Int.negSucc
        ((congrArg (· + 1) (Nat.add_comm headPredecessor rightValue)).trans
          (Nat.succ_add rightValue headPredecessor).symm)
  | leftValue + 1, rightValue + 1 =>
      (congrArg (Int.negSucc headPredecessor + ·) (intSubNatNatSuccSucc leftValue rightValue)).trans
        ((intNegSuccAddSubNatNat headPredecessor leftValue rightValue).trans
          ((intSubNatNatSuccSucc leftValue (rightValue + (headPredecessor + 1))).symm.trans
            (congrArg (Int.subNatNat (leftValue + 1))
              (congrArg Nat.succ (Nat.succ_add rightValue headPredecessor)).symm)))

/-- **Bridge 4**: a `negSucc` tail summand enters the right side of a `subNatNat` — a
corollary of bridge 3 through `intAddComm` (both land on the SAME right-hand side). -/
theorem intSubNatNatAddNegSucc (leftValue rightValue tailPredecessor : Nat) :
    Int.subNatNat leftValue rightValue + Int.negSucc tailPredecessor =
      Int.subNatNat leftValue (rightValue + (tailPredecessor + 1)) :=
  (intAddComm (Int.subNatNat leftValue rightValue) (Int.negSucc tailPredecessor)).trans
    (intNegSuccAddSubNatNat tailPredecessor leftValue rightValue)

/-- **Addition associates** (Init's `Int.add_assoc` is propext-dirty).  Eight-way
constructor bash: the pure-sign arms are `congrArg` over `Nat.add_assoc`; every mixed arm
collapses through the bridges to a single shared `subNatNat` call, with at most a
`Nat.succ_add`/`Nat.add_comm` shuffle in the second argument. -/
theorem intAddAssoc : ∀ firstSummand secondSummand thirdSummand : Int,
    firstSummand + secondSummand + thirdSummand =
      firstSummand + (secondSummand + thirdSummand)
  | .ofNat firstNat, .ofNat secondNat, .ofNat thirdNat =>
      congrArg Int.ofNat (Nat.add_assoc firstNat secondNat thirdNat)
  | .ofNat firstNat, .ofNat secondNat, .negSucc thirdPredecessor =>
      (intOfNatAddSubNatNat firstNat secondNat (thirdPredecessor + 1)).symm
  | .ofNat firstNat, .negSucc secondPredecessor, .ofNat thirdNat =>
      (intSubNatNatAddOfNat firstNat (secondPredecessor + 1) thirdNat).trans
        (intOfNatAddSubNatNat firstNat thirdNat (secondPredecessor + 1)).symm
  | .ofNat firstNat, .negSucc secondPredecessor, .negSucc thirdPredecessor =>
      (intSubNatNatAddNegSucc firstNat (secondPredecessor + 1) thirdPredecessor).trans
        (congrArg (Int.subNatNat firstNat)
          (congrArg Nat.succ (Nat.succ_add secondPredecessor thirdPredecessor)))
  | .negSucc firstPredecessor, .ofNat secondNat, .ofNat thirdNat =>
      intSubNatNatAddOfNat secondNat (firstPredecessor + 1) thirdNat
  | .negSucc firstPredecessor, .ofNat secondNat, .negSucc thirdPredecessor =>
      (intSubNatNatAddNegSucc secondNat (firstPredecessor + 1) thirdPredecessor).trans
        ((congrArg (Int.subNatNat secondNat)
            (Nat.add_comm (firstPredecessor + 1) (thirdPredecessor + 1))).trans
          (intNegSuccAddSubNatNat firstPredecessor secondNat (thirdPredecessor + 1)).symm)
  | .negSucc firstPredecessor, .negSucc secondPredecessor, .ofNat thirdNat =>
      (congrArg (Int.subNatNat thirdNat)
          (congrArg Nat.succ
            ((congrArg (· + 1) (Nat.add_comm firstPredecessor secondPredecessor)).trans
              (Nat.succ_add secondPredecessor firstPredecessor).symm))).trans
        (intNegSuccAddSubNatNat firstPredecessor thirdNat (secondPredecessor + 1)).symm
  | .negSucc firstPredecessor, .negSucc secondPredecessor, .negSucc thirdPredecessor =>
      congrArg Int.negSucc
        (congrArg Nat.succ
          ((Nat.succ_add (firstPredecessor + secondPredecessor) thirdPredecessor).trans
            (congrArg (· + 1)
              (Nat.add_assoc firstPredecessor secondPredecessor thirdPredecessor))))

end FX1Poly.ComputerAlgebra
