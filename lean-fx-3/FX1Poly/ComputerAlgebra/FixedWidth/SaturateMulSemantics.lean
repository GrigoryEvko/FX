import FX1Poly.ComputerAlgebra.FixedWidth.OverflowArithmetic

/-! # FixedWidth/SaturateMulSemantics — saturating multiplication (dim 16)

The one defined-but-uncertified overflow op of `OverflowArithmetic` was
`saturateMulUnsigned` (the saturate mode for `*`): the op exists there, but the
correctness cluster covered only saturate-`add`.  This file supplies the missing
three theorems, transcribing the shipped saturate-`add` cluster (`saturateAddInRange`
/ `saturateAddClamps` / `saturateAddUpperBounded`) verbatim with `+` → `*`, so
saturate now matches wrap and trap: every unsigned op in every mode is certified.

* **in range** — when the true product fits below `2^n`, saturate mul is the exact
  reduced product.
* **clamp** — on overflow it pins to the top value `2^n − 1`.
* **upper bound** — on both branches the result is `≤ 2^n − 1` (clamp correctness).

Reuses only the saturate-`add` cluster's exact axiom-clean toolkit: the
`Nat.blt`/`cond` structural order bridges (`natBltEqTrueOfLt`, `natBltEqFalseOfLe`),
the modulus reader (`bitVecOfNatModToNat`, `natRemainderOfLt`), the clamp constant
(`bitVecMaxUnsigned`, `bitVecMaxUnsignedToNat`), and `natLeSubOneOfLt`.  No
`propext`/`Quot.sound` paths.

`Init`-only, structural, genuine-`Eq`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-- **In range, saturate mul is the exact product.** -/
theorem saturateMulInRange {width : Nat} (left right : BitVec width)
    (fits : left.toNat * right.toNat < 2 ^ width) :
    (saturateMulUnsigned left right).toNat = left.toNat * right.toNat :=
  (congrArg
      (fun flag =>
        (cond flag (bitVecOfNatMod (left.toNat * right.toNat)) bitVecMaxUnsigned).toNat)
      (natBltEqTrueOfLt fits)).trans
    ((bitVecOfNatModToNat (left.toNat * right.toNat)).trans (natRemainderOfLt fits))

/-- **On overflow, saturate mul clamps to `2^n − 1`.** -/
theorem saturateMulClamps {width : Nat} (left right : BitVec width)
    (overflows : 2 ^ width ≤ left.toNat * right.toNat) :
    (saturateMulUnsigned left right).toNat = 2 ^ width - 1 :=
  (congrArg
      (fun flag =>
        (cond flag (bitVecOfNatMod (left.toNat * right.toNat)) bitVecMaxUnsigned).toNat)
      (natBltEqFalseOfLe overflows)).trans
    bitVecMaxUnsignedToNat

/-- **Saturate mul is upper-bounded by `2^n − 1`** on both branches (clamp
correctness). -/
theorem saturateMulUpperBounded {width : Nat} (left right : BitVec width) :
    (saturateMulUnsigned left right).toNat ≤ 2 ^ width - 1 :=
  match Nat.lt_or_ge (left.toNat * right.toNat) (2 ^ width) with
  | .inl fits =>
      Nat.le_trans (Nat.le_of_eq (saturateMulInRange left right fits))
        (natLeSubOneOfLt fits)
  | .inr overflows => Nat.le_of_eq (saturateMulClamps left right overflows)

end FX1Poly.ComputerAlgebra
