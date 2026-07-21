import FX1Poly.ComputerAlgebra.FixedWidth.OverflowArithmetic

/-! # FixedWidth/SaturateMulSemantics — saturating multiplication (dim 16)

The saturate-mode correctness theorems for `*` on `saturateMulUnsigned` (defined
in `OverflowArithmetic`), matching the saturate-`add` cluster there
(`saturateAddInRange` / `saturateAddClamps` / `saturateAddUpperBounded`) with
`+` replaced by `*`: in range the exact reduced product, clamp to `2^n − 1` on
overflow, and the `≤ 2^n − 1` upper bound on both branches.  The proofs reuse the
saturate-`add` toolkit: the `Nat.blt`/`cond` order bridges, the modulus reader
(`bitVecOfNatModToNat`, `natRemainderOfLt`), and the clamp constant
`bitVecMaxUnsigned`.

`Init`-only, structural, genuine-`Eq`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-- In range, saturate mul is the exact product. -/
theorem saturateMulInRange {width : Nat} (left right : BitVec width)
    (fits : left.toNat * right.toNat < 2 ^ width) :
    (saturateMulUnsigned left right).toNat = left.toNat * right.toNat :=
  (congrArg
      (fun flag =>
        (cond flag (bitVecOfNatMod (left.toNat * right.toNat)) bitVecMaxUnsigned).toNat)
      (natBltEqTrueOfLt fits)).trans
    ((bitVecOfNatModToNat (left.toNat * right.toNat)).trans (natRemainderOfLt fits))

/-- On overflow, saturate mul clamps to `2^n − 1`. -/
theorem saturateMulClamps {width : Nat} (left right : BitVec width)
    (overflows : 2 ^ width ≤ left.toNat * right.toNat) :
    (saturateMulUnsigned left right).toNat = 2 ^ width - 1 :=
  (congrArg
      (fun flag =>
        (cond flag (bitVecOfNatMod (left.toNat * right.toNat)) bitVecMaxUnsigned).toNat)
      (natBltEqFalseOfLe overflows)).trans
    bitVecMaxUnsignedToNat

/-- Saturate mul is upper-bounded by `2^n − 1` on both branches (clamp
correctness). -/
theorem saturateMulUpperBounded {width : Nat} (left right : BitVec width) :
    (saturateMulUnsigned left right).toNat ≤ 2 ^ width - 1 :=
  match Nat.lt_or_ge (left.toNat * right.toNat) (2 ^ width) with
  | .inl fits =>
      Nat.le_trans (Nat.le_of_eq (saturateMulInRange left right fits))
        (natLeSubOneOfLt fits)
  | .inr overflows => Nat.le_of_eq (saturateMulClamps left right overflows)

end FX1Poly.ComputerAlgebra
