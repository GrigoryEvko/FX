import FX1Poly.ComputerAlgebra.Register.VirtualField

/-! # VirtualFieldReassembly — the numeric correctness of a reassembled virtual field

`VirtualField` builds a `virtual` field (fx_design.md §18.1) as the LSB-first
`bitVecConcat` fold `extractVirtual`, and ties off the *range* semantics
(`isDisjointSpec_ne`).  What it does NOT prove is the *numeric* reassembly law: that
the reassembled vector, read as a natural, places field `k`'s slice at the bit
offset given by the sum of all prior widths.  That is the honest §18.1 statement,
and it is exactly the gap this file closes.

Two facts, riding the shipped modular-arithmetic corpus that `FieldLayout` already
uses at much greater depth:

* `bitVecConcatToNat` — the missing `.toNat` law for LSB-first concatenation.
  `bitVecConcat low high` is definitionally `bitVecOfNatMod (low.toNat + high.toNat *
  2^lowWidth)` at width `lowWidth + highWidth`; the outer `mod 2^(lowWidth+highWidth)`
  drops because `natLowPlusScaledLt low.isLt high.isLt` bounds the concatenated
  natural below `2^lowWidth * 2^highWidth = 2^(lowWidth+highWidth)` (`twoPowAdd`).

* `extractVirtualToNat` — structural induction on the spec list: the reassembled
  vector's `.toNat` equals the LSB-first weighted fold `virtualReassembledSum`.  The
  base case is `bitVecZeroToNat`; the cons case is one `bitVecConcatToNat` (lowWidth
  = the head width) then the induction hypothesis.

The corollary `virtualReassembledSum_recoversHeadSlice` reads the low head-width bits
back to slice 0, mirroring `FieldLayout`'s `extractField_insertField_same` remainder
step (`natRemainderUnique`).

`Init`-only, structural (no well-founded recursion), zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The `.toNat` law for LSB-first concatenation -/

/-- `(bitVecConcat low high).toNat = low.toNat + high.toNat * 2^lowWidth`: LSB-first
concatenation places `high` scaled past `low`'s `lowWidth` bits, and the sum never
overflows the combined width, so the reducer's `mod 2^(lowWidth+highWidth)` is the
identity.  Pure `.toNat` `Eq` — no wildcard match, no propext. -/
theorem bitVecConcatToNat {lowWidth highWidth : Nat}
    (low : BitVec lowWidth) (high : BitVec highWidth) :
    (bitVecConcat low high).toNat = low.toNat + high.toNat * 2 ^ lowWidth :=
  let concatArg := low.toNat + high.toNat * 2 ^ lowWidth
  let sumBelowCombined : concatArg < 2 ^ (lowWidth + highWidth) :=
    Nat.lt_of_lt_of_le (natLowPlusScaledLt low.isLt high.isLt)
      (Nat.le_of_eq (twoPowAdd 2 lowWidth highWidth).symm)
  (bitVecOfNatModToNat (width := lowWidth + highWidth) concatArg).trans
    (natRemainderOfLt sumBelowCombined)

/-! ## The reassembled-sum specification and its correctness -/

/-- The LSB-first weighted fold that `extractVirtual` computes as a natural: the head
slice sits in the low bits, and each tail contribution is scaled past the head's
`spec.width` bits.  This is the numeric §18.1 virtual-field value. -/
def virtualReassembledSum {n : Nat} (value : BitVec n) : List FieldSpec → Nat
  | []          => 0
  | spec :: rest =>
      (extractFieldSlice value spec.offset spec.width).toNat
        + virtualReassembledSum value rest * 2 ^ spec.width

/-- **Reassembly correctness**: reading the reassembled virtual field as a natural
yields exactly the LSB-first weighted fold — field `k`'s slice occupies the bit
offset equal to the sum of all prior field widths.  Structural induction on the spec
list: base is `bitVecZeroToNat`, cons is `bitVecConcatToNat` (head width) then the IH. -/
theorem extractVirtualToNat {n : Nat} (value : BitVec n) :
    (specs : List FieldSpec) →
      (extractVirtual value specs).toNat = virtualReassembledSum value specs
  | []          => bitVecZeroToNat
  | spec :: rest =>
      (bitVecConcatToNat (extractFieldSlice value spec.offset spec.width)
          (extractVirtual value rest)).trans
        (congrArg
          (fun tailNat =>
            (extractFieldSlice value spec.offset spec.width).toNat + tailNat * 2 ^ spec.width)
          (extractVirtualToNat value rest))

/-! ## Low-bits corollary -/

/-- The low `spec.width` bits of the reassembled sum read back the head slice: the
Euclidean remainder by `2^spec.width` discards the (multiple-of-`2^spec.width`) tail
and returns slice 0.  Pinned by `natRemainderUnique` from the slice's own bound. -/
theorem virtualReassembledSum_recoversHeadSlice {n : Nat} (value : BitVec n)
    (spec : FieldSpec) (rest : List FieldSpec) :
    natRemainder (virtualReassembledSum value (spec :: rest)) (2 ^ spec.width)
      = (extractFieldSlice value spec.offset spec.width).toNat :=
  let headSlice := (extractFieldSlice value spec.offset spec.width).toNat
  let tailSum := virtualReassembledSum value rest
  natRemainderUnique (extractFieldSlice value spec.offset spec.width).isLt
    ((Nat.add_comm headSlice (tailSum * 2 ^ spec.width)).trans
      (congrArg (· + headSlice) (Nat.mul_comm tailSum (2 ^ spec.width))))

end FX1Poly.ComputerAlgebra
