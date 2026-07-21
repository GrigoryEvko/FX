import FX1Poly.ComputerAlgebra.Register.VirtualField

/-! # VirtualFieldReassembly — numeric correctness of a reassembled virtual field

`extractVirtual` (from `VirtualField`) is the LSB-first `bitVecConcat` fold of a
`virtual` field (fx_design.md §18.1).  Its numeric law: read as a natural, the
reassembled vector places field `k`'s slice at the bit offset equal to the sum of
all prior widths.  `bitVecConcatToNat` is the `.toNat` law for LSB-first
concatenation; `extractVirtualToNat` equates the reassembled `.toNat` with the
weighted fold `virtualReassembledSum`; `virtualReassembledSum_recoversHeadSlice`
recovers the head slice.

`Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-- `(bitVecConcat low high).toNat = low.toNat + high.toNat * 2^lowWidth`: `high`
sits scaled past `low`'s `lowWidth` bits, and the sum stays below the combined
width, so the reducer's outer `mod` is the identity. -/
theorem bitVecConcatToNat {lowWidth highWidth : Nat}
    (low : BitVec lowWidth) (high : BitVec highWidth) :
    (bitVecConcat low high).toNat = low.toNat + high.toNat * 2 ^ lowWidth :=
  let concatArg := low.toNat + high.toNat * 2 ^ lowWidth
  let sumBelowCombined : concatArg < 2 ^ (lowWidth + highWidth) :=
    Nat.lt_of_lt_of_le (natLowPlusScaledLt low.isLt high.isLt)
      (Nat.le_of_eq (twoPowAdd 2 lowWidth highWidth).symm)
  (bitVecOfNatModToNat (width := lowWidth + highWidth) concatArg).trans
    (natRemainderOfLt sumBelowCombined)

/-- The LSB-first weighted fold `extractVirtual` computes as a natural: head slice in
the low bits, each tail contribution scaled past the head's `spec.width` bits. -/
def virtualReassembledSum {n : Nat} (value : BitVec n) : List FieldSpec → Nat
  | []          => 0
  | spec :: rest =>
      (extractFieldSlice value spec.offset spec.width).toNat
        + virtualReassembledSum value rest * 2 ^ spec.width

/-- Reassembly correctness: read as a natural, the reassembled virtual field equals
the weighted fold `virtualReassembledSum`. -/
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

/-- The low `spec.width` bits of the reassembled sum recover the head slice: the
remainder by `2^spec.width` discards the tail, via `natRemainderUnique` from the
slice's bound. -/
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
