import FX1Poly.ComputerAlgebra.Register.VirtualFieldReassembly

/-! # VirtualFieldPositional — every virtual sub-field occupies its own window

`VirtualFieldReassembly` equated the reassembled virtual value (as a natural) with
the weighted fold `virtualReassembledSum` and recovered the head slice.  This file
proves the general §18.1 statement: field `k`'s slice occupies the window
`[prefixWidth_k, prefixWidth_k + width_k)` of the reassembled value.

Two structural helpers stand in for `List.take`/`List.drop` (whose `Init` versions
are unaudited for propext): `dropSpecs k`, the specs after the first `k`; and
`prefixFieldWidth k`, the summed width of the first `k` specs — the bit offset at
which field `k` begins.

`virtualReassembledSum_recoversFieldAt` reads the `2^widthAt_k`-remainder of the
`2^prefixWidth_k`-quotient and recovers field `k`'s slice, via the head-drop
quotient `virtualReassembledSum_dropsHeadByQuotient` and its iterate
`virtualReassembledSum_dropsPrefixByQuotient`; pure quotient/`mod 2^n` arithmetic on
`NatModularReduction` and `FieldLayout`.

`Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## `2^0` quotient/remainder degeneracies (divisor `2^0 = 1`) -/

/-- Every remainder by `2^0 = 1` is `0`, by uniqueness with quotient the whole
dividend. -/
theorem natRemainderTwoPowZero (dividend : Nat) : natRemainder dividend (2 ^ 0) = 0 :=
  natRemainderUnique (Nat.two_pow_pos 0)
    ((Nat.add_zero (2 ^ 0 * dividend)).trans
      ((Nat.mul_comm (2 ^ 0) dividend).trans (Nat.mul_one dividend))).symm

/-- Dividing by `2^0 = 1` returns the dividend. -/
theorem natQuotientTwoPowZero (dividend : Nat) : natQuotient dividend (2 ^ 0) = dividend :=
  natQuotientOfDecomp (Nat.two_pow_pos 0)
    ((Nat.add_zero (2 ^ 0 * dividend)).trans
      ((Nat.mul_comm (2 ^ 0) dividend).trans (Nat.mul_one dividend))).symm

/-! ## Positional spec accessors -/

/-- The specs remaining after dropping the first `k`: structural `List.drop` for
`FieldSpec`s. -/
def dropSpecs : Nat → List FieldSpec → List FieldSpec
  | 0,         specs         => specs
  | _count + 1, []           => []
  | count + 1,  _spec :: rest => dropSpecs count rest

/-- The summed width of the first `k` fields: the bit offset at which field `k`
begins. -/
def prefixFieldWidth : Nat → List FieldSpec → Nat
  | 0,         _specs        => 0
  | _count + 1, []           => 0
  | count + 1,  spec :: rest => spec.width + prefixFieldWidth count rest

/-- The head field of a list, or the trivial `⟨0, 0⟩` field when empty. -/
def headSpec : List FieldSpec → FieldSpec
  | []           => ⟨0, 0⟩
  | spec :: _rest => spec

/-- Field `k` of the list — the head remaining after dropping the first `k`. -/
def fieldSpecAt (index : Nat) (specs : List FieldSpec) : FieldSpec :=
  headSpec (dropSpecs index specs)

/-- The width of field `k`. -/
def fieldWidthAt (index : Nat) (specs : List FieldSpec) : Nat :=
  (fieldSpecAt index specs).width

/-- The source bit offset of field `k`. -/
def fieldOffsetAt (index : Nat) (specs : List FieldSpec) : Nat :=
  (fieldSpecAt index specs).offset

/-! ## Head-drop by quotient (dual of `recoversHeadSlice`) -/

/-- Dividing the head-inclusive reassembled sum by `2^spec.width` discards the head
slice and returns the tail sum — the quotient dual of
`virtualReassembledSum_recoversHeadSlice`. -/
theorem virtualReassembledSum_dropsHeadByQuotient {n : Nat} (value : BitVec n)
    (spec : FieldSpec) (rest : List FieldSpec) :
    natQuotient (virtualReassembledSum value (spec :: rest)) (2 ^ spec.width)
      = virtualReassembledSum value rest :=
  let headSlice := (extractFieldSlice value spec.offset spec.width).toNat
  let tailSum := virtualReassembledSum value rest
  natQuotientOfDecomp (extractFieldSlice value spec.offset spec.width).isLt
    ((Nat.add_comm headSlice (tailSum * 2 ^ spec.width)).trans
      (congrArg (· + headSlice) (Nat.mul_comm tailSum (2 ^ spec.width))))

/-! ## Prefix-drop by iterated quotient -/

/-- Dividing the reassembled sum by `2^prefixFieldWidth k specs` returns the fold
over the specs after the first `k`.  Induction on `k`: `twoPowAdd` splits the
divisor, `natQuotientHighCollapse` strips the head block, then the IH. -/
theorem virtualReassembledSum_dropsPrefixByQuotient {n : Nat} (value : BitVec n) :
    (index : Nat) → (specs : List FieldSpec) →
      natQuotient (virtualReassembledSum value specs) (2 ^ prefixFieldWidth index specs)
        = virtualReassembledSum value (dropSpecs index specs)
  | 0,         specs => natQuotientTwoPowZero (virtualReassembledSum value specs)
  | _count + 1, []   => natQuotientTwoPowZero (virtualReassembledSum value [])
  | count + 1,  spec :: rest =>
      let restPrefix := prefixFieldWidth count rest
      let headSlice := (extractFieldSlice value spec.offset spec.width).toNat
      let tailSum := virtualReassembledSum value rest
      let divisorSplit : (2 : Nat) ^ (spec.width + restPrefix) = 2 ^ spec.width * 2 ^ restPrefix :=
        twoPowAdd 2 spec.width restPrefix
      let stripped :
          natQuotient (headSlice + tailSum * 2 ^ spec.width) (2 ^ spec.width * 2 ^ restPrefix)
            = natQuotient tailSum (2 ^ restPrefix) :=
        natQuotientHighCollapse (extractFieldSlice value spec.offset spec.width).isLt
          (Nat.two_pow_pos restPrefix)
      (congrArg (natQuotient (headSlice + tailSum * 2 ^ spec.width) ·) divisorSplit).trans
        (stripped.trans (virtualReassembledSum_dropsPrefixByQuotient value count rest))

/-! ## Head-slice recovery for an arbitrary list -/

/-- The `2^(headSpec).width`-remainder of the reassembled sum recovers the head
field's slice for any list: empty via the `2^0` degeneracy, cons via
`virtualReassembledSum_recoversHeadSlice`. -/
theorem virtualReassembledSum_recoversHeadFieldSlice {n : Nat} (value : BitVec n) :
    (specs : List FieldSpec) →
      natRemainder (virtualReassembledSum value specs) (2 ^ (headSpec specs).width)
        = (extractFieldSlice value (headSpec specs).offset (headSpec specs).width).toNat
  | [] =>
      let headZeroSliceIsZero : (extractFieldSlice value 0 0).toNat = 0 :=
        (bitVecOfNatModToNat (width := 0) (natQuotient value.toNat (2 ^ 0))).trans
          (natRemainderTwoPowZero (natQuotient value.toNat (2 ^ 0)))
      (natRemainderTwoPowZero 0).trans headZeroSliceIsZero.symm
  | spec :: rest => virtualReassembledSum_recoversHeadSlice value spec rest

/-! ## k-th field positional recovery (§18.1 capstone) -/

/-- Positional field-decode law (§18.1, each virtual sub-field occupies its own
contiguous window): for every field `k`, the `2^fieldWidthAt k`-remainder of the
`2^prefixFieldWidth k`-quotient of the reassembled value recovers field `k`'s source
slice.  Rewrite the quotient by `virtualReassembledSum_dropsPrefixByQuotient` to
expose field `k` as the new head, then close with `recoversHeadFieldSlice`. -/
theorem virtualReassembledSum_recoversFieldAt {n : Nat} (value : BitVec n)
    (index : Nat) (specs : List FieldSpec) :
    natRemainder
        (natQuotient (virtualReassembledSum value specs) (2 ^ prefixFieldWidth index specs))
        (2 ^ fieldWidthAt index specs)
      = (extractFieldSlice value (fieldOffsetAt index specs) (fieldWidthAt index specs)).toNat :=
  (congrArg (fun quotient => natRemainder quotient (2 ^ fieldWidthAt index specs))
      (virtualReassembledSum_dropsPrefixByQuotient value index specs)).trans
    (virtualReassembledSum_recoversHeadFieldSlice value (dropSpecs index specs))

end FX1Poly.ComputerAlgebra
