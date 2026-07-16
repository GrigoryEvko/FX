import FX1Poly.ComputerAlgebra.Register.VirtualFieldReassembly

/-! # VirtualFieldPositional — every virtual sub-field occupies its own window

`VirtualFieldReassembly` proved that the reassembled virtual value read as a
natural equals the LSB-first weighted fold `virtualReassembledSum`, and recovered
the head field's slice (`virtualReassembledSum_recoversHeadSlice`, slice 0 only).
What it left open is the honest §18.1 statement for EVERY field: that field `k`'s
slice occupies exactly the positional window `[prefixWidth_k, prefixWidth_k +
width_k)` of the reassembled value.  This file closes that gap.

Two hand-rolled structural helpers stand in for `List.take`/`List.drop` (whose
`Init` versions are unaudited for propext, and which appear nowhere in the
zero-axiom CA tree):

* `dropSpecs k specs` — the specs remaining after the first `k`, structural on `k`.
* `prefixFieldWidth k specs` — `totalFieldWidth` of the first `k` specs, i.e. the
  bit offset at which field `k` begins.

The three-theorem cluster, all pure `mod 2^n` / quotient arithmetic on the shipped
`NatModularReduction` + `FieldLayout` corpus:

* `virtualReassembledSum_dropsHeadByQuotient` — the quotient dual of the shipped
  remainder corollary: dividing the head-inclusive sum by `2^headWidth` drops the
  head slice and returns the tail sum (`natQuotientOfDecomp`).
* `virtualReassembledSum_dropsPrefixByQuotient` — iterating that head-drop: dividing
  by `2^prefixFieldWidth k` returns the fold over `dropSpecs k specs`.  Structural
  induction on `k`; the step strips one head block with `natQuotientHighCollapse`
  (`twoPowAdd` splitting `2^(headWidth + restPrefix)`) then the IH.
* `virtualReassembledSum_recoversFieldAt` — the §18.1 capstone: read the
  `2^widthAt_k`-remainder of the `2^prefixFieldWidth_k`-quotient and recover field
  `k`'s slice, for every `k`.  Rewrite the quotient by the previous theorem to
  expose field `k` as the new head, then close with the head-slice corollary.

`Init`-only, structural (no well-founded recursion), zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## `mod 2^0` / `quot by 2^0` degeneracies (divisor `2^0 = 1`) -/

/-- Every remainder by `2^0 = 1` is `0`.  Pinned by uniqueness with quotient the
whole dividend and remainder `0`. -/
theorem natRemainderTwoPowZero (dividend : Nat) : natRemainder dividend (2 ^ 0) = 0 :=
  natRemainderUnique (Nat.two_pow_pos 0)
    ((Nat.add_zero (2 ^ 0 * dividend)).trans
      ((Nat.mul_comm (2 ^ 0) dividend).trans (Nat.mul_one dividend))).symm

/-- Dividing by `2^0 = 1` returns the dividend.  Same decomposition, fed to
`natQuotientOfDecomp`. -/
theorem natQuotientTwoPowZero (dividend : Nat) : natQuotient dividend (2 ^ 0) = dividend :=
  natQuotientOfDecomp (Nat.two_pow_pos 0)
    ((Nat.add_zero (2 ^ 0 * dividend)).trans
      ((Nat.mul_comm (2 ^ 0) dividend).trans (Nat.mul_one dividend))).symm

/-! ## Positional spec accessors (hand-rolled, structural on the index) -/

/-- The specs remaining after dropping the first `k` — the structural
`List.drop` for `FieldSpec`s, avoiding the unaudited `Init` version. -/
def dropSpecs : Nat → List FieldSpec → List FieldSpec
  | 0,         specs         => specs
  | _count + 1, []           => []
  | count + 1,  _spec :: rest => dropSpecs count rest

/-- The summed width of the first `k` fields — the bit offset at which field `k`
begins.  `totalFieldWidth` of the taken prefix, structural on `k`. -/
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

/-! ## Theorem 1 — head-drop by quotient (the dual of `recoversHeadSlice`) -/

/-- Dividing the head-inclusive reassembled sum by `2^headWidth` discards the head
slice and returns the tail sum: the exact quotient dual of
`virtualReassembledSum_recoversHeadSlice`.  Same decomposition `headSlice +
tailSum·2^width` (commuted to `2^width·tailSum + headSlice`), same slice bound
`.isLt`, fed to `natQuotientOfDecomp` in place of `natRemainderUnique`. -/
theorem virtualReassembledSum_dropsHeadByQuotient {n : Nat} (value : BitVec n)
    (spec : FieldSpec) (rest : List FieldSpec) :
    natQuotient (virtualReassembledSum value (spec :: rest)) (2 ^ spec.width)
      = virtualReassembledSum value rest :=
  let headSlice := (extractFieldSlice value spec.offset spec.width).toNat
  let tailSum := virtualReassembledSum value rest
  natQuotientOfDecomp (extractFieldSlice value spec.offset spec.width).isLt
    ((Nat.add_comm headSlice (tailSum * 2 ^ spec.width)).trans
      (congrArg (· + headSlice) (Nat.mul_comm tailSum (2 ^ spec.width))))

/-! ## Theorem 2 — prefix-drop by iterated quotient -/

/-- Dividing the reassembled sum by `2^prefixFieldWidth k specs` returns the fold
over the specs remaining after the first `k`.  Structural induction on `k`: the
base is the `2^0`-quotient identity; the step splits `2^(headWidth + restPrefix)`
by `twoPowAdd`, strips the head block by `natQuotientHighCollapse` (block modulus
`2^headWidth`, low bound the head slice's `.isLt`), then applies the IH. -/
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

/-! ## Head-slice recovery for an arbitrary list (bridges the capstone) -/

/-- The `2^headWidth`-remainder of the reassembled sum recovers the head field's
slice, for ANY list — the empty case reads `0 = 0` through the `2^0`
degeneracy, the cons case is exactly `virtualReassembledSum_recoversHeadSlice`. -/
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

/-! ## Theorem 3 — k-th field positional recovery (the §18.1 capstone) -/

/-- **Positional field-decode law**: for every field `k`, the reassembled virtual
value's slice at the positional window `[prefixFieldWidth k, prefixFieldWidth k +
fieldWidthAt k)` — read as the `2^fieldWidthAt k`-remainder of the
`2^prefixFieldWidth k`-quotient — recovers exactly field `k`'s source slice.
Rewrite the quotient by `virtualReassembledSum_dropsPrefixByQuotient` to expose
field `k` as the new head, then close with `recoversHeadFieldSlice`.  This is the
§18.1 "each virtual sub-field occupies its own contiguous window" law. -/
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
