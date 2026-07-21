import FX1Poly.ComputerAlgebra.Register.FieldLayout

/-! # VirtualField — reassembled virtual fields and decidable field non-overlap

The §18.1/§18.4 layer over `FieldLayout`.  A `virtual` field (fx_design.md §18.1)
reassembles scattered bit-windows into one contiguous value: a LSB-first
`bitVecConcat` fold over a list of `FieldSpec`s.  Field non-overlap (§18.4; the
§18.2 non-overlapping-patterns check) is a decidable structural `Bool` fold,
avoiding a `Decidable`-of-`Iff` bridge.  `isDisjointSpec_ne` ties a `true` decision
to genuinely disjoint bit-index sets by `Nat` order alone.

`Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Width-explicit field slice and LSB-first concat fold -/

/-- Read the `width`-bit window at `offset`: shift down by `offset` (quotient by
`2^offset`), keep the low `width` bits (`mod 2^width`).  Width is stated directly
rather than read from a `FieldSpec`. -/
def extractFieldSlice {n : Nat} (value : BitVec n) (offset width : Nat) : BitVec width :=
  bitVecOfNatMod (natQuotient value.toNat (2 ^ offset))

/-- Summed window widths of a field list; reduces definitionally so `extractVirtual`
type-checks without a cast. -/
def totalFieldWidth : List FieldSpec → Nat
  | []          => 0
  | spec :: rest => spec.width + totalFieldWidth rest

/-- Reassemble a virtual field: concatenate each spec's slice LSB-first, the
list-head occupying the low bits. -/
def extractVirtual {n : Nat} (value : BitVec n) :
    (specs : List FieldSpec) → BitVec (totalFieldWidth specs)
  | []          => bitVecZero
  | spec :: rest =>
      bitVecConcat (extractFieldSlice value spec.offset spec.width) (extractVirtual value rest)

/-- Disjoint half-open ranges `[offset, offset+width)`: one ends at or before the
other begins. -/
def isDisjointSpec (a b : FieldSpec) : Bool :=
  Nat.ble (a.offset + a.width) b.offset || Nat.ble (b.offset + b.width) a.offset

/-- `spec` is disjoint from every field in the list. -/
def isDisjointFromAll (spec : FieldSpec) : List FieldSpec → Bool
  | []           => true
  | other :: rest => isDisjointSpec spec other && isDisjointFromAll spec rest

/-- No two fields overlap: each head is disjoint from its tail. -/
def isNonOverlapping : List FieldSpec → Bool
  | []          => true
  | spec :: rest => isDisjointFromAll spec rest && isNonOverlapping rest

/-- The `Prop` face of `isNonOverlapping`. -/
def IsNonOverlapping (specs : List FieldSpec) : Prop := isNonOverlapping specs = true

instance (specs : List FieldSpec) : Decidable (IsNonOverlapping specs) :=
  inferInstanceAs (Decidable (isNonOverlapping specs = true))

/-- Boolean disjunction case-split: `(p || q) = true` gives one true disjunct. -/
theorem boolOrCases {p q : Bool} (isTrue : (p || q) = true) : p = true ∨ q = true :=
  match p with
  | true  => Or.inl rfl
  | false => Or.inr isTrue

/-- A `true` disjointness decision witnesses disjoint bit-index sets: no in-range
bit of `a` shares an absolute position with an in-range bit of `b`. -/
theorem isDisjointSpec_ne {a b : FieldSpec} (isDisjoint : isDisjointSpec a b = true)
    (indexA indexB : Nat) (indexABound : indexA < a.width) (indexBBound : indexB < b.width) :
    a.offset + indexA ≠ b.offset + indexB :=
  match boolOrCases isDisjoint with
  | Or.inl aBelowB =>
      let aTopLeB : a.offset + a.width ≤ b.offset := Nat.le_of_ble_eq_true aBelowB
      let strict : a.offset + indexA < b.offset + indexB :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left indexABound a.offset)
          (Nat.le_trans aTopLeB (Nat.le_add_right b.offset indexB))
      Nat.ne_of_lt strict
  | Or.inr bBelowA =>
      let bTopLeA : b.offset + b.width ≤ a.offset := Nat.le_of_ble_eq_true bBelowA
      let strict : b.offset + indexB < a.offset + indexA :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left indexBBound b.offset)
          (Nat.le_trans bTopLeA (Nat.le_add_right a.offset indexA))
      (Nat.ne_of_lt strict).symm

end FX1Poly.ComputerAlgebra
