import FX1Poly.ComputerAlgebra.Register.FieldLayout

/-! # VirtualField — reassembled virtual fields and decidable field non-overlap

The §18.1 / §18.4 layer on top of `FieldLayout`.  A `virtual` field (fx_design.md
§18.1) reassembles scattered bit-windows into one contiguous value; here that is a
LSB-first `bitVecConcat` fold over a list of `FieldSpec`s.  Field non-overlap
(§18.4 cross-field dependencies, and the "no overlapping patterns" check of §18.2)
is a decidable structural `Bool` fold — the decision IS the Bool, so there is no
`Decidable`-of-`Iff` bridge and no propext risk.

The honest tie-off `isDisjointSpec_ne` proves that a `true` disjointness decision
witnesses genuinely disjoint bit-index sets — pure `Nat` order reasoning, no
`BitVec` reasoning at all.

`Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Width-explicit field slice -/

/-- Read the `width`-bit window at `offset` from `value`, target width stated
directly (unlike `extractField`, which reads its width from a `FieldSpec`).  Same
arithmetic form: shift down by `offset` (quotient by `2^offset`), keep `width` low
bits (`mod 2^width`). -/
def extractFieldSlice {n : Nat} (value : BitVec n) (offset width : Nat) : BitVec width :=
  bitVecOfNatMod (natQuotient value.toNat (2 ^ offset))

/-! ## Virtual field = LSB-first concat fold -/

/-- Total width of a field list — the summed window widths, reducing definitionally
so the concat fold below type-checks with no cast. -/
def totalFieldWidth : List FieldSpec → Nat
  | []          => 0
  | spec :: rest => spec.width + totalFieldWidth rest

/-- Reassemble a virtual field: concatenate each spec's slice LSB-first, the
list-head occupying the low bits.  Type-checks against `totalFieldWidth` by the
structural reduction — no dependent-cast bookkeeping. -/
def extractVirtual {n : Nat} (value : BitVec n) :
    (specs : List FieldSpec) → BitVec (totalFieldWidth specs)
  | []          => bitVecZero
  | spec :: rest =>
      bitVecConcat (extractFieldSlice value spec.offset spec.width) (extractVirtual value rest)

/-! ## Decidable field non-overlap (structural `Bool` fold) -/

/-- Two fields occupy disjoint half-open ranges `[offset, offset+width)`: one ends
at or before the other begins. -/
def isDisjointSpec (a b : FieldSpec) : Bool :=
  Nat.ble (a.offset + a.width) b.offset || Nat.ble (b.offset + b.width) a.offset

/-- `spec` is disjoint from every field in the list. -/
def isDisjointFromAll (spec : FieldSpec) : List FieldSpec → Bool
  | []           => true
  | other :: rest => isDisjointSpec spec other && isDisjointFromAll spec rest

/-- No two fields in the list overlap (each head is disjoint from its tail). -/
def isNonOverlapping : List FieldSpec → Bool
  | []          => true
  | spec :: rest => isDisjointFromAll spec rest && isNonOverlapping rest

/-- The `Prop` face — decidable by construction since it is a `Bool` equality. -/
def IsNonOverlapping (specs : List FieldSpec) : Prop := isNonOverlapping specs = true

instance (specs : List FieldSpec) : Decidable (IsNonOverlapping specs) :=
  inferInstanceAs (Decidable (isNonOverlapping specs = true))

/-! ## Range-semantics tie-off -/

/-- Boolean disjunction case-split: `(p || q) = true` gives one true disjunct. -/
theorem boolOrCases {p q : Bool} (isTrue : (p || q) = true) : p = true ∨ q = true :=
  match p with
  | true  => Or.inl rfl
  | false => Or.inr isTrue

/-- A `true` two-field disjointness decision witnesses genuinely disjoint bit-index
sets: no in-range bit of `a` shares an absolute position with any in-range bit of
`b`.  Pure `Nat` order — the honest "the predicate means what it says". -/
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
