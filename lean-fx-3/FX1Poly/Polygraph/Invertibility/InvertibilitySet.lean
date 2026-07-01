import FX1Poly.Polygraph.Invertibility.WitnessClosure

/-! # FX1Poly/Polygraph/Invertibility/InvertibilitySet
    — Henry–Loubaton invertibility sets (arXiv 2301.11424, Def 4.15) as post-fixed families.

HL23 Def 4.15 / Remark 1.5: an **invertibility set** of an ω-category is a set `W` of cells such that
every cell in `W` has a reverse and unit/counit witnesses that ALSO lie in `W`; the maximal such set
`eq 𝒟` is the set of genuinely invertible cells.  That "every member's reverse + unit + counit are again
members" condition is exactly a post-fixed family (`W ⊆ apply W`) of a witness operator, so this file
reuses the generic `WitnessOperator` machinery: `maximalInvertibilitySet := coinductiveClosure` is `eq
𝒟`, the greatest post-fixed family.

## The abstract cell skeleton (honest simplification)

`CellStructure` models the cellular data an invertibility statement needs — for each cell, a chosen
reverse and chosen unit/counit witness cells — as TOTAL functions (a Skolemized skeleton of Def 4.15's
existentials).  This keeps the file substrate-agnostic and lets the fixpoint characterization be stated
cleanly; the genuine ω-categorical reverse/witness EXISTENCE is not modelled here (it belongs to the
Mode/OmegaCategory substrate).  What is proven is the fixpoint content: invertibility sets ARE the
post-fixed families, and the maximal one is the coinductive closure.

## Zero-axiom verification

Structure projections and the generic `WitnessClosure` lemmas — no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Invertibility/InvertibilitySet.lean`.
-/

namespace FX1Poly.Polygraph.Invertibility

/-- An abstract **cell structure**: a carrier of cells with, for each cell, a chosen reverse cell and
chosen unit/counit witness cells.  The Skolemized skeleton over which invertibility is stated (HL23's
existential reverse/witnesses are presented here as functions). -/
structure CellStructure where
  /-- The carrier of cells. -/
  Cell : Type
  /-- The chosen reverse of a cell. -/
  reverse : Cell → Cell
  /-- The chosen unit witness (the higher cell witnessing `reverse ∘ cell ≃ id`). -/
  unitWitness : Cell → Cell
  /-- The chosen counit witness (the higher cell witnessing `cell ∘ reverse ≃ id`). -/
  counitWitness : Cell → Cell

/-- The **invertibility witness operator** of a cell structure: a family is applied to a cell exactly
when the cell's reverse, unit witness, and counit witness are all already in the family.  Its post-fixed
families are precisely the invertibility sets. -/
def invertibilityWitnessOperator (cells : CellStructure) : WitnessOperator cells.Cell where
  apply := fun member cell =>
    member (cells.reverse cell) ∧ member (cells.unitWitness cell) ∧ member (cells.counitWitness cell)
  monotone := fun containment _cell witnesses =>
    ⟨containment _ witnesses.1, containment _ witnesses.2.1, containment _ witnesses.2.2⟩

/-- **HL23 Def 4.15.**  An **invertibility set** of a cell structure: a family of cells closed under
taking reverse, unit witness, and counit witness.  Stated as a structure to mirror the definition; it is
equivalent to a post-fixed family of `invertibilityWitnessOperator` (`isPostFixed` / `ofPostFixed`). -/
structure IsInvertibilitySet (cells : CellStructure) (member : cells.Cell → Prop) : Prop where
  /-- The reverse of a member is a member. -/
  reverseMember : ∀ {cell}, member cell → member (cells.reverse cell)
  /-- The unit witness of a member is a member. -/
  unitMember : ∀ {cell}, member cell → member (cells.unitWitness cell)
  /-- The counit witness of a member is a member. -/
  counitMember : ∀ {cell}, member cell → member (cells.counitWitness cell)

/-- An invertibility set is a post-fixed family of the invertibility operator. -/
theorem IsInvertibilitySet.isPostFixed {cells : CellStructure} {member : cells.Cell → Prop}
    (invertibilitySet : IsInvertibilitySet cells member) :
    IsPostFixed (invertibilityWitnessOperator cells) member :=
  fun _cell cellMember =>
    ⟨invertibilitySet.reverseMember cellMember,
     invertibilitySet.unitMember cellMember,
     invertibilitySet.counitMember cellMember⟩

/-- A post-fixed family of the invertibility operator is an invertibility set (converse of
`isPostFixed`). -/
theorem IsInvertibilitySet.ofPostFixed {cells : CellStructure} {member : cells.Cell → Prop}
    (postFixed : IsPostFixed (invertibilityWitnessOperator cells) member) :
    IsInvertibilitySet cells member where
  reverseMember := fun cellMember => (postFixed _ cellMember).1
  unitMember := fun cellMember => (postFixed _ cellMember).2.1
  counitMember := fun cellMember => (postFixed _ cellMember).2.2

/-- HL23's `eq 𝒟`: the **maximal invertibility set** — the coinductive closure (greatest post-fixed
family) of the invertibility operator, i.e. the genuinely invertible cells. -/
def maximalInvertibilitySet (cells : CellStructure) : cells.Cell → Prop :=
  coinductiveClosure (invertibilityWitnessOperator cells)

/-- The maximal invertibility set is itself an invertibility set (the greatest fixpoint is post-fixed). -/
theorem maximalInvertibilitySet_isInvertibilitySet (cells : CellStructure) :
    IsInvertibilitySet cells (maximalInvertibilitySet cells) :=
  IsInvertibilitySet.ofPostFixed (coinductiveClosure_isPostFixed (invertibilityWitnessOperator cells))

/-- **Maximality.**  Every invertibility set is contained in the maximal one — the greatest-ness of the
coinductive closure, transported across the `IsInvertibilitySet ↔ IsPostFixed` bridge. -/
theorem IsInvertibilitySet.subset_maximal {cells : CellStructure} {member : cells.Cell → Prop}
    (invertibilitySet : IsInvertibilitySet cells member) {cell : cells.Cell}
    (cellMember : member cell) : maximalInvertibilitySet cells cell :=
  invertibilitySet.isPostFixed.subset_coinductiveClosure cellMember

/-- The reverse of a maximally-invertible cell is maximally invertible. -/
theorem maximalInvertibilitySet.reverseMember {cells : CellStructure} {cell : cells.Cell}
    (member : maximalInvertibilitySet cells cell) :
    maximalInvertibilitySet cells (cells.reverse cell) :=
  (maximalInvertibilitySet_isInvertibilitySet cells).reverseMember member

/-- The unit witness of a maximally-invertible cell is maximally invertible. -/
theorem maximalInvertibilitySet.unitMember {cells : CellStructure} {cell : cells.Cell}
    (member : maximalInvertibilitySet cells cell) :
    maximalInvertibilitySet cells (cells.unitWitness cell) :=
  (maximalInvertibilitySet_isInvertibilitySet cells).unitMember member

/-- The counit witness of a maximally-invertible cell is maximally invertible. -/
theorem maximalInvertibilitySet.counitMember {cells : CellStructure} {cell : cells.Cell}
    (member : maximalInvertibilitySet cells cell) :
    maximalInvertibilitySet cells (cells.counitWitness cell) :=
  (maximalInvertibilitySet_isInvertibilitySet cells).counitMember member

end FX1Poly.Polygraph.Invertibility
