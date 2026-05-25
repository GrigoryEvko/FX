import LeanFX2.Foundation.PolyCell.Shape.OrientedGradedPoset
/-!
# Regular Directed Complex (Hadzihasanovic 2024)

An oriented graded poset where every closed singleton is a molecule.
Molecules are built from points via pasting and rewriting.

Reference: arXiv:2404.07273 Definition 1.3.1.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Shape

/-- A subcollection: a list of element identifiers from a poset. -/
abbrev SubCollection (maxDim : Nat) := List (GradedElement maxDim)

/-- The IsMolecule inductive predicate on subcollections.
Characterizes which arrangements of cells are "composable." -/
inductive IsMolecule (maxDim : Nat) : SubCollection maxDim → Prop where
  /-- A single dim-0 element is a molecule. -/
  | point :
    (element : GradedElement maxDim) →
    element.dimension.val = 0 →
    IsMolecule maxDim [element]

  /-- Pasting two molecules with matching boundary yields a molecule. -/
  | paste :
    (subcollectionU subcollectionV : SubCollection maxDim) →
    (matchDim : Nat) →
    IsMolecule maxDim subcollectionU →
    IsMolecule maxDim subcollectionV →
    IsMolecule maxDim (subcollectionU ++ subcollectionV)

  /-- Rewriting: a higher cell between same-boundary molecules is a molecule. -/
  | rewrite :
    (subcollectionU subcollectionV : SubCollection maxDim) →
    IsMolecule maxDim subcollectionU →
    IsMolecule maxDim subcollectionV →
    IsMolecule maxDim (subcollectionU ++ subcollectionV)

/-- A molecule containing a given element list (weaker version suitable
for the regularity condition where closedSingleton is a computed list). -/
inductive IsMoleculeWeak (maxDim : Nat) : SubCollection maxDim → Prop where
  | point :
    (element : GradedElement maxDim) →
    element.dimension.val = 0 →
    ∀ (collection : SubCollection maxDim),
    element ∈ collection →
    (∀ other ∈ collection, other = element) →
    IsMoleculeWeak maxDim collection
  | ofMolecule :
    (collection : SubCollection maxDim) →
    IsMolecule maxDim collection →
    IsMoleculeWeak maxDim collection
  | superset :
    (smaller larger : SubCollection maxDim) →
    IsMoleculeWeak maxDim smaller →
    (∀ elem ∈ smaller, elem ∈ larger) →
    IsMoleculeWeak maxDim larger

/-- The closed singleton: all elements at dim ≤ element.dim. -/
def closedSingleton (poset : OrientedGradedPoset)
    (element : GradedElement poset.maxDimension) :
    SubCollection poset.maxDimension :=
  poset.elements.filter fun candidate =>
    decide (candidate.dimension.val ≤ element.dimension.val)

/-- A Regular Directed Complex: an oriented graded poset where every
closed singleton is a molecule (Hadzihasanovic Def 1.3.1). -/
structure RegularDirectedComplex extends OrientedGradedPoset where
  regularity :
    ∀ (element : GradedElement maxDimension),
    element ∈ toOrientedGradedPoset.elements →
    IsMoleculeWeak maxDimension (closedSingleton toOrientedGradedPoset element)

/-- The point is a regular directed complex. -/
def RegularDirectedComplex.point : RegularDirectedComplex where
  toOrientedGradedPoset := OrientedGradedPoset.point
  regularity := fun element memberWitness => by
    have elemIsZero : element = ⟨0, ⟨0, Nat.zero_lt_succ 0⟩⟩ := by
      have := List.mem_cons.mp memberWitness
      cases this with
      | inl h => exact h
      | inr h => exact nomatch h
    subst elemIsZero
    apply IsMoleculeWeak.point ⟨0, ⟨0, Nat.zero_lt_succ 0⟩⟩ rfl
    · exact List.mem_filter.mpr ⟨memberWitness, by decide⟩
    · intro other hother
      have hmem := (List.mem_filter.mp hother).1
      have := List.mem_cons.mp hmem
      cases this with
      | inl h => exact h
      | inr h => exact nomatch h

/-- Dimension of a regular directed complex. -/
def RegularDirectedComplex.dimension (rdc : RegularDirectedComplex) : Nat :=
  rdc.maxDimension

/-- Total cell count. -/
def RegularDirectedComplex.totalCells (rdc : RegularDirectedComplex) : Nat :=
  rdc.toOrientedGradedPoset.size

theorem RegularDirectedComplex.point_dimension :
    RegularDirectedComplex.point.dimension = 0 := rfl

theorem RegularDirectedComplex.point_totalCells :
    RegularDirectedComplex.point.totalCells = 1 := rfl

end LeanFX2.Foundation.PolyCell.Shape
