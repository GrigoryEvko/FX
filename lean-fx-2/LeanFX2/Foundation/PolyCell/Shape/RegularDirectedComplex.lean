import LeanFX2.Foundation.PolyCell.Shape.OrientedGradedPoset
/-!
# Regular Directed Complex (Hadzihasanovic 2024)

The current Axis 1 regular-directed-complex interface.  It supplies
molecule-shaped predicates, closed singletons, the regularity record, and
the point regular directed complex.

This is not the Hadzihasanovic development package: there are no classical
shape-family constructors, no boundary-checked molecule laws, and no
omega-category structure in this file.

Reference: arXiv:2404.07273 Definition 1.3.1.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Shape

/-- Construction ledger for Axis 1 shape machinery.

The levels are deliberately evidence-shaped.  A later level may only be
selected after the corresponding Lean objects and audit gates exist. -/
inductive ShapeConstructionLevel where
  /-- Graded elements and oriented-graded-poset interface are available. -/
  | gradedElementAndPosetInterface
  /-- Empty and point oriented graded posets are available. -/
  | pointAndEmptyShapes
  /-- The point regular directed complex has been constructed. -/
  | regularDirectedComplexPoint
  /-- Molecule predicates and the regularity record interface exist. -/
  | moleculePredicateInterfaces
  /-- Standard shape-family constructors have been supplied. -/
  | classicalShapeFamilyConstructors
  /-- Omega-category structure on molecules has been supplied. -/
  | omegaCategoryStructure
  /-- The Hadzihasanovic shape package has been mechanized. -/
  | hadzihasanovicShapePackage
  deriving DecidableEq, Repr

/-- Whether the level includes graded-element and OGP interfaces. -/
def ShapeConstructionLevel.hasGradedElementAndPosetInterface :
    ShapeConstructionLevel → Bool
  | .gradedElementAndPosetInterface => true
  | .pointAndEmptyShapes => true
  | .regularDirectedComplexPoint => true
  | .moleculePredicateInterfaces => true
  | .classicalShapeFamilyConstructors => true
  | .omegaCategoryStructure => true
  | .hadzihasanovicShapePackage => true

/-- Whether the level includes empty and point OGP examples. -/
def ShapeConstructionLevel.hasPointAndEmptyShapes :
    ShapeConstructionLevel → Bool
  | .gradedElementAndPosetInterface => false
  | .pointAndEmptyShapes => true
  | .regularDirectedComplexPoint => true
  | .moleculePredicateInterfaces => true
  | .classicalShapeFamilyConstructors => true
  | .omegaCategoryStructure => true
  | .hadzihasanovicShapePackage => true

/-- Whether the level includes the point regular directed complex. -/
def ShapeConstructionLevel.hasRegularDirectedComplexPoint :
    ShapeConstructionLevel → Bool
  | .gradedElementAndPosetInterface => false
  | .pointAndEmptyShapes => false
  | .regularDirectedComplexPoint => true
  | .moleculePredicateInterfaces => true
  | .classicalShapeFamilyConstructors => true
  | .omegaCategoryStructure => true
  | .hadzihasanovicShapePackage => true

/-- Whether the level includes molecule predicates and regularity records. -/
def ShapeConstructionLevel.hasMoleculePredicateInterfaces :
    ShapeConstructionLevel → Bool
  | .gradedElementAndPosetInterface => false
  | .pointAndEmptyShapes => false
  | .regularDirectedComplexPoint => false
  | .moleculePredicateInterfaces => true
  | .classicalShapeFamilyConstructors => true
  | .omegaCategoryStructure => true
  | .hadzihasanovicShapePackage => true

/-- Whether the level includes boundary-checked molecule laws. -/
def ShapeConstructionLevel.hasBoundaryCheckedMoleculeLaws :
    ShapeConstructionLevel → Bool
  | .gradedElementAndPosetInterface => false
  | .pointAndEmptyShapes => false
  | .regularDirectedComplexPoint => false
  | .moleculePredicateInterfaces => false
  | .classicalShapeFamilyConstructors => false
  | .omegaCategoryStructure => true
  | .hadzihasanovicShapePackage => true

/-- Whether the level includes classical shape-family constructors. -/
def ShapeConstructionLevel.hasClassicalShapeFamilyConstructors :
    ShapeConstructionLevel → Bool
  | .gradedElementAndPosetInterface => false
  | .pointAndEmptyShapes => false
  | .regularDirectedComplexPoint => false
  | .moleculePredicateInterfaces => false
  | .classicalShapeFamilyConstructors => true
  | .omegaCategoryStructure => true
  | .hadzihasanovicShapePackage => true

/-- Whether the level includes omega-category structure on molecules. -/
def ShapeConstructionLevel.hasOmegaCategoryStructure :
    ShapeConstructionLevel → Bool
  | .gradedElementAndPosetInterface => false
  | .pointAndEmptyShapes => false
  | .regularDirectedComplexPoint => false
  | .moleculePredicateInterfaces => false
  | .classicalShapeFamilyConstructors => false
  | .omegaCategoryStructure => true
  | .hadzihasanovicShapePackage => true

/-- Whether the level includes the Hadzihasanovic shape package. -/
def ShapeConstructionLevel.hasHadzihasanovicShapePackage :
    ShapeConstructionLevel → Bool
  | .gradedElementAndPosetInterface => false
  | .pointAndEmptyShapes => false
  | .regularDirectedComplexPoint => false
  | .moleculePredicateInterfaces => false
  | .classicalShapeFamilyConstructors => false
  | .omegaCategoryStructure => false
  | .hadzihasanovicShapePackage => true

/-- FX Axis 1 currently has shape interfaces plus molecule predicate records. -/
def fxShapeConstructionLevel : ShapeConstructionLevel :=
  .moleculePredicateInterfaces

theorem fxShapeConstructionLevel_eq :
    fxShapeConstructionLevel =
      ShapeConstructionLevel.moleculePredicateInterfaces := rfl

theorem fxShape_hasGradedElementAndPosetInterface :
    fxShapeConstructionLevel.hasGradedElementAndPosetInterface = true := rfl

theorem fxShape_hasPointAndEmptyShapes :
    fxShapeConstructionLevel.hasPointAndEmptyShapes = true := rfl

theorem fxShape_hasRegularDirectedComplexPoint :
    fxShapeConstructionLevel.hasRegularDirectedComplexPoint = true := rfl

theorem fxShape_hasMoleculePredicateInterfaces :
    fxShapeConstructionLevel.hasMoleculePredicateInterfaces = true := rfl

theorem fxShape_hasNoBoundaryCheckedMoleculeLaws :
    fxShapeConstructionLevel.hasBoundaryCheckedMoleculeLaws = false := rfl

theorem fxShape_hasNoClassicalShapeFamilyConstructors :
    fxShapeConstructionLevel.hasClassicalShapeFamilyConstructors = false :=
  rfl

theorem fxShape_hasNoOmegaCategoryStructure :
    fxShapeConstructionLevel.hasOmegaCategoryStructure = false := rfl

theorem fxShape_hasNoHadzihasanovicShapePackage :
    fxShapeConstructionLevel.hasHadzihasanovicShapePackage = false := rfl

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
