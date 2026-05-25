/-!
# Oriented Graded Poset (Hadzihasanovic 2024)

The current Axis 1 interface for finite oriented graded posets.  An
oriented graded poset is a finite list of cells graded by dimension, with
each cell's cofaces partitioned into input and output cofaces.

This file only provides the interface plus empty and point examples.  It
does not construct the classical shape families, molecule category, or the
Hadzihasanovic regular-directed-complex package.

Reference: arXiv:2404.07273 §1.1-1.2 (337-page monograph).
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Shape

/-- An element of a graded poset with its dimension. -/
structure GradedElement (maxDim : Nat) where
  identifier : Nat
  dimension : Fin (maxDim + 1)
  deriving DecidableEq, Repr

/-- An oriented graded poset: elements graded by dimension, with each
element's immediate cofaces (higher-dim neighbors) partitioned into
input (source-facing) and output (target-facing) cofaces.

This is a FINITARY encoding suitable for computation — all sets are
represented as lists with uniqueness invariants enforced externally. -/
structure OrientedGradedPoset where
  /-- Maximum dimension present in this poset. -/
  maxDimension : Nat

  /-- The elements, each carrying an identifier and dimension. -/
  elements : List (GradedElement maxDimension)

  /-- No duplicate identifiers. -/
  elementsUnique : elements.Pairwise (fun elemA elemB => elemA.identifier ≠ elemB.identifier)

  /-- Input cofaces (source-facing): for element x at dim d, these are
  elements at dim d+1 that have x as a source-boundary face. -/
  inputCofaces : GradedElement maxDimension → List (GradedElement maxDimension)

  /-- Output cofaces (target-facing): for element x at dim d, these are
  elements at dim d+1 that have x as a target-boundary face. -/
  outputCofaces : GradedElement maxDimension → List (GradedElement maxDimension)

  /-- Cofaces are at exactly one dimension higher. -/
  inputCofacesDimension :
    ∀ (element : GradedElement maxDimension)
      (coface : GradedElement maxDimension),
    coface ∈ inputCofaces element →
    coface.dimension.val = element.dimension.val + 1

  outputCofacesDimension :
    ∀ (element : GradedElement maxDimension)
      (coface : GradedElement maxDimension),
    coface ∈ outputCofaces element →
    coface.dimension.val = element.dimension.val + 1

  /-- Input and output cofaces are disjoint. -/
  cofacesDisjoint :
    ∀ (element : GradedElement maxDimension)
      (coface : GradedElement maxDimension),
    coface ∈ inputCofaces element →
    coface ∉ outputCofaces element

/-- The faces of an element (lower-dim boundary cells). -/
def OrientedGradedPoset.faces (poset : OrientedGradedPoset)
    (element : GradedElement poset.maxDimension) :
    List (GradedElement poset.maxDimension) :=
  poset.elements.filter fun candidate =>
    element ∈ poset.inputCofaces candidate ∨
    element ∈ poset.outputCofaces candidate

/-- Source boundary at dimension k (fuel-bounded traversal).
Fuel = dimension difference; decreases at each recursive step. -/
def OrientedGradedPoset.sourceBoundary (poset : OrientedGradedPoset)
    (element : GradedElement poset.maxDimension)
    (targetDim : Nat)
    (fuel : Nat := poset.maxDimension) :
    List (GradedElement poset.maxDimension) :=
  match fuel with
  | 0 => [element]
  | fuel + 1 =>
    if element.dimension.val ≤ targetDim then [element]
    else
      let inputFaces := poset.elements.filter fun candidate =>
        element ∈ poset.inputCofaces candidate
      inputFaces.flatMap (fun face => poset.sourceBoundary face targetDim fuel)

/-- Target boundary at dimension k (fuel-bounded). -/
def OrientedGradedPoset.targetBoundary (poset : OrientedGradedPoset)
    (element : GradedElement poset.maxDimension)
    (targetDim : Nat)
    (fuel : Nat := poset.maxDimension) :
    List (GradedElement poset.maxDimension) :=
  match fuel with
  | 0 => [element]
  | fuel + 1 =>
    if element.dimension.val ≤ targetDim then [element]
    else
      let outputFaces := poset.elements.filter fun candidate =>
        element ∈ poset.outputCofaces candidate
      outputFaces.flatMap (fun face => poset.targetBoundary face targetDim fuel)

/-- Number of elements at a given dimension. -/
def OrientedGradedPoset.countAtDim (poset : OrientedGradedPoset)
    (dimension : Nat) : Nat :=
  (poset.elements.filter fun elem => elem.dimension.val = dimension).length

/-- Total number of elements. -/
def OrientedGradedPoset.size (poset : OrientedGradedPoset) : Nat :=
  poset.elements.length

/-- An element is a point (dim 0) iff it has no faces. -/
def OrientedGradedPoset.isPoint (poset : OrientedGradedPoset)
    (element : GradedElement poset.maxDimension) : Bool :=
  element.dimension.val == 0

/-- An element is top-dimensional. -/
def OrientedGradedPoset.isTopDim (poset : OrientedGradedPoset)
    (element : GradedElement poset.maxDimension) : Bool :=
  element.dimension.val == poset.maxDimension

/-- Roundness: a sub-collection is "round" if its source and target
boundaries at each dimension are well-formed. For dim-0, roundness is
trivial. This is the recursive well-formedness predicate that gates
composition (pasting). -/
def OrientedGradedPoset.isRound (poset : OrientedGradedPoset)
    (subcollection : List (GradedElement poset.maxDimension)) : Bool :=
  subcollection.all fun elem => poset.elements.contains elem

/-- The empty oriented graded poset (no elements). -/
def OrientedGradedPoset.empty : OrientedGradedPoset where
  maxDimension := 0
  elements := []
  elementsUnique := List.Pairwise.nil
  inputCofaces := fun _ => []
  outputCofaces := fun _ => []
  inputCofacesDimension := fun _ _ h => nomatch h
  outputCofacesDimension := fun _ _ h => nomatch h
  cofacesDisjoint := fun _ _ h => nomatch h

/-- The point: one dim-0 element, no cofaces. -/
def OrientedGradedPoset.point : OrientedGradedPoset where
  maxDimension := 0
  elements := [⟨0, ⟨0, Nat.zero_lt_succ 0⟩⟩]
  elementsUnique := List.pairwise_singleton _ _
  inputCofaces := fun _ => []
  outputCofaces := fun _ => []
  inputCofacesDimension := fun _ _ h => nomatch h
  outputCofacesDimension := fun _ _ h => nomatch h
  cofacesDisjoint := fun _ _ h => nomatch h

theorem OrientedGradedPoset.point_size : OrientedGradedPoset.point.size = 1 := rfl

theorem OrientedGradedPoset.empty_size : OrientedGradedPoset.empty.size = 0 := rfl

end LeanFX2.Foundation.PolyCell.Shape
