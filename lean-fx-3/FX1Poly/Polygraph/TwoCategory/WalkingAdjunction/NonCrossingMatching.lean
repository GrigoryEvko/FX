import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision

/-! # NonCrossingMatching — the planarity predicate on an extracted partner matching (cup rung D2a-i)

The arc diagram a spine folds to is planar in the RECTANGLE: bottom ports along the bottom edge,
top ports (the final open wires) along the top edge, strands connecting them without crossing.
This file states that planarity on the extracted `partner` list and gives its decision procedure.

`extractDiagram` builds `partner : List Nat` over the boundary `List.range bottomCount ++
openWires`, so index `< bottomCount` is a bottom port (left to right) and index `≥ bottomCount`
is a top port (also left to right).  Planarity of a diagram drawn in a rectangle is non-crossing
with respect to the boundary read AROUND the rectangle: bottom left-to-right, then top
RIGHT-to-left.  `boundaryPosition` performs exactly that cyclic linearization — bottom indices
keep their value, top indices are reversed past the bottom block — so that the identity diagram
(straight parallel strands) reads as a NESTED family (planar), not an interleaved one.

An arc's two rectangle endpoints are `arcMinPosition`/`arcMaxPosition` (the smaller/larger
`boundaryPosition` of the index and its partner).  Two arcs cross (`ArcsCross`) when their
endpoints interleave on the boundary — `min(left) < min(right) < max(left) < max(right)` — and
every genuine crossing is caught at the smaller-`min` arc.  `IsNonCrossing` is the bounded
negation over all in-range index pairs, the planarity statement.

Decidability is a bounded `Nat` search (`Nat.decidableBallLT` over both indices), zero-axiom.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Rectangle boundary linearization -/

/-- Position of a boundary index in the rectangle's cyclic traversal.  Bottom ports (`index <
bottomCount`) keep their left-to-right order; top ports are traversed right-to-left, so top
index `index` lands at `bottomCount + (total - 1 - index)` — the last top port first. -/
def boundaryPosition (bottomCount total index : Nat) : Nat :=
  if index < bottomCount then index else bottomCount + (total - 1 - index)

/-- The nearer rectangle endpoint of the arc through `index`: the smaller `boundaryPosition` of
`index` and its partner. -/
def arcMinPosition (bottomCount total : Nat) (partner : List Nat) (index : Nat) : Nat :=
  Nat.min (boundaryPosition bottomCount total index)
          (boundaryPosition bottomCount total (natListGetAt partner index))

/-- The farther rectangle endpoint of the arc through `index`: the larger `boundaryPosition` of
`index` and its partner. -/
def arcMaxPosition (bottomCount total : Nat) (partner : List Nat) (index : Nat) : Nat :=
  Nat.max (boundaryPosition bottomCount total index)
          (boundaryPosition bottomCount total (natListGetAt partner index))

/-! ## The crossing shape and its decision -/

/-- The arcs through `leftIndex` and `rightIndex` cross: their endpoints interleave on the
rectangle boundary, `min(left) < min(right) < max(left) < max(right)`.  Reading the arc with the
smaller near-endpoint as the left one, this is the interleaved pattern that makes two strands
cross inside the rectangle. -/
def ArcsCross (bottomCount total : Nat) (partner : List Nat) (leftIndex rightIndex : Nat) :
    Prop :=
  arcMinPosition bottomCount total partner leftIndex
      < arcMinPosition bottomCount total partner rightIndex
    ∧ arcMinPosition bottomCount total partner rightIndex
      < arcMaxPosition bottomCount total partner leftIndex
    ∧ arcMaxPosition bottomCount total partner leftIndex
      < arcMaxPosition bottomCount total partner rightIndex

instance instDecidableArcsCross (bottomCount total : Nat) (partner : List Nat)
    (leftIndex rightIndex : Nat) :
    Decidable (ArcsCross bottomCount total partner leftIndex rightIndex) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## The planarity predicate and its decision -/

/-- The extracted matching `partner` (over `List.range bottomCount ++ openWires`) is non-crossing
(planar in the rectangle): no two in-range arcs interleave on the cyclic boundary.  The nested
bounded-`∀` form is what makes the decision a `Nat.decidableBallLT` over both indices; `total` is
`partner.length` (the boundary size). -/
def IsNonCrossing (bottomCount : Nat) (partner : List Nat) : Prop :=
  ∀ leftIndex : Nat, leftIndex < partner.length →
    ∀ rightIndex : Nat, rightIndex < partner.length →
      ¬ ArcsCross bottomCount partner.length partner leftIndex rightIndex

instance instDecidableIsNonCrossing (bottomCount : Nat) (partner : List Nat) :
    Decidable (IsNonCrossing bottomCount partner) :=
  Nat.decidableBallLT partner.length
    (fun leftIndex _ => ∀ rightIndex, rightIndex < partner.length →
      ¬ ArcsCross bottomCount partner.length partner leftIndex rightIndex)

/-- The empty matching is non-crossing — there are no in-range indices to cross. -/
theorem isNonCrossing_nil (bottomCount : Nat) : IsNonCrossing bottomCount [] :=
  fun _ leftBelow _ _ => absurd leftBelow (Nat.not_lt_zero _)

/-! ## Honesty marker -/

/-- **Honesty marker — the RECTANGLE planarity predicate on the extracted matching is DEFINED and
DECIDABLE (cup rung D2a-i).**  `boundaryPosition` (the cyclic bottom-then-reversed-top boundary
linearization), `arcMinPosition`/`arcMaxPosition` (an arc's two rectangle endpoints), `ArcsCross`
(the complete crossing detector at the smaller-endpoint arc), `IsNonCrossing` (its bounded
negation), all `Decidable` via zero-axiom bounded `Nat` search, and the empty base case.  What
this marker does NOT claim: the state-level `ArcNonCrossing` invariant and its fold preservation
(D2a-ii/iii/iv), the extract-time proof that `IsNonCrossing bottomCount (arcStructureOfSpineList
…).diagram.partner` actually holds, and the leg-aligned selector that consumes the resulting
planar partition (D1/D2).  `= true`. -/
def fxMode_hasNonCrossingMatchingPredicate : Bool := true

end FX1Poly.Polygraph
