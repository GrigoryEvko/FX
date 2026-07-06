import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision

/-! # NonCrossingMatching — the planarity predicate on an extracted partner matching (cup rung D2a-i)

The arc diagram a spine folds to is planar: read the boundary as a matching (each index paired
with its partner) and no two arcs interleave.  This file states that property on the extracted
`partner` list and gives its decision procedure.

A `partner : List Nat` records, at index `leftIndex`, the boundary index that `leftIndex` is
matched to (`extractDiagram` builds exactly this via `partnerIndexOf`).  Two matched arcs cross
when their endpoints interleave on the line — `leftIndex < rightIndex < partner[leftIndex] <
partner[rightIndex]`.  Every genuine crossing of two arcs is caught at its two left endpoints
(the smaller-left-endpoint arc supplies `leftIndex`, the other `rightIndex`), so the single
`PartnerCrosses` shape below is a complete crossing detector, and `IsNonCrossing` — its bounded
negation over all in-range index pairs — is the planarity statement.

Decidability is a bounded `Nat` search (`Nat.decidableBallLT` over both indices), zero-axiom.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The crossing shape and its decision -/

/-- Two matched arcs of `partner` cross: their endpoints interleave on the line, i.e.
`leftIndex < rightIndex < partner[leftIndex] < partner[rightIndex]`.  Reading `leftIndex`,
`rightIndex` as the two left endpoints and `partner[leftIndex]`, `partner[rightIndex]` as their
right endpoints, this is exactly the interleaved pattern `a < c < b < d` for arcs `a—b`, `c—d`. -/
def PartnerCrosses (partner : List Nat) (leftIndex rightIndex : Nat) : Prop :=
  leftIndex < rightIndex
    ∧ rightIndex < natListGetAt partner leftIndex
    ∧ natListGetAt partner leftIndex < natListGetAt partner rightIndex

instance instDecidablePartnerCrosses (partner : List Nat) (leftIndex rightIndex : Nat) :
    Decidable (PartnerCrosses partner leftIndex rightIndex) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## The planarity predicate and its decision -/

/-- The extracted matching `partner` is non-crossing (planar): no two in-range matched arcs
interleave.  The nested bounded-`∀` form (`leftIndex` under its bound, then `rightIndex` under
its bound) is what makes the decision a `Nat.decidableBallLT` over both indices. -/
def IsNonCrossing (partner : List Nat) : Prop :=
  ∀ leftIndex : Nat, leftIndex < partner.length →
    ∀ rightIndex : Nat, rightIndex < partner.length →
      ¬ PartnerCrosses partner leftIndex rightIndex

instance instDecidableIsNonCrossing (partner : List Nat) : Decidable (IsNonCrossing partner) :=
  Nat.decidableBallLT partner.length
    (fun leftIndex _ => ∀ rightIndex, rightIndex < partner.length →
      ¬ PartnerCrosses partner leftIndex rightIndex)

/-- The empty matching is non-crossing — there are no in-range indices to cross. -/
theorem isNonCrossing_nil : IsNonCrossing [] :=
  fun _ leftBelow _ _ => absurd leftBelow (Nat.not_lt_zero _)

/-! ## Honesty marker -/

/-- **Honesty marker — the non-crossing planarity predicate on the extracted matching is
DEFINED and DECIDABLE (cup rung D2a-i).**  `PartnerCrosses` (the complete crossing detector at
a left-endpoint pair), `IsNonCrossing` (its bounded negation), both `Decidable` via zero-axiom
bounded `Nat` search, and the empty base case.  What this marker does NOT claim: the state-level
`ArcNonCrossing` invariant and its fold preservation (D2a-ii/iii/iv), the extract-time
translation to `IsNonCrossing (extractDiagram …).partner`, and the leg-aligned selector that
consumes the resulting planar partition (D1/D2).  `= true`. -/
def fxMode_hasNonCrossingMatchingPredicate : Bool := true

end FX1Poly.Polygraph
