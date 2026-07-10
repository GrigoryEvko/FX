import FX1Poly.Polygraph.Omega.SteinerFoundation.CellCoordinates

/-! # FX1Poly/Polygraph/Steiner/DecidableCellEq — the free-fragment word-problem decider
    (frontiers.md §3.1: "two composites are the same cell iff their integer vectors are equal")

Under Steiner's equivalence the higher word problem on the loop-free / free fragment COLLAPSES to
`DecidableEq` of integer vectors — no rewriting search, no completion.  `SteinerCell` is a
non-indexed one-field structure over `List Int`, so its decidable equality is the STRUCTURAL
`List Int` decider (built from `Int.decEq` and `Nat.decEq`), propext-clean — none of the
indexed-`DecidableEq` propext traps apply.

Provenance: the REPRESENTATION is Steiner04 / Loubaton Thm 1.2.1.23; the "word problem =
`DecidableEq` of integer vectors" reading is [OurCorollary(Steiner04)].  Undecidability of the
GENERAL strict-omega-cat word problem (Novikov-Boone) is documented, never coded around: the
finiteness of the basis (the `List Int` length) is precisely what makes this collapse legitimate.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Steiner/DecidableCellEq.lean`. -/

namespace FX1Poly.Polygraph.Steiner

/-- Structural decidable equality of coordinate vectors — the whole word problem, reusing the
Init `List`/`Int` structural deciders (no indexed inductive, no `propext`). -/
def decideCoordinatesEqual : (left right : CellVector) → Decidable (left = right) :=
  fun left right => inferInstanceAs (Decidable (left = right))

/-- **The free-fragment word-problem decider.**  Decidable equality of Steiner cells = decidable
equality of their coordinate vectors: two composites are equal iff their integer vectors coincide. -/
instance decidableSteinerCellEq : DecidableEq SteinerCell :=
  fun leftCell rightCell =>
    match decideCoordinatesEqual leftCell.coordinates rightCell.coordinates with
    | isTrue areEqual =>
        isTrue (by cases leftCell; cases rightCell; exact congrArg SteinerCell.mk areEqual)
    | isFalse areNotEqual =>
        isFalse (fun cellsEqual => areNotEqual (congrArg SteinerCell.coordinates cellsEqual))

end FX1Poly.Polygraph.Steiner
