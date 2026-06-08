import FX1Poly.Typed.UniverseCodeShape

/-! Scratch: the pure structural universe-code dichotomy — every RawTerm either IS a universe code (∃ levelExpr
flag) or provably is NOT one (∀ levelExpr flag, ≠). This is the routing primitive the totalBridge assembly's
`var` / `piElim` arms need: `RefinedTotalBridgeConclusion.var` / `.piElim` carry a `lookupNotUniverse` /
`resultNotUniverse` hypothesis (the classifier is not a universe code), and the assembly discharges it for the
TERM case while routing the neutral-TYPE case (type variable / type-family application — the cases whose
conjunct-2 level-flexibility is unsatisfiable) to the pinned reclassifier handler. The split is exactly this
dichotomy applied to `context.lookup index` resp. `subst0 codomainCode argument`.

Decided by head-generator inspection (`DecidableEq Generator` via `by_cases`, no Classical): head =
`gen_universeCode` recovers the cell as a `universeCodeCell` (`eq_universeCodeCell_of_headGenerator`); otherwise
any equality to a universe code would force the head to be `gen_universeCode` (`headGenerator_universeCodeCell`),
contradiction. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem RawTerm.isUniverseCodeOrNot {scope : Nat} (term : RawTerm scope) :
    (∃ (levelExpr : LevelExpr) (flag : UniverseFlag), term = universeCodeCell levelExpr flag) ∨
    (∀ (levelExpr : LevelExpr) (flag : UniverseFlag), term ≠ universeCodeCell levelExpr flag) := by
  by_cases headIsUniverseCode : RawTerm.headGenerator term = Generator.gen_universeCode
  · exact Or.inl (eq_universeCodeCell_of_headGenerator headIsUniverseCode)
  · refine Or.inr (fun levelExpr flag termEqUniverseCode => headIsUniverseCode ?_)
    rw [termEqUniverseCode]
    exact headGenerator_universeCodeCell levelExpr flag

end FX1Poly.Typed

#print axioms FX1Poly.Typed.RawTerm.isUniverseCodeOrNot
