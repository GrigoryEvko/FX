import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellStrongNormalization

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellStrongNormalization — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the strong normalization of the `TwoCellStep` 3-polygraph — the
TERMINATION half of `fxMode_hasConvergentThreeCellSystem`, the structural floor under the entire fib-3
mode-side decidability keystone. The polynomial weight, its per-rule strict-decrease (twelve `TwoCellStep`
rules, including the derived-`hcomp` interchange/Godement law), and the fuel-bounded `Acc`-descent SN theorem.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. The interchange
arithmetic in particular is hand-built from a single associative-commutative primitive (`natAddSwapMiddle`)
plus structural `Nat` lemmas precisely because `omega`/`simp`-with-AC/`ac_rfl`/`Nat.add_right_cancel` all leak
`propext`. -/

namespace FX1PolyAudit

-- ★ The polynomial weight is itself axiom-free (structural recursion, constant Nat motive)
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.weight

-- ★ Every TwoCellStep rule strictly decreases the weight (the twelve-rule case analysis)
#assert_no_axioms FX1Poly.Tier0.TwoCellStep.weight_lt

-- ★ TwoCellStep is strongly normalizing — the mode-3 structural floor's termination half
#assert_no_axioms FX1Poly.Tier0.twoCellStep_isStronglyNormalizing

end FX1PolyAudit
