import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Rewrite.LevyOptimality

/-! # FX1PolyAudit/AuditTier0TermLevyOptimality — zero-axiom gate for term-9 (Lévy optimality)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Rewrite/LevyOptimality.lean`: the redex-family
relation (`CoFamilial` + refl/symm/trans — families partition redexes into Lévy-label classes), the naive
redex count (`familyTotalRedexes`), and the QUANTITATIVE optimality bound (`optimalReduction_le_unshared`:
shared ≤ naive; `optimalReduction_lt_unshared_of_sharing`: strict under genuine sharing) + the concrete
saving witnesses.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — in particular the `Nat`-order bound proofs must not leak (no `Nat.add_comm`). -/

namespace FX1PolyAudit

-- The redex-family relation (Lévy-label classes) + its equivalence laws
#assert_no_axioms FX1Poly.Core.CoFamilial
#assert_no_axioms FX1Poly.Core.CoFamilial.refl
#assert_no_axioms FX1Poly.Core.CoFamilial.symm
#assert_no_axioms FX1Poly.Core.CoFamilial.trans

-- The naive redex count + the quantitative optimality bounds
#assert_no_axioms FX1Poly.Core.familyTotalRedexes
#assert_no_axioms FX1Poly.Core.optimalReduction_le_unshared
#assert_no_axioms FX1Poly.Core.optimalReduction_lt_unshared_of_sharing

-- The concrete saving witnesses (sharing does 2 steps vs 5 naive)
#assert_no_axioms FX1Poly.Core.familyTotalRedexes_example
#assert_no_axioms FX1Poly.Core.optimalReductionLength_example
#assert_no_axioms FX1Poly.Core.levyOptimality_savesWork_witness

end FX1PolyAudit
