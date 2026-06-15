import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.DemocracyLCC

/-! # FX1PolyAudit/AuditTier0ContextDemocracyLCC — zero-axiom gate for context-16's democracy + LCC

Per-declaration zero-axiom gate for `context-16`'s context-side deliverable
(`FX1Poly/Tier0/Context/DemocracyLCC.lean`, `⊟SPLIT · core=democracy×type→fib-1`): the democracy interface
(context ≅ closed-type comprehension) and the cartesian part of local cartesian closure (terminal +
products with their universal property).  Beyond the point witness, the GENERIC dualization
(`ofOppositeFiniteCoproducts` — coproducts in `𝒟` are products in `𝒟ᵒᵖ`) yields `fxContextCartesianClosed`,
the NON-degenerate cartesian witness over the genuine context category `𝒞` (products are real context
concatenation).  The closed-type packing, the local exponentials (Π), and the FULL Σ/Π FX witness are the
honest `×type → fib-1` deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Democracy (interface + terminal witness)
#assert_no_axioms FX1Poly.Tier0.DemocraticStructure
#assert_no_axioms FX1Poly.Tier0.terminalDemocratic

-- Local cartesian closure — the cartesian part (interface + terminal witness)
#assert_no_axioms FX1Poly.Tier0.LocallyCartesianClosedStructure
#assert_no_axioms FX1Poly.Tier0.terminalLCC

-- The GENUINE 𝒞 cartesian witness via the coproduct→product dualization
#assert_no_axioms FX1Poly.Tier0.LocallyCartesianClosedStructure.ofOppositeFiniteCoproducts
#assert_no_axioms FX1Poly.Tier0.fxContextCartesianClosed

-- Honesty markers (the ×type → fib-1 core) + smokes
#assert_no_axioms FX1Poly.Tier0.democracyLCC_hasClosedTypePacking
#assert_no_axioms FX1Poly.Tier0.democracyLCC_hasLocalExponentials
#assert_no_axioms FX1Poly.Tier0.democracyLCC_hasFxWitness
#assert_no_axioms FX1Poly.Tier0.terminalDemocratic_comparisonIso_smoke
#assert_no_axioms FX1Poly.Tier0.fxContextCartesianClosed_product_smoke

end FX1PolyAudit
