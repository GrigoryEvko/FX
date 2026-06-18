import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Rewrite.PolygraphicResolution

/-! # FX1PolyAudit/AuditTier0TermPolygraphicResolution — zero-axiom gate for term-5

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Rewrite/PolygraphicResolution.lean`: the 𝔽₂
polygraphic chain complex (`F2ChainComplex` + `∂²=0`), the quotient-free homology objects
(`IsCycle` / `IsBoundary` / `boundary_isCycle` / `HomologyVanishes` / `IsAcyclic`), the concrete witnesses
(`trivialComplex` acyclic vs `zeroDifferentialComplex` non-vanishing), the term-4 connection
(`rewriteResolution_dimTwoAcyclic`), and the (∞)-resolution interface (`PolygraphResolution`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — in particular the `Bool`-case 𝔽₂ laws and the `Unit`-eta witness must not
leak. -/

namespace FX1PolyAudit

-- The 𝔽₂ chain complex + the quotient-free homology objects
#assert_no_axioms FX1Poly.Core.F2ChainComplex
#assert_no_axioms FX1Poly.Core.F2ChainComplex.IsCycle
#assert_no_axioms FX1Poly.Core.F2ChainComplex.IsBoundary
#assert_no_axioms FX1Poly.Core.F2ChainComplex.boundary_isCycle
#assert_no_axioms FX1Poly.Core.F2ChainComplex.HomologyVanishes
#assert_no_axioms FX1Poly.Core.F2ChainComplex.IsAcyclic

-- The concrete witnesses (acyclic vs non-vanishing) — non-vacuity
#assert_no_axioms FX1Poly.Core.F2ChainComplex.trivialComplex
#assert_no_axioms FX1Poly.Core.F2ChainComplex.trivialComplex_isAcyclic
#assert_no_axioms FX1Poly.Core.F2ChainComplex.zeroDifferentialComplex
#assert_no_axioms FX1Poly.Core.F2ChainComplex.zeroDifferentialComplex_homologyNotVanishing

-- Cycles and boundaries are 𝔽₂-subgroups
#assert_no_axioms FX1Poly.Core.F2ChainComplex.zero_isCycle
#assert_no_axioms FX1Poly.Core.F2ChainComplex.add_isCycle
#assert_no_axioms FX1Poly.Core.F2ChainComplex.zero_isBoundary
#assert_no_axioms FX1Poly.Core.F2ChainComplex.add_isBoundary

-- The concrete polygraphic computation: the abelianized boundary of two presentations
#assert_no_axioms FX1Poly.Core.wordAbelianizationF2
#assert_no_axioms FX1Poly.Core.relationBoundaryF2
#assert_no_axioms FX1Poly.Core.zmod2_relationBoundary_zero
#assert_no_axioms FX1Poly.Core.aEqB_relationBoundary_nonzero

-- The (∞)-resolution interface + the term-4 dim-2 acyclicity connection
#assert_no_axioms FX1Poly.Core.rewriteResolution_dimTwoAcyclic
#assert_no_axioms FX1Poly.Core.PolygraphResolution

end FX1PolyAudit
