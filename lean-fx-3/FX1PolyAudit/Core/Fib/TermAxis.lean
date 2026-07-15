import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.TermAxis

/-! # FX1PolyAudit/Core/Fib/TermAxis — zero-axiom gate for `term-0` (part 1 of 2)

Per-declaration zero-axiom gate for the term-axis ledger (`FX1Poly/Axis/Term/TermAxis.lean`): the
`term-0` design-lock that adopts the Mode-style honesty-marker convention for the term axis and backs
the three metatheoretic properties the raw term layer genuinely earns — raw confluence (`term-2` /
`term-20` substrate), decidable conversion as a function of convergence (`term-20` capstone), and the
modular strong-normalization criterion (`term-6` / `term-19`). This part covers term-0 through the
`term-12` standardization core; `term-13`..`term-27` plus the deferred markers continue in
`TermAxisMore.lean`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The three backed metatheory flips
#assert_no_axioms FX1Poly.Axis.fxTerm_hasRawConfluence
#assert_no_axioms FX1Poly.Axis.fxTerm_rawConfluence_isBacked
#assert_no_axioms FX1Poly.Axis.fxTerm_hasNormalizerConvDecision
#assert_no_axioms FX1Poly.Axis.fxTerm_normalizerConvDecision_isBacked
#assert_no_axioms FX1Poly.Axis.fxTerm_hasModularStrongNormalizationCriterion
#assert_no_axioms FX1Poly.Axis.fxTerm_modularStrongNormalizationCriterion_isBacked

-- The term-6 modular-confluence criterion (Hindley-Rosen, confluence half; Core theorem referenced)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasModularConfluenceCriterion
#assert_no_axioms FX1Poly.Axis.fxTerm_modularConfluenceCriterion_isBacked

-- The term-native beta-substitution bridge (term-beta, re-homed from context-9)
#assert_no_axioms FX1Poly.Core.RawTerm.subst_cons_eq_singleton_after_lift
#assert_no_axioms FX1Poly.Axis.fxTerm_hasBetaSubstitutionBridge
#assert_no_axioms FX1Poly.Axis.fxTerm_betaSubstitutionBridge_isBacked

-- The term-1 recursor uniqueness (initial-algebra UP, uniqueness leg)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasInitialAlgebraUniqueness
#assert_no_axioms FX1Poly.Axis.fxTerm_initialAlgebraUniqueness_isBacked

-- The term-2 dim-1 rewrite preorder (free-preorder universal property + the fxIotaBundle bridge)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasDim1RewritePreorder
#assert_no_axioms FX1Poly.Axis.fxTerm_dim1RewritePreorder_isBacked

-- The term-3 terminal coalgebra (final-coalgebra UP + corecursion + coinduction)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasTerminalCoalgebra
#assert_no_axioms FX1Poly.Axis.fxTerm_terminalCoalgebra_isBacked

-- The term-4 Squier coherence (proof-relevant 2-category + the diamonds are a homotopy basis)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasCoherentPresentation
#assert_no_axioms FX1Poly.Axis.fxTerm_coherentPresentation_isBacked

-- The term-5 polygraphic resolution + 𝔽₂ homology (chain complex + homology vanishing + dim-2 acyclicity)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasPolygraphicResolution
#assert_no_axioms FX1Poly.Axis.fxTerm_polygraphicResolution_isBacked

-- The term-7 Knuth-Bendix convergence criterion (Church-Rosser + orientation soundness; Core referenced)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasKnuthBendixConvergenceCriterion
#assert_no_axioms FX1Poly.Axis.fxTerm_knuthBendixConvergenceCriterion_isBacked

-- The term-8 decreasing-diagrams framework (universal confluence; the diamond instance; Core referenced)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasDecreasingDiagramsFramework
#assert_no_axioms FX1Poly.Axis.fxTerm_decreasingDiagramsFramework_isBacked

-- The term-9 Lévy-optimality framework (redex families + the no-duplication bound)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasLevyOptimalityFramework
#assert_no_axioms FX1Poly.Axis.fxTerm_levyOptimality_isBacked

-- The term-10 Fiore-Plotkin-Turi substitution monoid (monoid laws ⟹ the substitution category)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasSubstitutionMonoid
#assert_no_axioms FX1Poly.Axis.fxTerm_substitutionMonoid_isBacked

-- The term-11 pattern-unification fragment (MGU uniqueness + the inversion round-trip)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasPatternUnification
#assert_no_axioms FX1Poly.Axis.fxTerm_patternUnification_isBacked

-- The term-12 standardization + finite-developments cores (the two reordering theorems)
#assert_no_axioms FX1Poly.Axis.fxTerm_hasStandardizationFiniteDevelopments
#assert_no_axioms FX1Poly.Axis.fxTerm_standardizationFiniteDevelopments_isBacked

end FX1PolyAudit
