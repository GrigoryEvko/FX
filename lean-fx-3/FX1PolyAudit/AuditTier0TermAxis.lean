import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.TermAxis

/-! # FX1PolyAudit/AuditTier0TermAxis — zero-axiom gate for `term-0`

Per-declaration zero-axiom gate for the term-axis ledger (`FX1Poly/Tier0/Term/TermAxis.lean`): the
`term-0` design-lock that adopts the Mode-style honesty-marker convention for the term axis and backs
the three metatheoretic properties the raw term layer genuinely earns — raw confluence (`term-2` /
`term-20` substrate), decidable conversion as a function of convergence (`term-20` capstone), and the
modular strong-normalization criterion (`term-6` / `term-19`) — plus the honest deferred markers for
the structural / coinductive / semantics frontier.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The three backed metatheory flips
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasRawConfluence
#assert_no_axioms FX1Poly.Tier0.fxTerm_rawConfluence_isBacked
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasNormalizerConvDecision
#assert_no_axioms FX1Poly.Tier0.fxTerm_normalizerConvDecision_isBacked
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasModularStrongNormalizationCriterion
#assert_no_axioms FX1Poly.Tier0.fxTerm_modularStrongNormalizationCriterion_isBacked

-- The honest deferred markers (structural / coinductive / semantics frontier)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasInitialAlgebraUniqueness
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasTerminalCoalgebra
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasCoherentPresentation
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasKnuthBendixCompletion
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasDenotationalAdequacy

end FX1PolyAudit
