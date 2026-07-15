import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.FibrationCategory

/-! # FX1PolyAudit/AuditAxisContextFibrationCategory — zero-axiom gate for context-15's model structure

Per-declaration zero-axiom gate for `context-15`'s context-side deliverable
(`FX1Poly/Axis/Context/FibrationCategory.lean`): the Avigad–Kapulkin–Lumsdaine fibration-category
structure on contexts — the Brown fibration-category interface, the reusable isomorphism 2-out-of-3 base
(identities are isos, isos compose), and the point as a genuine fibration-category witness.  The display-map
witness, factorization, pullback-stability, and path objects are the honest deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The reusable isomorphism base (the 2-out-of-3 weak-equivalence sub-class)
#assert_no_axioms FX1Poly.Polygraph.IsIsomorphism.identityWitness
#assert_no_axioms FX1Poly.Polygraph.IsIsomorphism.composeWitness
#assert_no_axioms FX1Poly.Polygraph.IsIsomorphism.inverseIso
#assert_no_axioms FX1Poly.Polygraph.IsIsomorphism.twoOutOfThreeRight

-- The Brown fibration-category interface
#assert_no_axioms FX1Poly.Axis.BrownFibrationStructure

-- The point as a fibration category
#assert_no_axioms FX1Poly.Axis.terminalCategory
#assert_no_axioms FX1Poly.Axis.terminalFibrationCategory

-- The GENUINE category of contexts 𝒞 as a fibration category
#assert_no_axioms FX1Poly.Polygraph.RawCategory.opposite
#assert_no_axioms FX1Poly.Axis.fxContextCategory
#assert_no_axioms FX1Poly.Axis.fxContextFibrationCategory

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Axis.fibrationCategory_hasDisplayMapFibrations
#assert_no_axioms FX1Poly.Axis.fibrationCategory_hasFactorization
#assert_no_axioms FX1Poly.Axis.fibrationCategory_hasFibrationPullbackStability
#assert_no_axioms FX1Poly.Axis.fibrationCategory_hasPathObjects
#assert_no_axioms FX1Poly.Axis.terminalFibrationCategory_identityIsWeakEquivalence_smoke
#assert_no_axioms FX1Poly.Axis.fxContextFibrationCategory_identityIsWeakEquivalence_smoke

end FX1PolyAudit
