import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Frontier.ProvabilityKripke

/-! # FX1PolyAudit/AuditAxisModeFrontierProvabilityKripke — zero-axiom gate for the mode-23 GL Kripke frontier

Per-declaration zero-axiom gate for `FX1Poly/Axis/Mode/Frontier/ProvabilityKripke.lean`: the GL formula syntax,
the Hilbert derivability calculus, the Kripke forcing semantics, GL soundness over transitive + converse-well-
founded two-valued frames, and the concrete one-point countermodel that refutes the T axiom (the contrapositive-of-
completeness / consistency witness).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- Syntax
#assert_no_axioms FX1Poly.Axis.GLFormula
#assert_no_axioms FX1Poly.Axis.glNot
#assert_no_axioms FX1Poly.Axis.GLProves

-- Kripke semantics
#assert_no_axioms FX1Poly.Axis.forces
#assert_no_axioms FX1Poly.Axis.forces_box_eq_boxOver
#assert_no_axioms FX1Poly.Axis.IsTwoValuedModel

-- Soundness (the modal cases delegate to Provability.lean)
#assert_no_axioms FX1Poly.Axis.glProves_sound

-- The concrete dead-end countermodel frame
#assert_no_axioms FX1Poly.Axis.DeadEndWorld
#assert_no_axioms FX1Poly.Axis.deadEndAccessible
#assert_no_axioms FX1Poly.Axis.deadEndValuation
#assert_no_axioms FX1Poly.Axis.deadEndFrame_isTransitive
#assert_no_axioms FX1Poly.Axis.deadEndFrame_isConverseWellFounded
#assert_no_axioms FX1Poly.Axis.deadEndFrame_isTwoValued

-- The refutation and the contrapositive-of-completeness witness
#assert_no_axioms FX1Poly.Axis.deadEndFrame_forces_box_atom
#assert_no_axioms FX1Poly.Axis.deadEndFrame_refutes_atom
#assert_no_axioms FX1Poly.Axis.deadEndFrame_refutes_box_atom_imp_atom
#assert_no_axioms FX1Poly.Axis.not_glProves_box_atom_imp_atom
#assert_no_axioms FX1Poly.Axis.not_glProves_bot

-- The marker stays `false` (proposed narrowed docstring is reported, not applied here)
#assert_no_axioms FX1Poly.Axis.fxMode_hasKripkeCompleteness

end FX1PolyAudit
