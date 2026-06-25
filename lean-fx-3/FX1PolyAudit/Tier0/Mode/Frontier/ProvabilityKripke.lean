import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Frontier.ProvabilityKripke

/-! # FX1PolyAudit/AuditTier0ModeFrontierProvabilityKripke — zero-axiom gate for the mode-23 GL Kripke frontier

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Mode/Frontier/ProvabilityKripke.lean`: the GL formula syntax,
the Hilbert derivability calculus, the Kripke forcing semantics, GL soundness over transitive + converse-well-
founded two-valued frames, and the concrete one-point countermodel that refutes the T axiom (the contrapositive-of-
completeness / consistency witness).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- Syntax
#assert_no_axioms FX1Poly.Tier0.GLFormula
#assert_no_axioms FX1Poly.Tier0.glNot
#assert_no_axioms FX1Poly.Tier0.GLProves

-- Kripke semantics
#assert_no_axioms FX1Poly.Tier0.forces
#assert_no_axioms FX1Poly.Tier0.forces_box_eq_boxOver
#assert_no_axioms FX1Poly.Tier0.IsTwoValuedModel

-- Soundness (the modal cases delegate to Provability.lean)
#assert_no_axioms FX1Poly.Tier0.glProves_sound

-- The concrete dead-end countermodel frame
#assert_no_axioms FX1Poly.Tier0.DeadEndWorld
#assert_no_axioms FX1Poly.Tier0.deadEndAccessible
#assert_no_axioms FX1Poly.Tier0.deadEndValuation
#assert_no_axioms FX1Poly.Tier0.deadEndFrame_isTransitive
#assert_no_axioms FX1Poly.Tier0.deadEndFrame_isConverseWellFounded
#assert_no_axioms FX1Poly.Tier0.deadEndFrame_isTwoValued

-- The refutation and the contrapositive-of-completeness witness
#assert_no_axioms FX1Poly.Tier0.deadEndFrame_forces_box_atom
#assert_no_axioms FX1Poly.Tier0.deadEndFrame_refutes_atom
#assert_no_axioms FX1Poly.Tier0.deadEndFrame_refutes_box_atom_imp_atom
#assert_no_axioms FX1Poly.Tier0.not_glProves_box_atom_imp_atom
#assert_no_axioms FX1Poly.Tier0.not_glProves_bot

-- The marker stays `false` (proposed narrowed docstring is reported, not applied here)
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKripkeCompleteness

end FX1PolyAudit
