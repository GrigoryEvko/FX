import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.ContextMarkedComplicial

/-! # FX1PolyAudit/.../ContextMarkedComplicial — zero-axiom gate for context-36

Per-declaration zero-axiom gate for `context-36`'s deliverable
(`FX1Poly/Axis/Context/ContextMarkedComplicial.lean`): the MARKED / COMPLICIAL structure on the context
(∞,ω)-category — the context-axis mirror of `term-18`.  The dimension-1 equivalence marking
(`IsContextEquivalence`), the elementary stratification axioms (identities thin, thin closed under inverse +
composition), the saturation 2-out-of-3 (cancel-left / cancel-right), 2-triviality (the `Eq` 2-cell layer is
proof-irrelevant), the packaged marked context category + its canonical marking, and the bridge from
`context-33`'s directed isos.  The full Verity weak-complicial horn-filling (which needs Type-valued non-thin
higher cells) is the honest `×type` deferral (`= false`); the Core table-native row is the honest cross-axis
sibling (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The dimension-1 marking + the elementary stratification axioms
#assert_no_axioms FX1Poly.Axis.IsContextEquivalence
#assert_no_axioms FX1Poly.Axis.contextEquivalence_id
#assert_no_axioms FX1Poly.Axis.contextEquivalence_symm
#assert_no_axioms FX1Poly.Axis.contextEquivalence_comp

-- Saturation (2-out-of-3)
#assert_no_axioms FX1Poly.Axis.contextEquivalence_ofEq
#assert_no_axioms FX1Poly.Axis.contextEquivalence_cancelLeft
#assert_no_axioms FX1Poly.Axis.contextEquivalence_cancelRight

-- 2-triviality
#assert_no_axioms FX1Poly.Axis.contextOmega_twoTrivial

-- The packaged marked context category + canonical marking + the context-33 bridge
#assert_no_axioms FX1Poly.Axis.MarkedContextCategory
#assert_no_axioms FX1Poly.Axis.equivalenceMarking
#assert_no_axioms FX1Poly.Axis.DirectedHomIso.isContextEquivalence

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Axis.fxMarkedContextCategory_hasStrictMarking
#assert_no_axioms FX1Poly.Axis.fxMarkedContextCategory_hasSaturationTwoOutOfThree
#assert_no_axioms FX1Poly.Axis.fxMarkedContextCategory_hasTwoTriviality
#assert_no_axioms FX1Poly.Axis.fxMarkedContextCategory_hasFullComplicialHornFilling
#assert_no_axioms FX1Poly.Axis.fxMarkedContextCategory_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Axis.equivalenceMarking_thin_identity_smoke
#assert_no_axioms FX1Poly.Axis.directedHomIso_isThin_smoke

end FX1PolyAudit
