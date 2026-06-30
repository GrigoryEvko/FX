import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextMarkedComplicial

/-! # FX1PolyAudit/.../ContextMarkedComplicial — zero-axiom gate for context-36

Per-declaration zero-axiom gate for `context-36`'s deliverable
(`FX1Poly/Tier0/Context/ContextMarkedComplicial.lean`): the MARKED / COMPLICIAL structure on the context
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
#assert_no_axioms FX1Poly.Tier0.IsContextEquivalence
#assert_no_axioms FX1Poly.Tier0.contextEquivalence_id
#assert_no_axioms FX1Poly.Tier0.contextEquivalence_symm
#assert_no_axioms FX1Poly.Tier0.contextEquivalence_comp

-- Saturation (2-out-of-3)
#assert_no_axioms FX1Poly.Tier0.contextEquivalence_ofEq
#assert_no_axioms FX1Poly.Tier0.contextEquivalence_cancelLeft
#assert_no_axioms FX1Poly.Tier0.contextEquivalence_cancelRight

-- 2-triviality
#assert_no_axioms FX1Poly.Tier0.contextOmega_twoTrivial

-- The packaged marked context category + canonical marking + the context-33 bridge
#assert_no_axioms FX1Poly.Tier0.MarkedContextCategory
#assert_no_axioms FX1Poly.Tier0.equivalenceMarking
#assert_no_axioms FX1Poly.Tier0.DirectedHomIso.isContextEquivalence

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Tier0.fxMarkedContextCategory_hasStrictMarking
#assert_no_axioms FX1Poly.Tier0.fxMarkedContextCategory_hasSaturationTwoOutOfThree
#assert_no_axioms FX1Poly.Tier0.fxMarkedContextCategory_hasTwoTriviality
#assert_no_axioms FX1Poly.Tier0.fxMarkedContextCategory_hasFullComplicialHornFilling
#assert_no_axioms FX1Poly.Tier0.fxMarkedContextCategory_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Tier0.equivalenceMarking_thin_identity_smoke
#assert_no_axioms FX1Poly.Tier0.directedHomIso_isThin_smoke

end FX1PolyAudit
