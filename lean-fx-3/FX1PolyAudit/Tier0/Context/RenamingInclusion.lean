import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.RenamingInclusion

/-! # FX1PolyAudit/AuditTier0ContextInclusion — zero-axiom gate for the renaming ⊂ subst inclusion

Per-declaration zero-axiom gate for `context-1`
(`FX1Poly/Tier0/Context/RenamingInclusion.lean`): the variable-term inclusion
`RenamingVec.toSubstVec`, the two PROVED functor laws (identity + composition),
the assembled inclusion functor `renamingInclusion`, and its identification with
the context-axis bundle's two categories `fxContextAxis_inclusion`.  Also gates
the generic `RawFunctor` API (promoted to `RepresentableMapCategory`, the
canonical home this inclusion is the leading consumer of).  Every declaration
below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The generic functor + its category structure (promoted to `RepresentableMapCategory`).
#assert_no_axioms FX1Poly.Polygraph.RawFunctor.identity
#assert_no_axioms FX1Poly.Polygraph.RawFunctor.compose
#assert_no_axioms FX1Poly.Polygraph.RawFunctor.identity_compose
#assert_no_axioms FX1Poly.Polygraph.RawFunctor.compose_identity
#assert_no_axioms FX1Poly.Polygraph.RawFunctor.compose_assoc

#assert_no_axioms FX1Poly.Tier0.RenamingVec.toSubstVec
#assert_no_axioms FX1Poly.Tier0.RenamingVec.toSubstVec_lookup
#assert_no_axioms FX1Poly.Tier0.RenamingVec.toSubstVec_identity
#assert_no_axioms FX1Poly.Tier0.RenamingVec.toSubstVec_compose
#assert_no_axioms FX1Poly.Tier0.renamingInclusion
#assert_no_axioms FX1Poly.Tier0.fxContextAxis_inclusion

end FX1PolyAudit
