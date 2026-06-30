import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextSyntheticInfinityCategory

/-! # FX1PolyAudit/.../ContextSyntheticInfinityCategory — zero-axiom gate for context-33

Per-declaration zero-axiom gate for `context-33`'s deliverable
(`FX1Poly/Tier0/Context/ContextSyntheticInfinityCategory.lean`): the context universe object as a SYNTHETIC
∞-CATEGORY (Riehl–Shulman) — a SEGAL structure (composable pairs of directed homs have a contractible type of
composites) plus REZK-COMPLETENESS (isomorphisms are exactly identity paths).  Structure eta + the strict
category laws of `composeHom`, the Segal condition (contractibility, for every `RawCategory`), directed isos +
the comparison `idToDirectedIso` + Rezk-completeness with the zero-axiom discrete witness, the packaged
synthetic ∞-category with its discrete capstone witness, and the decidable-classification instance.  The full
homotopy-coherent synthetic ∞-category (which needs funext) is the honest `×type` deferral (`= false`); the
Core table-native row is the honest cross-axis sibling (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Structure eta + the strict category laws (Segal composition coherence)
#assert_no_axioms FX1Poly.Tier0.DirectedCategoryHom.ext
#assert_no_axioms FX1Poly.Tier0.directedComposition_assoc
#assert_no_axioms FX1Poly.Tier0.directedComposition_identityLeft
#assert_no_axioms FX1Poly.Tier0.directedComposition_identityRight

-- Contractibility + the Segal condition
#assert_no_axioms FX1Poly.Tier0.IsContractibleType
#assert_no_axioms FX1Poly.Tier0.SegalComposite
#assert_no_axioms FX1Poly.Tier0.RawCategory.segalComposite_isContractible

-- Directed isomorphisms (the Rezk equivalences)
#assert_no_axioms FX1Poly.Tier0.DirectedHomIso
#assert_no_axioms FX1Poly.Tier0.DirectedHomIso.identityIso
#assert_no_axioms FX1Poly.Tier0.DirectedHomIso.symm
#assert_no_axioms FX1Poly.Tier0.DirectedHomIso.ext

-- The comparison map + Rezk-completeness with the discrete witness
#assert_no_axioms FX1Poly.Tier0.idToDirectedIso
#assert_no_axioms FX1Poly.Tier0.idToDirectedIso_refl
#assert_no_axioms FX1Poly.Tier0.IsRezkComplete
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_isRezkComplete

-- The packaged synthetic ∞-category + the discrete capstone witness
#assert_no_axioms FX1Poly.Tier0.IsSyntheticInfinityCategory
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_isSyntheticInfinityCategory

-- The decidable-classification witness
#assert_no_axioms FX1Poly.Tier0.DirectedHomIso.instDecidableEq

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Tier0.fxSyntheticInfinityCategory_hasStrictSegalStructure
#assert_no_axioms FX1Poly.Tier0.fxSyntheticInfinityCategory_hasRezkCompletenessAtDiscrete
#assert_no_axioms FX1Poly.Tier0.fxSyntheticInfinityCategory_hasFullSyntheticInfinityCategory
#assert_no_axioms FX1Poly.Tier0.fxSyntheticInfinityCategory_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_rezk_roundtrip_smoke
#assert_no_axioms FX1Poly.Tier0.discreteUniverseObject_segal_center_smoke

end FX1PolyAudit
