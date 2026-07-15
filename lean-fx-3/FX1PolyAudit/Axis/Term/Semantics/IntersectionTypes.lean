import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Semantics.IntersectionTypes

/-! # FX1PolyAudit/AuditAxisTermIntersectionTypes — zero-axiom gate for term-22 (intersection types)

Per-declaration zero-axiom gate for `FX1Poly/Axis/Term/Semantics/IntersectionTypes.lean`: the BCD
intersection-type algebra (`IntersectionType` / `Subtype` / `omega_isTop` / `inter_isGreatestLowerBound` /
`inter_commutative` / `inter_idempotent`), filters (`IsFilter` / `principalFilter` / `omegaFilter` + the
least-filter / antitone lemmas), and the ω-complete filter model (`FilterBelow` / `GeneratedFilter` /
`filterSup` / `filterSup_isUpperBound` / `filterSup_isLeast`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Intersection types + BCD subtyping (meet-semilattice with top)
#assert_no_axioms FX1Poly.Core.IntersectionType
#assert_no_axioms FX1Poly.Core.Subtype
#assert_no_axioms FX1Poly.Core.omega_isTop
#assert_no_axioms FX1Poly.Core.inter_isGreatestLowerBound
#assert_no_axioms FX1Poly.Core.inter_commutative
#assert_no_axioms FX1Poly.Core.inter_idempotent
#assert_no_axioms FX1Poly.Core.omega_isArrow
#assert_no_axioms FX1Poly.Core.arrow_distributesOverInter

-- Filters + the least filter + the order-reversing principal embedding
#assert_no_axioms FX1Poly.Core.IsFilter
#assert_no_axioms FX1Poly.Core.principalFilter
#assert_no_axioms FX1Poly.Core.principalFilter_isFilter
#assert_no_axioms FX1Poly.Core.omegaFilter
#assert_no_axioms FX1Poly.Core.omegaFilter_isFilter
#assert_no_axioms FX1Poly.Core.omegaFilter_isLeast
#assert_no_axioms FX1Poly.Core.principalFilter_antitone

-- The ω-complete filter model (the domain preorder)
#assert_no_axioms FX1Poly.Core.FilterBelow
#assert_no_axioms FX1Poly.Core.filterBelow_refl
#assert_no_axioms FX1Poly.Core.filterBelow_trans
#assert_no_axioms FX1Poly.Core.GeneratedFilter
#assert_no_axioms FX1Poly.Core.generatedFilter_isFilter
#assert_no_axioms FX1Poly.Core.generatedFilter_monotone
#assert_no_axioms FX1Poly.Core.filterSup
#assert_no_axioms FX1Poly.Core.filterSup_isUpperBound
#assert_no_axioms FX1Poly.Core.filterSup_isLeast

-- Filter application (the λ-model operation)
#assert_no_axioms FX1Poly.Core.filterApply
#assert_no_axioms FX1Poly.Core.filterApply_isFilter
#assert_no_axioms FX1Poly.Core.filterApply_monotone

end FX1PolyAudit
