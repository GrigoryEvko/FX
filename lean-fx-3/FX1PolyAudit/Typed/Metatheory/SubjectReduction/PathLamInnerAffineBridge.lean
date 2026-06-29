import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamInnerAffineBridge

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.PathLamInnerAffineBridge — zero-axiom gate

The per-declaration `#assert_no_axioms` gate for the typed ⟹ inner-affine bridge: the three per-table CELL
lemmas (every introducer / eliminator / formed-type member cell satisfies `AllInnerPathLamAffine` under the
per-obligation IH, with the `pathLam` intro row reading its App-scaled affine `sideCondition`), the four
formation-family navigation helpers, and the headline `induction`-on-derivation bridge
`allInnerPathLamAffine_ofTyped` (a union-typed subject is inner-affine). -/

namespace FX1PolyAudit

-- The intro-table cell lemma (17 rows: 16 `.other`, the `pathLam` row `.pathLam`)
#assert_no_axioms FX1Poly.Typed.introCellAffine

-- The elim-table cell lemma (11 rows, all `.other`; cell-spine `List.Mem` navigation)
#assert_no_axioms FX1Poly.Typed.elimCellAffine

-- The formation-family navigation helpers (children-spine + `levels` threading)
#assert_no_axioms FX1Poly.Typed.flatPairChildrenInner
#assert_no_axioms FX1Poly.Typed.flatUnaryChildInner
#assert_no_axioms FX1Poly.Typed.cumulativeBinderChildrenInner
#assert_no_axioms FX1Poly.Typed.cumulativeUnaryChildInner

-- The formation-table cell lemma (19 generators across the 4 families; per-generator pin + nav)
#assert_no_axioms FX1Poly.Typed.formationCellAffine

-- ★ The headline: a union-typed subject is inner-affine (the A1-SUBST-OPEN subterm-typing leg)
#assert_no_axioms FX1Poly.Typed.allInnerPathLamAffine_ofTyped

end FX1PolyAudit
