import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.PsContextTyped

/-! # FX1PolyAudit.Polygraph.Omega.PsContextTypedAudit — zero-axiom gate for the typed ps-telescope
(OMEGA-6 r2, B1).

Per-declaration `#assert_no_axioms` on the boundary-type language (`teleTypeDim` / `teleTypeBeq` /
`teleTypeWellScoped` / `telescopeLookup` / `teleTypeOptionBeq` / `teleTypeEndpointsTyped` /
`telescopeWellFormedFrom` / `telescopeWellFormed`), the de Bruijn-LEVEL elaborator (`extendFocus` /
`dropFocus` / `elaboratePsContext` / `telescopeOf` / `psTypedCheck`), the erasure fibre lemma
(`teleTypeDim_eq_zero`), THE ERASURE COMMUTING LEMMA (`elaborate_focusDim_eq_psFocus` +
`psTypedCheck_implies_psContextCheck` + the honest converse `psContextCheck_implies_psTypedCheck`), and the
four telescope non-vacuity witnesses (disk / horizontal-composite typed checks, dangling / underflow typed
rejections, both well-formedness witnesses, both commuting-lemma witnesses). -/

namespace FX1PolyAudit

-- PsContextTyped.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.teleTypeDim
#assert_no_axioms FX1Poly.Polygraph.Omega.teleTypeBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.teleTypeWellScoped
#assert_no_axioms FX1Poly.Polygraph.Omega.telescopeLookup
#assert_no_axioms FX1Poly.Polygraph.Omega.teleTypeOptionBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.teleTypeEndpointsTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.telescopeWellFormedFrom
#assert_no_axioms FX1Poly.Polygraph.Omega.telescopeWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.extendFocus
#assert_no_axioms FX1Poly.Polygraph.Omega.dropFocus
#assert_no_axioms FX1Poly.Polygraph.Omega.elaboratePsContext
#assert_no_axioms FX1Poly.Polygraph.Omega.telescopeOf
#assert_no_axioms FX1Poly.Polygraph.Omega.psTypedCheck
#assert_no_axioms FX1Poly.Polygraph.Omega.teleTypeDim_eq_zero
#assert_no_axioms FX1Poly.Polygraph.Omega.elaborate_focusDim_eq_psFocus
#assert_no_axioms FX1Poly.Polygraph.Omega.psTypedCheck_implies_psContextCheck
#assert_no_axioms FX1Poly.Polygraph.Omega.psContextCheck_implies_psTypedCheck
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobeTelescope
#assert_no_axioms FX1Poly.Polygraph.Omega.horizontalCompositeTelescope
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobePsContext_psTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.horizontalCompositePsContext_psTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.danglingPsContext_psTypedFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.underflowPsContext_psTypedFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobeTelescope_wellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.horizontalCompositeTelescope_wellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobe_typed_implies_untyped
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobe_untyped_implies_typed

end FX1PolyAudit
