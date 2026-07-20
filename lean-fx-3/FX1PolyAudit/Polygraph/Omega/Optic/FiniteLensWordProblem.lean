import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Optic.FiniteLensWordProblem

/-! # FX1PolyAudit/Polygraph/Omega/Optic/FiniteLensWordProblem — zero-axiom gate
    (WP-OPTIC-POLY: the finite-lens get/put table word problem)

Per-declaration zero-axiom gate for the concrete-lens word-problem kit (`lgp`): the
structural micro-kit (indexing `lgpListGet`, length, Boolean `<` `lgpBlt`, bounded `forall`
`lgpBoundedAll`, cons-only `lgpAppend` / `lgpMap` / range / table builders), the lens
carrier `LgpLens` with `lgpGet` / `lgpPut` / `lgpIsWellFormed`, the identity lens and
composition `lgpLensCompose`, the three lens laws as decidable Booleans
(`lgpIsGetPutLawful` / `lgpIsPutGetLawful` / `lgpIsPutPutLawful`) with the general soundness
bridge `lgpBoundedAllSound` -> `lgpGetPutSound`, the word decision `lgpDecideLensConv`, the
congruence `LgpLensConv` with BOTH halves (soundness `lgpLensConvDecides`, completeness
`lgpDecideLensConvComplete`, refutation `lgpLensConvRefute`), the three wall markers, and the
ground fires.

The general profunctor/coend optics (`lgpHasGeneralOpticCompleteness = false`) and the Poly
double-category interchange (`lgpHasPolyDoubleCoherence = false`) are WALLED with concrete
obstructions; lawful-lens completeness (`lgpHasLawfulLensCompleteness = false`) is held as an
owner-false census target.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Optic.lgpListGet
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpNatListLength
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpBlt
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpEntriesBelow
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpBoundedAll
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpAppend
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpMap
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpRangeFrom
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpRange
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpBuildRowFrom
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpBuildTableFrom
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpBuildTable
#assert_no_axioms FX1Poly.Polygraph.Optic.LgpLens
#assert_no_axioms FX1Poly.Polygraph.Optic.LgpLens.mk
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpGet
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpPut
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpIsWellFormed
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpIdentityLens
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpLensCompose
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpIsGetPutLawful
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpIsPutGetLawful
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpIsPutPutLawful
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpBltZeroRight
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpBltSuccCases
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpBoundedAllSound
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpGetPutSound
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpDecideLensConv
#assert_no_axioms FX1Poly.Polygraph.Optic.LgpLensConv
#assert_no_axioms FX1Poly.Polygraph.Optic.LgpLensConv.ofTableEq
#assert_no_axioms FX1Poly.Polygraph.Optic.LgpLensConv.symm
#assert_no_axioms FX1Poly.Polygraph.Optic.LgpLensConv.trans
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpLensConvRefl
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpLensConvSound
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpLensConvDecides
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpDecideLensConvComplete
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpLensConvRefute
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpHasGeneralOpticCompleteness
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpHasPolyDoubleCoherence
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpHasLawfulLensCompleteness
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireIdentityGetPut
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireIdentityPutGet
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireIdentityPutPut
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireIdentityGetPutThree
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireIdentityWellFormed
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpBadLens
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireBadPutGet
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpSwapLens
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireComposeIdentityDecides
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireComposeIdentityConv
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireDistinctDecides
#assert_no_axioms FX1Poly.Polygraph.Optic.lgpFireDistinctNotConv

end FX1PolyAudit
