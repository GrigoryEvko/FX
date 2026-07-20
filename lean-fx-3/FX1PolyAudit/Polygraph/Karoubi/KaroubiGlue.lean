import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Karoubi.KaroubiGlue

/-! # FX1PolyAudit/Polygraph/Karoubi/KaroubiGlue — zero-axiom gate

Per-declaration zero-axiom gate for WP-GLUE: the Eckmann–Hilton datum and its
constructor, the collapse theorems (`opsCoincide`, `medial`, commutativity,
associativity), the natural-number witness, the own cons-only word `kgwAppend`
with its identity/associativity laws, the Karoubi object/morphism carriers and
their constructors, the sandwiched normal form, left/right absorption, identity
and composition, the `KarConv` congruence with every constructor, the soundness
lemmas, the decision `kgwDecideConv` with its convertible-decides-true bridge and
the refutation half, and the two `false` wall markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.EckmannHiltonData
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.EckmannHiltonData.mk
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwOpsCoincide
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwMedial
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwOpIsCommutative
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwOpIsAssociative
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwNatAddInterchange
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwNatAddEH
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwAppend
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwNilAppend
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwAppendNil
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwAppendAssoc
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarObject
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarObject.mk
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarMor
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarMor.mk
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwNormalForm
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwLeftAbsorb
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwRightAbsorb
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwIdentity
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwCompose
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwDecideConv
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwDecideConvEq
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarConv
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarConv.refl
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarConv.symm
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarConv.trans
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarConv.leftIdentity
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarConv.rightIdentity
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarConv.associativity
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarConv.congLeft
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.KarConv.congRight
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwLeftIdentitySound
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwRightIdentitySound
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwAssociativitySound
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwKarConvSound
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwDecideConvOfKarConv
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwNotKarConvOfDecideFalse
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwHasGeneralKaroubiSplitting
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwHasDeloopingTower
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwEmptyObject
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwSampleMor
#assert_no_axioms FX1Poly.Polygraph.KaroubiGlue.kgwOtherMor

end FX1PolyAudit
