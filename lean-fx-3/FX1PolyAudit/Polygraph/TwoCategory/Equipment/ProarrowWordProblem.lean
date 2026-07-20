import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Equipment.ProarrowWordProblem

/-! # FX1PolyAudit.Polygraph.TwoCategory.Equipment.ProarrowWordProblem — zero-axiom gate (the free proarrow-equipment word problem)

Per-declaration zero-axiom gate for the free proarrow equipment: the `ProAtom` / `ProExpr` / `ProExprConv`
carriers and their constructors, the `Proarrow` structure, the `Nat.beq` / `Bool.and` micro-kit, the
companion/conjoint framing functors + their (contravariant) functoriality, the horizontal-monoid normal
form + the two-sided 1-cell word decision (`eqpProarrowConvSound` / `…Complete` / `…Refute`), the mates
transpose involution, the ground fires, and the two wall markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ProAtom
#assert_no_axioms FX1Poly.Polygraph.ProAtom.hgen
#assert_no_axioms FX1Poly.Polygraph.ProAtom.companion
#assert_no_axioms FX1Poly.Polygraph.ProAtom.conjoint
#assert_no_axioms FX1Poly.Polygraph.ProExpr
#assert_no_axioms FX1Poly.Polygraph.ProExpr.idPro
#assert_no_axioms FX1Poly.Polygraph.ProExpr.atom
#assert_no_axioms FX1Poly.Polygraph.ProExpr.hcomp
#assert_no_axioms FX1Poly.Polygraph.ProExprConv
#assert_no_axioms FX1Poly.Polygraph.ProExprConv.reflConv
#assert_no_axioms FX1Poly.Polygraph.ProExprConv.symmConv
#assert_no_axioms FX1Poly.Polygraph.ProExprConv.transConv
#assert_no_axioms FX1Poly.Polygraph.ProExprConv.hcompCongr
#assert_no_axioms FX1Poly.Polygraph.ProExprConv.hcompAssoc
#assert_no_axioms FX1Poly.Polygraph.ProExprConv.hcompIdLeft
#assert_no_axioms FX1Poly.Polygraph.ProExprConv.hcompIdRight
#assert_no_axioms FX1Poly.Polygraph.Proarrow
#assert_no_axioms FX1Poly.Polygraph.Proarrow.mk
#assert_no_axioms FX1Poly.Polygraph.eqpNatBeqRefl
#assert_no_axioms FX1Poly.Polygraph.eqpNatBeqEq
#assert_no_axioms FX1Poly.Polygraph.eqpBoolAndElim
#assert_no_axioms FX1Poly.Polygraph.eqpProAtomBeq
#assert_no_axioms FX1Poly.Polygraph.eqpProAtomBeqRefl
#assert_no_axioms FX1Poly.Polygraph.eqpProAtomBeqEq
#assert_no_axioms FX1Poly.Polygraph.eqpAppend
#assert_no_axioms FX1Poly.Polygraph.eqpAppendNil
#assert_no_axioms FX1Poly.Polygraph.eqpAppendAssoc
#assert_no_axioms FX1Poly.Polygraph.eqpProAtomListBeq
#assert_no_axioms FX1Poly.Polygraph.eqpProAtomListBeqRefl
#assert_no_axioms FX1Poly.Polygraph.eqpProAtomListBeqEq
#assert_no_axioms FX1Poly.Polygraph.eqpCompanionOfVertical
#assert_no_axioms FX1Poly.Polygraph.eqpConjointOfVertical
#assert_no_axioms FX1Poly.Polygraph.eqpCompanionNil
#assert_no_axioms FX1Poly.Polygraph.eqpConjointNil
#assert_no_axioms FX1Poly.Polygraph.eqpCompanionAppend
#assert_no_axioms FX1Poly.Polygraph.eqpConjointAppend
#assert_no_axioms FX1Poly.Polygraph.eqpIdentityProarrow
#assert_no_axioms FX1Poly.Polygraph.eqpDecideProarrowEq
#assert_no_axioms FX1Poly.Polygraph.eqpDecideProarrowEqSound
#assert_no_axioms FX1Poly.Polygraph.normalizeProExpr
#assert_no_axioms FX1Poly.Polygraph.eqpProExprConvNormEq
#assert_no_axioms FX1Poly.Polygraph.eqpProarrowConvSound
#assert_no_axioms FX1Poly.Polygraph.eqpAtomsToExpr
#assert_no_axioms FX1Poly.Polygraph.eqpAtomsToExprAppend
#assert_no_axioms FX1Poly.Polygraph.eqpExprConvAtomsToExprOfNorm
#assert_no_axioms FX1Poly.Polygraph.eqpProExprCompleteOfNormEq
#assert_no_axioms FX1Poly.Polygraph.eqpProarrowConvComplete
#assert_no_axioms FX1Poly.Polygraph.eqpProarrowConvRefute
#assert_no_axioms FX1Poly.Polygraph.eqpCompanionExprFunctorial
#assert_no_axioms FX1Poly.Polygraph.eqpConjointExprFunctorial
#assert_no_axioms FX1Poly.Polygraph.eqpMatesTransposeAtom
#assert_no_axioms FX1Poly.Polygraph.eqpMatesTransposeAtomInvol
#assert_no_axioms FX1Poly.Polygraph.eqpMatesTranspose
#assert_no_axioms FX1Poly.Polygraph.eqpMatesTransposeAppend
#assert_no_axioms FX1Poly.Polygraph.eqpMatesTransposeInvol
#assert_no_axioms FX1Poly.Polygraph.eqpFireCompanionTwoLetter
#assert_no_axioms FX1Poly.Polygraph.eqpFireConjointTwoLetterReversed
#assert_no_axioms FX1Poly.Polygraph.eqpFireDistinctWordsNotEqual
#assert_no_axioms FX1Poly.Polygraph.eqpFireMatesInvolConcrete
#assert_no_axioms FX1Poly.Polygraph.eqpFireIdentityComposeEqual
#assert_no_axioms FX1Poly.Polygraph.eqpFireMatesSwapSingleton
#assert_no_axioms FX1Poly.Polygraph.eqpHasFull2CellCoherence
#assert_no_axioms FX1Poly.Polygraph.eqpHasNonFreeCompanionExistence

end FX1PolyAudit
