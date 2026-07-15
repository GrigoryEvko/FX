import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Level.LevelExprSimplify

/-! # FX1PolyAudit.Axis.Type.Level.LevelExprSimplify07

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Level.LevelExprSimplify` (part 7 of 7).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.length_append

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.incrementOffsets_length

#assert_no_axioms FX1Poly.Universe.LevelExpr.toMaxPlusForm_varOffsets_length_le_size

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariable_length

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariable_length

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFrom_length_le

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacent_length_le

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsets_length_le

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize_toMaxPlusForm_varOffsets_length_le_size

#assert_no_axioms FX1Poly.Universe.LevelExpr.decidableOccursIn

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps_le_length

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFromSteps

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFromSteps_le_length

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacentSteps

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacentSteps_le_length

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariableSteps

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.mulSelf_add_self_le_succ_mul_succ

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariableSteps_le

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsetsSteps

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsetsSteps_le

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsetsSteps_toMaxPlusForm_le_size

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffsetSteps

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffsetSteps_eq_length

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalizeSteps

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalizeSteps_toMaxPlusForm_le_size

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffsetSteps_smoke_twoEntries

#assert_no_axioms FX1Poly.Universe.LevelExpr.decideDenoteEquivSteps

#assert_no_axioms FX1Poly.Universe.LevelExpr.decideDenoteEquivSteps_le_size

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps_smoke_empty

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps_smoke_stopAtHead

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps_smoke_walkToEnd

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariableSteps_smoke_reversedPair

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariableSteps_smoke_reversedTriple

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFromSteps_smoke_fuseThenSkip

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsetsSteps_smoke_reversedPair

end FX1PolyAudit
