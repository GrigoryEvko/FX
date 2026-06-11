import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.HasTypeNativeUnionInversion

/-! # FX1PolyAudit/AuditNativeUnionInversion — NATIVE-37 audit shard (the FIRST eliminations over the
    native union: the inversion substrate + the union-wide affine rejection)

Per-declaration zero-axiom gate for NATIVE-37 part 1: the host pathLam/natSucc head refutations (the Rung-103
missing lemma plus its data-intro companion), the three engine-embedding subject-head exclusions, the in-file
recursive-eliminator row inverter, the four representative per-head inversions over `HasTypeNativeUnion`
(`invertAtPathLamHead` / `invertAtLamHead` / `invertAtNatElimHead` / `invertAtNatSuccHead`), the union-wide
affine rejection (`unionRejectsAffineDoubleUse`), and the inversion coverage record / witness.  Every declaration
below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## (2) The host head refutations -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pathLamCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.natSuccCellHasNoTyping

/-! ## The engine-embedding subject-head exclusions -/

#assert_no_axioms FX1Poly.Typed.baseTypeSubjectHeadExcluded
#assert_no_axioms FX1Poly.Typed.dataIntroSubjectHeadExcluded
#assert_no_axioms FX1Poly.Typed.termIndexedFormerSubjectHeadExcluded

/-! ## The in-file recursive-eliminator row inverter -/

#assert_no_axioms FX1Poly.Typed.nativeRecursiveElimRuleOf_isNatElimOrNatRec

/-! ## (1) The four representative per-head inversions over the union -/

#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtPathLamHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtLamHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtNatElimHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtNatSuccHead

/-! ## (3) ★ The union-wide affine rejection -/

#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.unionRejectsAffineDoubleUse

/-! ## (5) Coverage record + witness -/

#assert_no_axioms FX1Poly.Typed.NativeUnionInversionCoverage
#assert_no_axioms FX1Poly.Typed.nativeUnionInversionCoverageWitness

end FX1PolyAudit
