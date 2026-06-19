import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.LexJointRowSN

/-! # FX1PolyAudit/AuditLexJointRowSN — zero-axiom gate for the lexicographic joint SN

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/LexJointRowSN.lean`: the generic
`lex(primaryMeasure, size)` combinator (`wellFounded_of_lexMeasureStrictlyDecreasing`, riding the
propext-clean `wellFounded_of_lexPairMeasure`), the load-bearing compatibility fact
(`UnivalenceRowStep.preservesProductFormerCount`), the mixed union (`UnifiedDefinitionalRowStep`), its
per-step lex decrease (`unifiedDefinitionalRow_decreasesLex`), the headline JOINT SN across the size axis
(`unifiedDefinitionalRow_wellFounded`) and accessibility, the both-directions non-vacuity, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — the first instantiated joint SN spanning a size-SHRINKING and a size-GROWING
oriented row under ONE lexicographic type-complexity measure. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.wellFounded_of_lexMeasureStrictlyDecreasing
#assert_no_axioms FX1Poly.Core.UnivalenceRowStep.preservesProductFormerCount
#assert_no_axioms FX1Poly.Core.UnifiedDefinitionalRowStep
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalRow_decreasesLex
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalRow_wellFounded
#assert_no_axioms FX1Poly.Core.UnifiedDefinitionalRowStep.isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalRow_containsShrinking
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalRow_containsGrowing
#assert_no_axioms FX1Poly.Core.fxLexJointSN_mixesShrinkingAndGrowing
#assert_no_axioms FX1Poly.Core.fxLexJointSN_composesViaFormerCountPreservation
#assert_no_axioms FX1Poly.Core.fxLexJointSN_isJointWithBetaIota

end FX1PolyAudit
