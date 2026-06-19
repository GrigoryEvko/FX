import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.LexMeasureTowerSN

/-! # FX1PolyAudit/AuditLexMeasureTowerSN — zero-axiom gate for the n-level lexicographic measure tower

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/LexMeasureTowerSN.lean`: the generic
n-level lexicographic tower relation and its well-foundedness (`lexTowerRel` / `lexTowerRel_wellFounded`),
the `RawTerm` tower combinator (`wellFounded_of_lexMeasureTowerStrictlyDecreasing`), the joint-SN recovery
as the 2-level instance (`unifiedDefinitionalRow_wellFoundedViaTower`), the depth witnesses, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — the n-ary lexicographic generalization, riding the propext-clean
`LexPair.isWellFounded` by structural list induction. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.lexTowerRel
#assert_no_axioms FX1Poly.Core.lexTowerRel_wellFounded
#assert_no_axioms FX1Poly.Core.wellFounded_of_lexMeasureTowerStrictlyDecreasing
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalRow_wellFoundedViaTower
#assert_no_axioms FX1Poly.Core.productFormerCountSizeTower_wellFounded
#assert_no_axioms FX1Poly.Core.sizeTower_wellFounded
#assert_no_axioms FX1Poly.Core.fxLexTower_isNAryGeneralization
#assert_no_axioms FX1Poly.Core.fxLexTower_requiresPerLevelPreservation

end FX1PolyAudit
