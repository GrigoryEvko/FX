import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstUnionTyped

/-! # FX1PolyAudit.Typed.Engine.Union.HasTypeUnionSubstUnionTyped — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped.cons
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped.consTwice
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped
-- ★ A1-CONJUNCT-WIRE (#1829): the cons/fibrant single- and two-substitution accessibility preservers (the
-- lock-free leaf-lemma `.2` dischargers the substituent file consumes).
#assert_no_axioms FX1Poly.Typed.substSingletonAccessibilityPreserved
#assert_no_axioms FX1Poly.Typed.substPairAccessibilityPreserved

end FX1PolyAudit
