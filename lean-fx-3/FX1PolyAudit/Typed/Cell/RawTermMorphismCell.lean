import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Cell.RawTermMorphismCell

/-! # FX1PolyAudit.Typed.Cell.RawTermMorphismCell — zero-axiom gate (mirror shard)

The raw-term morphism action (`LiftsRaw` + `ActsOnRawTermVar`, i.e. `fold`'s two
constraints) and the closed-cell computations every morphism satisfies. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.RawTerm.applyMorphism
#assert_no_axioms FX1Poly.Typed.RawTermChildren.applyMorphism
#assert_no_axioms FX1Poly.Typed.rename_eq_applyMorphism
#assert_no_axioms FX1Poly.Typed.subst_eq_applyMorphism
#assert_no_axioms FX1Poly.Typed.renameChildren_eq_applyMorphism
#assert_no_axioms FX1Poly.Typed.substChildren_eq_applyMorphism
#assert_no_axioms FX1Poly.Typed.applyMorphism_universeCodeCell
#assert_no_axioms FX1Poly.Typed.applyMorphism_emptyTypeCell

end FX1PolyAudit
