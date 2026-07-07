import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.HostAdmissibility.OfGrownArmReflection

/-! # FX1PolyAudit.Typed.Metatheory.HostAdmissibility.OfGrownArmReflection — zero-axiom gate (Retirement Brick 1)

The retired-`ofGrown`-arm reflection capstone and its per-arm coverage gate.  Every declaration below
must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.ofGrownReflected
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.ofGrownFormationReflected
#assert_no_axioms FX1Poly.Typed.OfGrownArmReflectionCoverage
#assert_no_axioms FX1Poly.Typed.ofGrownArmReflectionCoverageWitness

end FX1PolyAudit
