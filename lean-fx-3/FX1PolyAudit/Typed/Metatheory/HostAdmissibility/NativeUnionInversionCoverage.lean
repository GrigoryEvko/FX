import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.HostAdmissibility.NativeUnionInversionCoverage

/-! # FX1PolyAudit.Typed.Metatheory.HostAdmissibility.NativeUnionInversionCoverage — zero-axiom gate (B0-b relocation)

The native-union inversion coverage gate relocated out of `HasTypeUnionInversion` so the union core no longer
imports the grown engine.  Free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.NativeUnionInversionCoverage
#assert_no_axioms FX1Poly.Typed.nativeUnionInversionCoverageWitness

end FX1PolyAudit
