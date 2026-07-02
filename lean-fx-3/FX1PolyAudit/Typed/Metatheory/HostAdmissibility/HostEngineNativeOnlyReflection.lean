import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.HostAdmissibility.HostEngineNativeOnlyReflection

/-! # FX1PolyAudit.Typed.Metatheory.HostAdmissibility.HostEngineNativeOnlyReflection — zero-axiom gate (B0-b relocation)

The host-engine → native-only reflections relocated out of `HasTypeUnionNativeOnlyAdmissibility` so the union
core no longer imports the grown engine.  Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.DescTelescopeNativeOnly
#assert_no_axioms FX1Poly.Typed.cumulativeFormationNativeOnlyPremiseToObligations
#assert_no_axioms FX1Poly.Typed.nativeOnlyCumulativeFormerCloses
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.toNativeOnly
#assert_no_axioms FX1Poly.Typed.DescTelescope.toNativeOnlyTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.toNativeOnly
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.toNativeOnlyTelescope

end FX1PolyAudit
