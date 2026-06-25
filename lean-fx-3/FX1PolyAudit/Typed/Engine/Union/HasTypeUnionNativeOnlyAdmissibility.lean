import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility

/-! # FX1PolyAudit/AuditHasTypeUnionNativeOnlyAdmissibility — TYTAB-2 ADMIT headline audit shard

Per-declaration zero-axiom gate for host-engine admissibility: every host `HasTypeDescPi` derivation (and,
via the inverse, every `HasTypeUnion` derivation) reflects into the `ofGrown`-free `HasTypeUnionNativeOnly`
judgment — so `ofGrown` is provably redundant.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.DescTelescopeNativeOnly
#assert_no_axioms FX1Poly.Typed.cumulativeFormationNativeOnlyPremiseToObligations
#assert_no_axioms FX1Poly.Typed.nativeOnlyCumulativeFormerCloses
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.toNativeOnly
#assert_no_axioms FX1Poly.Typed.DescTelescope.toNativeOnlyTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.toNativeOnly
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.toNativeOnlyTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.toNativeOnly

-- The packaged equivalence `HasTypeUnion ↔ HasTypeUnionNativeOnly` — `ofGrown` is provably redundant.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.iff_nativeOnly

end FX1PolyAudit
