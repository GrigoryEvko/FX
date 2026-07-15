import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Universe.UniverseFlag

/-! # FX1PolyAudit.Axis.Type.Universe.UniverseFlag

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Universe.UniverseFlag`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.UniverseFlag

#assert_no_axioms FX1Poly.Universe.UniverseFlag.standard_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.inaccessible_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.mahlo_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.superMahlo_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.nMahlo_zero_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.hyperMahlo_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.weaklyCompact_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.indescribable_zero_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.reflecting_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.vopenka_canonical

#assert_no_axioms FX1Poly.Universe.UniverseFlag.decEq_refl_standard

#assert_no_axioms FX1Poly.Universe.UniverseFlag.ctorCount

#assert_no_axioms FX1Poly.Universe.UniverseFlag.ctorCount_correct

end FX1PolyAudit
