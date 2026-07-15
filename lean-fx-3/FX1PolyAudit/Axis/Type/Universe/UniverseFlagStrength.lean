import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Universe.UniverseFlagStrength

/-! # FX1PolyAudit.Axis.Type.Universe.UniverseFlagStrength

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Universe.UniverseFlagStrength`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ### UNIVERSE-FLAG CONSISTENCY-STRENGTH TOTAL ORDER (the Setzer-Rathjen ladder, §11.8.2 / §3.16.3).
    The decidable total order on universe admission predicates: `strengthBand`/`strengthDegree`
    lexicographic rank (placing unbounded `nMahlo`/`indescribable` between fixed neighbours), its injective
    left inverse, the `LE` + `Decidable` instances, the four order laws, and the ladder non-degeneracy
    smokes.  Realizes the spec's "strictly stronger admission predicate" + "admission decidable in O(flag
    enum position)" as theorems. -/
#assert_no_axioms FX1Poly.Universe.UniverseFlag.strengthBand

#assert_no_axioms FX1Poly.Universe.UniverseFlag.strengthDegree

#assert_no_axioms FX1Poly.Universe.UniverseFlag.decodeStrengthRank_strength

#assert_no_axioms FX1Poly.Universe.UniverseFlag.eq_of_strengthRank

#assert_no_axioms FX1Poly.Universe.UniverseFlag.le

#assert_no_axioms FX1Poly.Universe.UniverseFlag.le_refl

#assert_no_axioms FX1Poly.Universe.UniverseFlag.le_trans

#assert_no_axioms FX1Poly.Universe.UniverseFlag.le_antisymm

#assert_no_axioms FX1Poly.Universe.UniverseFlag.le_total

#assert_no_axioms FX1Poly.Universe.UniverseFlag.standard_le_vopenka

#assert_no_axioms FX1Poly.Universe.UniverseFlag.not_vopenka_le_standard

#assert_no_axioms FX1Poly.Universe.UniverseFlag.nMahlo_le_hyperMahlo

#assert_no_axioms FX1Poly.Universe.UniverseFlag.nMahlo_mono

end FX1PolyAudit
