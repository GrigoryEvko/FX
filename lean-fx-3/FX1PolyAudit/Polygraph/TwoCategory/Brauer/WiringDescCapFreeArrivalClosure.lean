import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCapFreeArrivalClosure

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCapFreeArrivalClosure — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER cap-free arrival closure: the cap-free-right lemma
(`capFreeRight_of_hasNoCap`), the generic cap-free arrival provider (`outcomeCapFreeArrival`), the result-word projector,
the cap-free-stripped driver (`flatRegionDriveArrivalStripped`), the four-class fires + fates, the r47 census
subsumption, the out-of-scope guard, the honest reflexive-not-canonical wall pin, the two honesty markers, and the
machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the cap-free-right lemma is a
STRUCTURAL recursion whose leading-cap contradiction is Bool/Nat noConfusion via `nomatch` (never `Nat.succ_ne_zero`),
the arrival provider uses the reflexive `BrauerConvFree8` (no opaque transport), and the driver is a STRUCTURAL top-level
match + `Nat.beq` enum + dependent-if over the shipped fuel driver (no `WellFounded.fix` / `termination_by`).  Registered
in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capFreeRight_of_hasNoCap
#assert_no_axioms FX1Poly.Polygraph.outcomeCapFreeArrival
#assert_no_axioms FX1Poly.Polygraph.RegionCupOutcome.resultWord
#assert_no_axioms FX1Poly.Polygraph.flatRegionDriveArrivalStripped
#assert_no_axioms FX1Poly.Polygraph.capFreeArrivalFiresOnFourClasses
#assert_no_axioms FX1Poly.Polygraph.capFreeArrivalFates
#assert_no_axioms FX1Poly.Polygraph.capFreeArrivalSubsumesR47Census
#assert_no_axioms FX1Poly.Polygraph.capFreeArrivalOutOfScopeStaysNone
#assert_no_axioms FX1Poly.Polygraph.flatRegionDriveArrivalReflexiveNotCanonical
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCapFreeArrivalClosure
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCanonicalCapFreeSink
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_capFreeArrivalClosureTerminalState

end FX1PolyAudit
