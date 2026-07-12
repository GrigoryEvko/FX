import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFoldCapFreeScope

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFoldCapFreeScope — zero-axiom gate (r52)

Per-declaration zero-axiom gate for the BRAUER r52 corrected-fold cap-free scoping: the positionsFit guard machinery
(`maxAtomPosition`, `hasBoundaryRoomForPositions`), the scoped fold target (`BrauerExt5CorrectedFoldReachesCapFree`),
the free-vs-genuine relation architectural gap (`cupSlide_diagram_soundAtBoundaryOne`,
`cupSlide_diagram_notSoundAtBoundaryZero`, `not_brauerConvFree8_diagramInvariant`), the census-extension enumerators
(`capFreeGuardHoldsRealizeFailCount`, `withCapRepresentativeFailCount`), the cap-side defect autopsy
(`capSideDefect_atCapSlot0`, `capSideDefect_atCapSlot1`, `capSideDefect_atCapSlot2`), the structural
idempotence-from-realization corollary (`representativeIdempotent_ofDiagramEq`), the honesty markers, and the
machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `WellFounded.fix` — the guard
and census defs are structural over `List.filter`/`Nat.max`/`Nat.ble`, the architectural-gap and cap-side witnesses are
`decide`s over small concrete diagrams, and the idempotence corollary is the shipped diagram-only `congrArg`.
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.maxAtomPosition
#assert_no_axioms FX1Poly.Polygraph.hasBoundaryRoomForPositions
#assert_no_axioms FX1Poly.Polygraph.BrauerExt5CorrectedFoldReachesCapFree
#assert_no_axioms FX1Poly.Polygraph.cupSlide_diagram_soundAtBoundaryOne
#assert_no_axioms FX1Poly.Polygraph.cupSlide_diagram_notSoundAtBoundaryZero
#assert_no_axioms FX1Poly.Polygraph.not_brauerConvFree8_diagramInvariant
#assert_no_axioms FX1Poly.Polygraph.capFreeGuardHoldsRealizeFailCount
#assert_no_axioms FX1Poly.Polygraph.withCapRepresentativeFailCount
#assert_no_axioms FX1Poly.Polygraph.capSideDefect_atCapSlot0
#assert_no_axioms FX1Poly.Polygraph.capSideDefect_atCapSlot1
#assert_no_axioms FX1Poly.Polygraph.capSideDefect_atCapSlot2
#assert_no_axioms FX1Poly.Polygraph.representativeIdempotent_ofDiagramEq
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedFoldCapFreeScope
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedFoldCapFreeDischarged
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_correctedFoldCapFreeScopeTerminalState

end FX1PolyAudit
