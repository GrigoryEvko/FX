import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommuteRefutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommuteRefutation — zero-axiom gate (mode-3 floor, parent residual refuted)

Per-declaration zero-axiom gate for the parent Godement PARTITION residual refuted as stated: the re-exhibited
adversarial witness (`refuteIdentityBase` / `refuteIdentityLeftRight` / `refuteNilBase` /
`refuteAdversarialState` / `refuteRedexState` / `refuteReductState`), the `.diagram` divergence
(`refute_diagram_differs`), the refutation (`not_arcGodementPartitionCommute` :
`¬ ArcGodementPartitionCommute adjunctionModeSignature`), and the honesty marker.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per key declaration — the
two are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in `AuditAll` beyond the parent's unified
registration. -/

namespace FX1PolyAudit

-- the re-exhibited adversarial witness
#assert_no_axioms FX1Poly.Polygraph.refuteIdentityBase
#assert_no_axioms FX1Poly.Polygraph.refuteIdentityLeftRight
#assert_no_axioms FX1Poly.Polygraph.refuteNilBase
#assert_no_axioms FX1Poly.Polygraph.refuteAdversarialState
#assert_no_axioms FX1Poly.Polygraph.refuteRedexState
#assert_no_axioms FX1Poly.Polygraph.refuteReductState

-- the diagram divergence + the refutation
#assert_no_axioms FX1Poly.Polygraph.refute_diagram_differs
#assert_no_axioms FX1Poly.Polygraph.not_arcGodementPartitionCommute

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPartitionCommuteRefutedAsStated

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.refuteRedexState
#print axioms FX1Poly.Polygraph.refuteReductState
#print axioms FX1Poly.Polygraph.refute_diagram_differs
#print axioms FX1Poly.Polygraph.not_arcGodementPartitionCommute

end FX1PolyAudit
