import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescUntwistAbsorbGenuineArrival

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescUntwistAbsorbGenuineArrival — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER genuine untwist-absorb arrival: the genuine arrival provider that ABSORBS
the on-leg crossing (`outcomeUntwistAbsorbArrival`), its reduced-result projector, the STRUCTURAL strict crossing-count
drop (`outcomeUntwistAbsorbArrival_reduces`), the type-level genuine-reduction bundle (`GenuineCupArrival` +
`genuineUntwistAbsorbArrival`), the before/after exemplar pins (genuine result vs reflexive input, strict `2 < 3` beat),
the honest wall pin (untwist arm only; every survivor has `crossingCount ≥ 2`), the honesty marker, and the machine-checked
terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the strict drop is the shipped
fold homomorphism `crossingCount_append` (never `rfl`-hope on a generic word), the arrival carries the shipped
`cupUntwistFree8_clean` whiskered (no opaque transport), and the concrete pins use `rfl` / `decide` over `Nat.decLt`
(no `WellFounded.fix` / `termination_by`).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.outcomeUntwistAbsorbArrival
#assert_no_axioms FX1Poly.Polygraph.outcomeUntwistAbsorbArrival_resultWord
#assert_no_axioms FX1Poly.Polygraph.outcomeUntwistAbsorbArrival_reduces
#assert_no_axioms FX1Poly.Polygraph.GenuineCupArrival
#assert_no_axioms FX1Poly.Polygraph.genuineUntwistAbsorbArrival
#assert_no_axioms FX1Poly.Polygraph.untwistAbsorbResultWord
#assert_no_axioms FX1Poly.Polygraph.reflexiveArrivalKeepsInput
#assert_no_axioms FX1Poly.Polygraph.untwistAbsorbStrictlyBelowReflexive
#assert_no_axioms FX1Poly.Polygraph.untwistAbsorbExemplarDrops
#assert_no_axioms FX1Poly.Polygraph.crossingLeftArmIsNotUntwistShape
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasUntwistAbsorbGenuineArrival
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_untwistAbsorbGenuineArrivalTerminalState

end FX1PolyAudit
