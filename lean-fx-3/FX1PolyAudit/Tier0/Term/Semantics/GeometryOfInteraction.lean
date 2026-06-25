import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Semantics.GeometryOfInteraction

/-! # FX1PolyAudit/AuditTier0TermGeometryOfInteraction — zero-axiom gate for term-23 (GoI token machine)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Semantics/GeometryOfInteraction.lean`: the token
machine (`TokenMachine` / `step_deterministic` / `IsHalted` / `execute` / `execute_succ`), the absorption
laws (`execute_halted` / `execute_succ_of_halted` / `reaches_stable`), the execution determinacy
(`Reaches` / `reaches_unique`), and the wire witness (`wireMachine` / `wireMachine_isHalted_zero` /
`wireMachine_runsToExit` / `wireMachine_reachesExit`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The token machine + deterministic step + fuel-bounded execution
#assert_no_axioms FX1Poly.Core.TokenMachine
#assert_no_axioms FX1Poly.Core.TokenMachine.step_deterministic
#assert_no_axioms FX1Poly.Core.TokenMachine.IsHalted
#assert_no_axioms FX1Poly.Core.TokenMachine.execute
#assert_no_axioms FX1Poly.Core.TokenMachine.execute_succ

-- The absorption / stability laws
#assert_no_axioms FX1Poly.Core.TokenMachine.execute_halted
#assert_no_axioms FX1Poly.Core.TokenMachine.execute_succ_of_halted
#assert_no_axioms FX1Poly.Core.TokenMachine.reaches_stable

-- Execution determinacy (the GoI denotation is a well-defined partial function)
#assert_no_axioms FX1Poly.Core.TokenMachine.Reaches
#assert_no_axioms FX1Poly.Core.TokenMachine.reaches_unique

-- Termination from a measure (the token trip is finite ⟹ execution is total)
#assert_no_axioms FX1Poly.Core.TokenMachine.haltsWithin
#assert_no_axioms FX1Poly.Core.TokenMachine.reachesOfMeasure
#assert_no_axioms FX1Poly.Core.TokenMachine.executeTotal_of_measure

-- The wire (axiom link) witness + its measure
#assert_no_axioms FX1Poly.Core.wireMachine
#assert_no_axioms FX1Poly.Core.wireMachine_isHalted_zero
#assert_no_axioms FX1Poly.Core.wireMachine_runsToExit
#assert_no_axioms FX1Poly.Core.wireMachine_reachesExit
#assert_no_axioms FX1Poly.Core.wireMachine_measureDecreases

end FX1PolyAudit
