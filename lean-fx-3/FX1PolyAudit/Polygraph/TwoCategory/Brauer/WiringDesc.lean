import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDesc

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDesc — zero-axiom gate (WP-BRAUER-1/2)

Per-declaration zero-axiom gate for the table-driven `WiringDesc` engine (WP-BRAUER-1) and the symmetric
self-dual Brauer / Temperley–Lieb + crossing presentation (WP-BRAUER-2): the wiring datum + its list helpers, the
single `stepWiring` step, the canonical generator wirings, the agreement smokes with the shipped `stepCup` /
`stepCap`, the Brauer diagram evaluator, the crossing transposition smoke, the relation set as a value, and the
per-relation diagram-soundness witnesses.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- WP-BRAUER-1: the wiring datum + list helpers
#assert_no_axioms FX1Poly.Polygraph.WiringDesc
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqWiringDesc
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt
#assert_no_axioms FX1Poly.Polygraph.natListRemoveManyAt

-- WP-BRAUER-1: the single wiring step
#assert_no_axioms FX1Poly.Polygraph.wiringEndpointNode
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs
#assert_no_axioms FX1Poly.Polygraph.stepWiring

-- WP-BRAUER-1: the canonical generator wirings
#assert_no_axioms FX1Poly.Polygraph.cupWiring
#assert_no_axioms FX1Poly.Polygraph.capWiring
#assert_no_axioms FX1Poly.Polygraph.crossingWiring
#assert_no_axioms FX1Poly.Polygraph.identityWiring

-- WP-BRAUER-1: agreement with the shipped steps
#assert_no_axioms FX1Poly.Polygraph.brauerSeed
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cupWiring_seed
#assert_no_axioms FX1Poly.Polygraph.stepWiring_capWiring_seed
#assert_no_axioms FX1Poly.Polygraph.stepWiring_capWiring_loop

-- WP-BRAUER-2: the Brauer diagram evaluator
#assert_no_axioms FX1Poly.Polygraph.BrauerAtom
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqBrauerAtom
#assert_no_axioms FX1Poly.Polygraph.stepBrauerAtom
#assert_no_axioms FX1Poly.Polygraph.processBrauer
#assert_no_axioms FX1Poly.Polygraph.brauerDiagramOf
#assert_no_axioms FX1Poly.Polygraph.cupAt
#assert_no_axioms FX1Poly.Polygraph.capAt
#assert_no_axioms FX1Poly.Polygraph.crossingAt
#assert_no_axioms FX1Poly.Polygraph.identityStrandAt

-- WP-BRAUER-1: the crossing captures the transposition
#assert_no_axioms FX1Poly.Polygraph.crossing_diagram
#assert_no_axioms FX1Poly.Polygraph.identity_pair_diagram

-- WP-BRAUER-2: the relations as data
#assert_no_axioms FX1Poly.Polygraph.BrauerRelation
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqBrauerRelation
#assert_no_axioms FX1Poly.Polygraph.snakeRelation
#assert_no_axioms FX1Poly.Polygraph.snakeMirrorRelation
#assert_no_axioms FX1Poly.Polygraph.crossingInvolutionRelation
#assert_no_axioms FX1Poly.Polygraph.yangBaxterLhsWord
#assert_no_axioms FX1Poly.Polygraph.yangBaxterRhsWord
#assert_no_axioms FX1Poly.Polygraph.yangBaxterRelation
#assert_no_axioms FX1Poly.Polygraph.capSlideRelation
#assert_no_axioms FX1Poly.Polygraph.brauerPresentation

-- WP-BRAUER-2: per-relation soundness witnesses (R3 via the staged single-step chain)
#assert_no_axioms FX1Poly.Polygraph.snake_diagram_sound
#assert_no_axioms FX1Poly.Polygraph.snakeMirror_diagram_sound
#assert_no_axioms FX1Poly.Polygraph.crossingInvolution_diagram_sound
#assert_no_axioms FX1Poly.Polygraph.capSlide_diagram_sound
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStateLeftOne
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStateLeftTwo
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStateLeftThree
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStateRightOne
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStateRightTwo
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStateRightThree
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStepLeftOne
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStepLeftTwo
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStepLeftThree
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStepRightOne
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStepRightTwo
#assert_no_axioms FX1Poly.Polygraph.yangBaxterStepRightThree
#assert_no_axioms FX1Poly.Polygraph.yangBaxterProcessLeft
#assert_no_axioms FX1Poly.Polygraph.yangBaxterProcessRight
#assert_no_axioms FX1Poly.Polygraph.yangBaxter_diagram_sound
#assert_no_axioms FX1Poly.Polygraph.brauerPresentation_allSound

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescEngine
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingGenerator
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerPresentation
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerSoundness
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerCompleteness

end FX1PolyAudit
