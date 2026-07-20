import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.LinearLogic.MultiplicativeProofNet

/-! # FX1PolyAudit.Polygraph.LinearLogic.MultiplicativeProofNet — zero-axiom gate (unit-free MLL + Danos–Regnier)

Per-declaration zero-axiom gate for the unit-free MLL proof-structure layer and the Danos–Regnier correctness
decision: the formula / link / proof-structure syntax with computing `DecidableEq` and the involutive `dual`; the
inlined fuel-bounded union-find; the switching enumeration and the `mnlDecideProofNetCorrect` decision; the
sequent-proof type, its desugaring, and the axiom-rule soundness base; the honest wall markers; and the ground
fires.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- T1: unit-free MLL formula syntax + duality
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllFormula
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllFormula.atom
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllFormula.tensor
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllFormula.par
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.instDecidableEqMllFormula
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllFormula.dual
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllFormula.dual_dual

-- T1: link + proof-structure syntax + well-formedness
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllLink
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllLink.axiomLink
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllLink.cutLink
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllLink.tensorLink
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllLink.parLink
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.instDecidableEqMllLink
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllProofStructure
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllProofStructure.mk
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.instDecidableEqMllProofStructure
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllLink.isInRange
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllProofStructure.isWellFormed

-- the fuel-bounded union-find
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlParentOf
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlRootFuel
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlRootOf
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlIsSameComponent
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlJoin

-- T2: the switching graph + the DR decision
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlFixedEdges
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlSwitchingEdges
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlCountParLinks
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlAllSwitchings
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlAllSwitchings_ne_nil
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllDrState
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllDrState.mk
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlAcyclicStep
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlRunAcyclic
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlIsFullyConnected
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlSwitchingIsCorrect
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlDecideProofNetCorrect

-- T3: sequent proofs, desugaring, soundness base, wall markers
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllSequentProof
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllSequentProof.axiomRule
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllSequentProof.parRule
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllSequentProof.tensorRule
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllSequentProof.cutRule
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.MllLink.shiftBy
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlShiftNatList
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlDesugarAux
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlDesugar
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlAxiomRuleDesugarsToCorrectNet
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlHasFullSoundnessProof
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlHasSequentialization

-- T4: the ground fires
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlSingleAxiomNet
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlParNet
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlCyclicTensorNet
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlDisconnectedNet
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlSingleAxiomNet_isCorrect
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlParNet_isCorrect
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlCyclicTensorNet_isNotCorrect
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlDisconnectedNet_isNotCorrect
#assert_no_axioms FX1Poly.Polygraph.LinearLogic.mnlParProofDesugarsToCorrectNet

end FX1PolyAudit
