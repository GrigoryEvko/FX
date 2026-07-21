import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.PolInvGaloisConnection

/-! # FX1PolyAudit/ComputerAlgebra/Decision/PolInvGaloisConnection — zero-axiom gate

Per-declaration zero-axiom gate for the finite Pol-Inv Galois core: the Boolean-connective kit,
the bit-tuple/row/relation/function equality + membership layer, the `PigBoolRel` carrier, the
componentwise-preservation predicate `pigPreserves`, the `pigPol`/`pigInv` operators, the Galois
soundness / base-closure / antitonicity theorems, the pp-definability primitives, the capability
markers (two left `false`), and the ground fires.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `WellFounded.fix`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.pigBoolAndElim
#assert_no_axioms FX1Poly.ComputerAlgebra.pigBoolAndIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.pigBoolOrElim
#assert_no_axioms FX1Poly.ComputerAlgebra.pigBoolOrIntroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.pigBoolOrIntroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.pigTupleBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.pigTupleBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.pigTupleBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRowsBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRowsBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.PigBoolRel
#assert_no_axioms FX1Poly.ComputerAlgebra.PigBoolRel.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRowMem
#assert_no_axioms FX1Poly.ComputerAlgebra.pigAllRowsLen
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRelWellFormed
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRelBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRelBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRelMem
#assert_no_axioms FX1Poly.ComputerAlgebra.pigFuncBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.pigFuncBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.pigFuncMem
#assert_no_axioms FX1Poly.ComputerAlgebra.pigColumn
#assert_no_axioms FX1Poly.ComputerAlgebra.pigApplyOverCoords
#assert_no_axioms FX1Poly.ComputerAlgebra.pigApplyComponentwise
#assert_no_axioms FX1Poly.ComputerAlgebra.pigConsRowToAll
#assert_no_axioms FX1Poly.ComputerAlgebra.pigConsEachRow
#assert_no_axioms FX1Poly.ComputerAlgebra.pigChooseRows
#assert_no_axioms FX1Poly.ComputerAlgebra.pigCheckAllChoices
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPreserves
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPreservesAll
#assert_no_axioms FX1Poly.ComputerAlgebra.pigAllPreserve
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPreservesAllDropTail
#assert_no_axioms FX1Poly.ComputerAlgebra.pigAllPreserveDropTail
#assert_no_axioms FX1Poly.ComputerAlgebra.pigConsIf
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRelConsIf
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPol
#assert_no_axioms FX1Poly.ComputerAlgebra.pigInv
#assert_no_axioms FX1Poly.ComputerAlgebra.pigFuncMemConsIfElim
#assert_no_axioms FX1Poly.ComputerAlgebra.pigFuncMemConsIfIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRelMemConsIfElim
#assert_no_axioms FX1Poly.ComputerAlgebra.pigRelMemConsIfIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPolProducesPreservers
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPolSubsetBase
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPolKeepsPreserver
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPolAntitone
#assert_no_axioms FX1Poly.ComputerAlgebra.pigInvProducesInvariants
#assert_no_axioms FX1Poly.ComputerAlgebra.pigInvSubsetBase
#assert_no_axioms FX1Poly.ComputerAlgebra.pigInvKeepsInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.pigInvAntitone
#assert_no_axioms FX1Poly.ComputerAlgebra.pigConjKeep
#assert_no_axioms FX1Poly.ComputerAlgebra.pigIntersectRows
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPpConjoin
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPredecessor
#assert_no_axioms FX1Poly.ComputerAlgebra.pigDropCoord
#assert_no_axioms FX1Poly.ComputerAlgebra.pigProjectRows
#assert_no_axioms FX1Poly.ComputerAlgebra.pigPpProject
#assert_no_axioms FX1Poly.ComputerAlgebra.pigHasFinitePreservation
#assert_no_axioms FX1Poly.ComputerAlgebra.pigHasBoundedPolInv
#assert_no_axioms FX1Poly.ComputerAlgebra.pigHasGaloisInequalities
#assert_no_axioms FX1Poly.ComputerAlgebra.pigHasPolInvAntitone
#assert_no_axioms FX1Poly.ComputerAlgebra.pigHasFullGaloisCorrespondence
#assert_no_axioms FX1Poly.ComputerAlgebra.pigHasPpDefinabilityClosure
#assert_no_axioms FX1Poly.ComputerAlgebra.pigOrderRel
#assert_no_axioms FX1Poly.ComputerAlgebra.pigEqRel
#assert_no_axioms FX1Poly.ComputerAlgebra.pigFuncBase
#assert_no_axioms FX1Poly.ComputerAlgebra.pigOrderRelWellFormed
#assert_no_axioms FX1Poly.ComputerAlgebra.pigAndPreservesOrder
#assert_no_axioms FX1Poly.ComputerAlgebra.pigXorNotPreservesOrder
#assert_no_axioms FX1Poly.ComputerAlgebra.pigNegPreservesEquality
#assert_no_axioms FX1Poly.ComputerAlgebra.pigAndPreservesEquality
#assert_no_axioms FX1Poly.ComputerAlgebra.pigAndInPolInvSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.pigXorInPolEqAlone
#assert_no_axioms FX1Poly.ComputerAlgebra.pigXorDroppedByOrder
#assert_no_axioms FX1Poly.ComputerAlgebra.pigConjoinOrderEqIsEq
#assert_no_axioms FX1Poly.ComputerAlgebra.pigAndPreservesConjoin
#assert_no_axioms FX1Poly.ComputerAlgebra.pigDecidedMarkers
#assert_no_axioms FX1Poly.ComputerAlgebra.pigWallMarkers

end FX1PolyAudit
