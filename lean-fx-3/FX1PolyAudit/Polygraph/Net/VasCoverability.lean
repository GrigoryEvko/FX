import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Net.VasCoverability

/-! # FX1PolyAudit/Polygraph/Net/VasCoverability — zero-axiom gate
    (NET-5 brick: backward coverability for vector addition systems)

Per-declaration zero-axiom gate for the VAS backward-coverability kit: the scalar
`cvbAdd`/`cvbMonus` arithmetic and its cancellation/monotonicity lemmas, the vector order
`cvbVecLe` with reflexivity/transitivity, vector `cvbVecAdd`/`cvbVecMonus`/`cvbSameShape`,
the `CvbVas` carrier, firing (`cvbFire`/`cvbFireEnabled`), the minimal backward pre-image
`cvbBackwardMarking`, the genuine-coverability inductive `CvbCovers`, the TWO soundness
theorems (`cvbBackwardStepSound` — one backward step is a real cover; `cvbCheckCoverSound` —
a checked forward firing chain witnesses coverability), the bounded-fuel decision engine
(`cvbPreStep`, `cvbAntichainMinimise`, `cvbCoverBounded`, `cvbDecideCover`, `CvbVerdict`),
the Dickson termination walls, and the ground fires.

The unconditional-termination and Karp–Miller-tree claims are WALLED
(`cvbHasUnconditionalCoverabilityTermination = false`,
`cvbHasKarpMillerTree = false`): the backward antichain iteration stabilises by the
`Nat^k`-WQO (Dickson), whose zero-axiom proof is the almost-full PRODUCT needing
`WellFounded.fix` — the NET-4 impossibility `FX1Poly.ComputerAlgebra.fxNet4_dicksonWall`.
`cvbTerminationWallEqualsDickson` equates the marker to that wall by `rfl`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Net.cvbAdd
#assert_no_axioms FX1Poly.Polygraph.Net.cvbMonus
#assert_no_axioms FX1Poly.Polygraph.Net.cvbAddZeroLeft
#assert_no_axioms FX1Poly.Polygraph.Net.cvbMonusZeroRight
#assert_no_axioms FX1Poly.Polygraph.Net.cvbAddSuccLeft
#assert_no_axioms FX1Poly.Polygraph.Net.cvbMonusAddCancel
#assert_no_axioms FX1Poly.Polygraph.Net.cvbLeSuccRight
#assert_no_axioms FX1Poly.Polygraph.Net.cvbLeAddSelf
#assert_no_axioms FX1Poly.Polygraph.Net.cvbLeMonusAdd
#assert_no_axioms FX1Poly.Polygraph.Net.cvbLePreOneFire
#assert_no_axioms FX1Poly.Polygraph.Net.cvbAddMonoLeft
#assert_no_axioms FX1Poly.Polygraph.Net.cvbMonusMonoLeft
#assert_no_axioms FX1Poly.Polygraph.Net.cvbCondGuardElim
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecLe
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecLeConsIntro
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecLeConsElim
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecLeRefl
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecLeTrans
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecAdd
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecMonus
#assert_no_axioms FX1Poly.Polygraph.Net.cvbSameShape
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecLeAddSelf
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecMonusMono
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecAddMono
#assert_no_axioms FX1Poly.Polygraph.Net.CvbVas
#assert_no_axioms FX1Poly.Polygraph.Net.CvbVas.mk
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireEnabled
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFire
#assert_no_axioms FX1Poly.Polygraph.Net.cvbBackwardMarking
#assert_no_axioms FX1Poly.Polygraph.Net.cvbTransitionBeq
#assert_no_axioms FX1Poly.Polygraph.Net.cvbTransitionMem
#assert_no_axioms FX1Poly.Polygraph.Net.cvbTransitionMemVas
#assert_no_axioms FX1Poly.Polygraph.Net.cvbVecLePreOneFire
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireMono
#assert_no_axioms FX1Poly.Polygraph.Net.CvbCovers
#assert_no_axioms FX1Poly.Polygraph.Net.CvbCovers.here
#assert_no_axioms FX1Poly.Polygraph.Net.CvbCovers.step
#assert_no_axioms FX1Poly.Polygraph.Net.cvbBackwardStepSound
#assert_no_axioms FX1Poly.Polygraph.Net.cvbChainInVas
#assert_no_axioms FX1Poly.Polygraph.Net.cvbCheckCover
#assert_no_axioms FX1Poly.Polygraph.Net.cvbCheckCoverSound
#assert_no_axioms FX1Poly.Polygraph.Net.cvbConcat
#assert_no_axioms FX1Poly.Polygraph.Net.cvbMapPreOne
#assert_no_axioms FX1Poly.Polygraph.Net.cvbPreImagesAll
#assert_no_axioms FX1Poly.Polygraph.Net.cvbDominated
#assert_no_axioms FX1Poly.Polygraph.Net.cvbDropDominatedBy
#assert_no_axioms FX1Poly.Polygraph.Net.cvbAntichainInsert
#assert_no_axioms FX1Poly.Polygraph.Net.cvbAntichainMinimise
#assert_no_axioms FX1Poly.Polygraph.Net.cvbPreStep
#assert_no_axioms FX1Poly.Polygraph.Net.cvbSourceCovers
#assert_no_axioms FX1Poly.Polygraph.Net.cvbBasisBeq
#assert_no_axioms FX1Poly.Polygraph.Net.CvbVerdict
#assert_no_axioms FX1Poly.Polygraph.Net.CvbVerdict.covered
#assert_no_axioms FX1Poly.Polygraph.Net.CvbVerdict.notYetAtFuel
#assert_no_axioms FX1Poly.Polygraph.Net.CvbVerdict.stableUncovered
#assert_no_axioms FX1Poly.Polygraph.Net.cvbCoverBounded
#assert_no_axioms FX1Poly.Polygraph.Net.cvbDecideCover
#assert_no_axioms FX1Poly.Polygraph.Net.cvbHasUnconditionalCoverabilityTermination
#assert_no_axioms FX1Poly.Polygraph.Net.cvbHasKarpMillerTree
#assert_no_axioms FX1Poly.Polygraph.Net.cvbTerminationWallEqualsDickson
#assert_no_axioms FX1Poly.Polygraph.Net.cvbExampleVas
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireVecLeComputes
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireVecLeComputesFalse
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireVecAddComputes
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireVecMonusComputes
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireEnabledTrue
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireEnabledFalse
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireProducesToken
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireCovered
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireStableUncovered
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireNotYetAtFuel
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireBackwardStepCovers
#assert_no_axioms FX1Poly.Polygraph.Net.cvbFireForwardChainCovers

end FX1PolyAudit
