import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.GlobularSet

/-! # FX1PolyAudit/AuditTier0ModeGlobularSet — zero-axiom gate for mode-6's globular sets

Per-declaration zero-axiom gate for `mode-6` (`FX1Poly/Tier0/Mode/GlobularSet.lean`): the globular-set
foundation (`RawGlobularSet` with the globular identities), the terminal/discrete instances, globular-set
morphisms (`GlobularMap` + identity/compose), Leinster's contraction (`IsParallel` + `GlobularContraction`),
the contractible-globular-set bundle, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The globular-set foundation + instances
#assert_no_axioms FX1Poly.Polygraph.RawGlobularSet
#assert_no_axioms FX1Poly.Polygraph.terminalGlobularSet
#assert_no_axioms FX1Poly.Polygraph.discreteGlobularSet

-- Morphisms of globular sets
#assert_no_axioms FX1Poly.Polygraph.GlobularMap
#assert_no_axioms FX1Poly.Polygraph.GlobularMap.identity
#assert_no_axioms FX1Poly.Polygraph.GlobularMap.compose

-- Contraction (the weak-coherence mechanism)
#assert_no_axioms FX1Poly.Polygraph.RawGlobularSet.IsParallel
#assert_no_axioms FX1Poly.Polygraph.GlobularContraction
#assert_no_axioms FX1Poly.Polygraph.terminalGlobularContraction
#assert_no_axioms FX1Poly.Polygraph.ContractibleGlobularSet
#assert_no_axioms FX1Poly.Polygraph.terminalContractibleGlobularSet

-- Honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasFreeStrictOmegaMonadAndOperad
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasInitialContractibleOperadAlgebras
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasStrictOmegaCategory
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasGeneralDirectedComplexCellShape

end FX1PolyAudit
