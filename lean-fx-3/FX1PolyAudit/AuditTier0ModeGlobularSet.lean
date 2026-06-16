import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.GlobularSet

/-! # FX1PolyAudit/AuditTier0ModeGlobularSet — zero-axiom gate for mode-6's globular sets

Per-declaration zero-axiom gate for `mode-6` (`FX1Poly/Tier0/Mode/GlobularSet.lean`): the globular-set
foundation (`RawGlobularSet` with the globular identities), the terminal/discrete instances, globular-set
morphisms (`GlobularMap` + identity/compose), Leinster's contraction (`IsParallel` + `GlobularContraction`),
the contractible-globular-set bundle, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The globular-set foundation + instances
#assert_no_axioms FX1Poly.Tier0.RawGlobularSet
#assert_no_axioms FX1Poly.Tier0.terminalGlobularSet
#assert_no_axioms FX1Poly.Tier0.discreteGlobularSet

-- Morphisms of globular sets
#assert_no_axioms FX1Poly.Tier0.GlobularMap
#assert_no_axioms FX1Poly.Tier0.GlobularMap.identity
#assert_no_axioms FX1Poly.Tier0.GlobularMap.compose

-- Contraction (the weak-coherence mechanism)
#assert_no_axioms FX1Poly.Tier0.RawGlobularSet.IsParallel
#assert_no_axioms FX1Poly.Tier0.GlobularContraction
#assert_no_axioms FX1Poly.Tier0.terminalGlobularContraction
#assert_no_axioms FX1Poly.Tier0.ContractibleGlobularSet
#assert_no_axioms FX1Poly.Tier0.terminalContractibleGlobularSet

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasFreeStrictOmegaMonadAndOperad
#assert_no_axioms FX1Poly.Tier0.fxMode_hasInitialContractibleOperadAlgebras
#assert_no_axioms FX1Poly.Tier0.fxMode_hasStrictOmegaCategory
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGeneralDirectedComplexCellShape

end FX1PolyAudit
