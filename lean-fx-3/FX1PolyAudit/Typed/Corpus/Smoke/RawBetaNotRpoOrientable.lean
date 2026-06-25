import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Corpus.Smoke.RawBetaNotRpoOrientable

/-! # FX1PolyAudit.Typed.Corpus.Smoke.RawBetaNotRpoOrientable

Zero-axiom audit shard mirroring kernel module `FX1Poly.Typed.Corpus.Smoke.RawBetaNotRpoOrientable`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The β boundary of the rose-tree RPO is a THEOREM, not a hand-typed verdict. The bridge orients the
-- terminating ι/η fragment (realGenRpoWellFounded above), but no type-blind well-founded order on the
-- eraseToRose-erased syntax can orient raw β: Ω = (λx. x x)(λx. x x) β-steps to ITSELF, so its single
-- erasure would have to sit strictly below itself — a self-loop accessibleElementNotSelfRelated refutes.
-- This forces the rose-tree-word-rewriting leg to cover strong normalization only as a partial fragment;
-- full β-SN routes through Tait (Ω is untypable), exactly as RawIotaRpoBridge already imports.
#assert_no_axioms FX1Poly.Core.RawIotaRpo.betaNotOrientableByErasure

end FX1PolyAudit
