import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.PathApplicationStrongNormalizationForward

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.PathApplicationStrongNormalizationForward

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.PathApplicationStrongNormalizationForward`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The path-application twin: `pathApp path argument` is SN under the ENDPOINT-β side-condition (every `body`
-- with `path ↝* pathLam body` has `body[argument]` SN).  `gen_pathLam` has no domain annotation, so the
-- side-condition quantifies over `body` alone; otherwise the verbatim shape of the `app` forward SN, riding the
-- new `Step.from_pathApp` inversion.  The load-bearing SN ingredient for the `pathApp` member weak-head-expansion.
#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_pathApplicationCell_aux

#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_pathApplicationCell_ofEndpointBetaContractionsStronglyNormalizing

end FX1PolyAudit
