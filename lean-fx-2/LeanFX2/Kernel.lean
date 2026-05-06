-- Layer 0 - Foundation
import LeanFX2.Foundation.Mode
import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Foundation.TyAct
import LeanFX2.Foundation.TyActBridge
import LeanFX2.Foundation.Context
import LeanFX2.Foundation.Universe
import LeanFX2.Foundation.Cofib
import LeanFX2.Foundation.RenameIdentity

-- Layer 1 - Term
import LeanFX2.Term
import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.Act
import LeanFX2.Term.ToRaw
import LeanFX2.Term.Pointwise
import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Bridge
import LeanFX2.Term.ProofIrrel
import LeanFX2.Term.Inversion

-- Layer 2 - Reduction
import LeanFX2.Reduction.Step
import LeanFX2.Reduction.StepStar
import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Reduction.ConvCanonical
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.ParStar
import LeanFX2.Reduction.StepStarToPar
import LeanFX2.Reduction.Compat
import LeanFX2.Reduction.Cumul
import LeanFX2.Reduction.ConvCumulHomo
import LeanFX2.Reduction.CumulCastElim
import LeanFX2.Reduction.CumulBenton
import LeanFX2.Reduction.CumulAllais
import LeanFX2.Reduction.CumulPairedEnv
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Reduction.CumulPattern23Bridge

-- Layer 3 - Reduction-facing metatheory and typed/raw bridge
import LeanFX2.Term.SubjectReduction
import LeanFX2.Term.SubjectReductionUniverse
import LeanFX2.Bridge

-- Layer 4 - Confluence
import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.RawParStarCong
import LeanFX2.Confluence.ParStarBridge
import LeanFX2.Confluence.ConvBridge

/-! # LeanFX2.Kernel

Narrow public umbrella for the rich lean-fx-2 kernel core: foundation,
typed terms, reduction, typed/raw bridge, and confluence.  It deliberately
excludes HoTT/cubical/modal theories, graded dimensions, algorithms, surface
syntax, smoke tests, tooling, FX1, and the legacy Lean-kernel scaffold.
-/

namespace LeanFX2

end LeanFX2
