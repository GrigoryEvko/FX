-- Layer 0 - Foundation
import LeanFX2.Foundation.Mode
import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst.ActionInstances
import LeanFX2.Foundation.RawPartialRename.VarLemmas
import LeanFX2.Foundation.RawPartialRenameCommute
import LeanFX2.Foundation.RawPartialRename.Strengthen
import LeanFX2.Foundation.RawPartialRename.UnweakenSubstCommute
import LeanFX2.Foundation.RawPartialRename.UnweakenSubstDispatch
import LeanFX2.Foundation.RawPartialRename.Swap01
import LeanFX2.Foundation.RawPartialRename.TranspPiContractum
import LeanFX2.Foundation.RawPartialRename.TranspPiPathRecognizer
import LeanFX2.Foundation.RawTermInjective
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.TyStrengthen
import LeanFX2.Foundation.TyRenameInjective
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Foundation.TyAct
import LeanFX2.Foundation.TyActBridge
import LeanFX2.Foundation.Context
import LeanFX2.Foundation.Universe
import LeanFX2.Foundation.Cofib
import LeanFX2.Foundation.RenameIdentity
import LeanFX2.Foundation.Polygraph.PolyCell
import LeanFX2.Foundation.Polygraph.ParallelPair
import LeanFX2.Foundation.Polygraph.Wellfounded
import LeanFX2.Foundation.Polygraph.DecEq
import LeanFX2.Foundation.Polygraph.VerticalComp
import LeanFX2.Foundation.Polygraph.HorizontalComp
import LeanFX2.Foundation.Polygraph.Laws
import LeanFX2.Foundation.Polygraph.FreeCategory
import LeanFX2.Foundation.Polygraph.RawPolyTerm
import LeanFX2.Foundation.Polygraph.PolyTerm
import LeanFX2.Foundation.Polygraph.PolyTermRoundtrip
import LeanFX2.Foundation.Polygraph.PolyTermAction.RawPolyTermRename
import LeanFX2.Foundation.Polygraph.PolyTermAction.RawPolyTermSubst
import LeanFX2.Foundation.Polygraph.PolyTermAction.SubstCommute
import LeanFX2.Foundation.Polygraph.PolyTermAction.ToRawTermRename
import LeanFX2.Foundation.Polygraph.PolyTermAction.ToRawTermSubst
import LeanFX2.Foundation.Polygraph.StepLabel
import LeanFX2.Foundation.Polygraph.Dim1Extraction
import LeanFX2.Foundation.Polygraph.Dim1Equivalence
import LeanFX2.Foundation.Polygraph.Dim2Diamond

-- Layer 1 - Term
import LeanFX2.Term
import LeanFX2.Term.RenameInjective.ConstructorFamilies
import LeanFX2.Term.RenameInjective.BinderInversions
import LeanFX2.Term.RenameInjective.ClosedData
import LeanFX2.Term.RenameInjective.CubicalCollections
import LeanFX2.Term.RenameInjective.IdentityEliminators
import LeanFX2.Term.RenameInjective.ReflexivityInterval
import LeanFX2.Term.RenameInjective.IdentityInterval
import LeanFX2.Term.RenameInjective.ModalStructural
import LeanFX2.Term.RenameInjective.TypeCodes
import LeanFX2.Term.RenameInjective.EquivIntro
import LeanFX2.Term.Subst
import LeanFX2.Term.Act
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure
import LeanFX2.Term.Pointwise.IdentitySubst
import LeanFX2.Term.Pointwise.VariableAndIntroArms
import LeanFX2.Term.Pointwise.ApplicationAndSigmaArms
import LeanFX2.Term.Pointwise.EliminatorArms
import LeanFX2.Term.Pointwise.IdentityAndUniverseCodeArms
import LeanFX2.Term.Pointwise.CubicalAndStructuralArms
import LeanFX2.Term.Pointwise.EffectAndHoTTHetArms
import LeanFX2.Term.HEqCongr.Compound
import LeanFX2.Term.HEqCongr.Atomic
import LeanFX2.Term.Bridge
import LeanFX2.Term.ProofIrrel
import LeanFX2.Term.Inversion
import LeanFX2.Term.ContextStrengthening
import LeanFX2.Term.PartialStrengthen.RenameImage.TypeCodes
import LeanFX2.Term.PartialStrengthen.RenameImage.RefineSession
import LeanFX2.Term.PartialStrengthen.RenameImage.Equivalence
import LeanFX2.Term.PartialStrengthen.RenameImage.Cubical
import LeanFX2.Term.PartialStrengthen.RenameImage.CodataProjection
import LeanFX2.Term.PartialStrengthen.RenameImage.Effects
import LeanFX2.Term.PartialStrengthen.RenameImage.CastWrapped
import LeanFX2.Term.WeakenInverse
import LeanFX2.Term.TypedInversion
import LeanFX2.Term.StrengtheningImage.TotalOnWeakenHeadlines
import LeanFX2.Term.PolyToTerm
import LeanFX2.Term.ToPoly
import LeanFX2.Term.PolyRename
import LeanFX2.Term.PolySubst

-- Layer 2 - Reduction
import LeanFX2.Reduction.Step.Casts
import LeanFX2.Reduction.StepStar
import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Reduction.ConvCanonical
import LeanFX2.Reduction.ParRed.CongAliases
import LeanFX2.Reduction.ParRed.ParCasts
import LeanFX2.Reduction.ParRed.ParStepLift
import LeanFX2.Reduction.RawPar.Inductive
import LeanFX2.Reduction.RawParCompatible.NamedCompatibility
import LeanFX2.Reduction.RawParWeakenInv.Weaken
import LeanFX2.Reduction.TranspPiContractumPar
import LeanFX2.Reduction.ParStar
import LeanFX2.Reduction.StepStarToPar
import LeanFX2.Reduction.Compat.Cubical
import LeanFX2.Reduction.Compat.HoTT
import LeanFX2.Reduction.Compat.Effects
import LeanFX2.Reduction.Compat.Misc
import LeanFX2.Reduction.Compat.TypeCodes
import LeanFX2.Reduction.Cumul.Relation.Inductive
import LeanFX2.Reduction.Cumul.Promotion
import LeanFX2.Reduction.Cumul.BackwardCompat
import LeanFX2.Reduction.Cumul.SubstOuter
import LeanFX2.Reduction.Cumul.SubstCompatCases
import LeanFX2.Reduction.Cumul.SubstCompatCong
import LeanFX2.Reduction.Cumul.SubstCompatTerm
import LeanFX2.Reduction.ConvCumulHomo.Relation
import LeanFX2.Reduction.ConvCumulHomo.Bridge
import LeanFX2.Reduction.ConvCumulHomo.BentonHeadlines
import LeanFX2.Reduction.ConvCumulHomo.CumulSide
import LeanFX2.Reduction.ConvCumulHomo.Dispatch
import LeanFX2.Reduction.CumulCastElim
import LeanFX2.Reduction.CumulBenton
import LeanFX2.Reduction.CumulAllais.EliminatorArms
import LeanFX2.Reduction.CumulPairedEnv
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Reduction.CumulPattern23Bridge

-- Layer 3 - Reduction-facing metatheory and typed/raw bridge
import LeanFX2.Term.SubjectReduction
import LeanFX2.Term.SubjectReductionUniverse
import LeanFX2.Bridge
import LeanFX2.Reduction.ParRed.PreEtaInversion
import LeanFX2.Reducibility.Basic
import LeanFX2.Reducibility.SN.Helpers
import LeanFX2.Reducibility.StableBase.SubtermSN
import LeanFX2.Reducibility.NeutralSNFoundation.EquivHott
import LeanFX2.Reducibility.NeutralSNHott.NatRecAndOption
import LeanFX2.Reducibility.NeutralSNIntro.Codes
import LeanFX2.Reducibility.NeutralSNClosure.GlueEquiv
import LeanFX2.Term.SN.DirectCases
import LeanFX2.Reducibility.Kripke.Headline.CanonicalAndStructural
import LeanFX2.Reducibility.Kripke.Headline.HoTTCodesAndCubical
import LeanFX2.Reducibility.Kripke.Headline.EliminatorsAndApplications
import LeanFX2.Reducibility.Kripke.SNExtraction

-- Layer 4 - Confluence
import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Confluence.ConvTrans
import LeanFX2.Confluence.RawCd.ArrowFamily
import LeanFX2.Confluence.RawCd.ModalAndRefine
import LeanFX2.Confluence.RawCd.RecordAndCodata
import LeanFX2.Confluence.RawCd.SigmaArms
import LeanFX2.Confluence.RawCd.BoolNatArms
import LeanFX2.Confluence.RawCd.ListOptionEitherArms
import LeanFX2.Confluence.RawCd.IdentityArms
import LeanFX2.Confluence.RawCd.CubicalAndEquiv
import LeanFX2.Confluence.RawCd.Core
import LeanFX2.Confluence.RawCdRename.Main
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
