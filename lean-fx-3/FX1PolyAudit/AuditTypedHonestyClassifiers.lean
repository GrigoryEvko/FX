import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecCategory
import FX1PolyAudit.Typed.Cell.RawTermHeadGenerator
import FX1PolyAudit.Typed.Corpus.Faithfulness.ListElimFaithfulLength
import FX1PolyAudit.Typed.Corpus.Faithfulness.NatElimFaithfulArithmetic
import FX1PolyAudit.Typed.Corpus.Faithfulness.NatElimFaithfulMul
import FX1PolyAudit.Typed.Engine.Classifier.ClassifierRefinement
import FX1PolyAudit.Typed.Engine.Classifier.GeneratorAdmissionSplit
import FX1PolyAudit.Typed.Engine.Classifier.GeneratorHonestyLedger
import FX1PolyAudit.Typed.Engine.Classifier.GeneratorHonestyOverview
import FX1PolyAudit.Typed.Engine.Classifier.GeneratorSemanticTier
import FX1PolyAudit.Typed.Engine.Classifier.StaticTypingSoundness
import FX1PolyAudit.Typed.Engine.Classifier.TypedBySomeEngine
import FX1PolyAudit.Typed.Engine.Classifier.TypingHeadKindClassifier
import FX1PolyAudit.Typed.Engine.Classifier.TypingRoleClassifier
import FX1PolyAudit.Typed.Engine.Classifier.UntypableHeadDecision
import FX1PolyAudit.Typed.Engine.Formation.ConvFlatFormerRigidity
import FX1PolyAudit.Typed.Engine.Formation.ConvFormationFormerRigidity
import FX1PolyAudit.Typed.Engine.Formation.HasTypeFormationNoLambdaApplication
import FX1PolyAudit.Typed.Engine.Formation.ListCodeShape
import FX1PolyAudit.Typed.Engine.Formation.OptionCodeShape
import FX1PolyAudit.Typed.Engine.Formation.SigmaCodeShape
import FX1PolyAudit.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiRootGeneric
import FX1PolyAudit.Typed.Engine.HasTypeDescPi.Inversion.PiTypeFunctionInversion
import FX1PolyAudit.Typed.Engine.IsTypeDesc.IsTypeDescRigidity
import FX1PolyAudit.Typed.Engine.RuleTables.GenElimIotaComputation
import FX1PolyAudit.Typed.Metatheory.Canonicity.Core.BoolElimComputingCanonicity
import FX1PolyAudit.Typed.Metatheory.Canonicity.Core.ListElimComputingCanonicity
import FX1PolyAudit.Typed.Metatheory.Canonicity.Core.MatchElimComputingCanonicity
import FX1PolyAudit.Typed.Metatheory.Canonicity.Core.MatchElimComputingCanonicityTyped
import FX1PolyAudit.Typed.Metatheory.Canonicity.Core.MatchGeneralBranchCanonicity
import FX1PolyAudit.Typed.Metatheory.Canonicity.Core.NatElimComputingCanonicity
import FX1PolyAudit.Typed.Metatheory.Normalizer.CertifiedWordReductionConfluence
import FX1PolyAudit.Typed.Metatheory.Reducibility.Core.ClosedNumeralSubstInvariant
import FX1PolyAudit.Typed.Metatheory.Reducibility.LogRel.TypedTypeValidityLeveledCompleteness
import FX1PolyAudit.Typed.Metatheory.Reducibility.Member.ReducibleSemanticRules
import FX1PolyAudit.Typed.Metatheory.Reducibility.Telescope.TelescopeReducible
import FX1PolyAudit.Typed.Metatheory.Universe.UniverseCodeShape
import FX1PolyAudit.Typed.Metatheory.Universe.UniverseTypingSuccessor
import FX1PolyAudit.Typed.RegionD.Contested.CertifiedWordReductionTermination
import FX1PolyAudit.Typed.RegionD.Contested.SemanticTierSoundness
import FX1PolyAudit.Typed.RegionD.SelfVerification.KnownUnsoundnessCorpus

/-! # FX1PolyAudit/AuditTypedHonestyClassifiers — region-D aggregator (restructured)

This file's per-declaration zero-axiom gates were redistributed into mirror
shards that literally mirror the `FX1Poly` source tree (one audit file per
source module, each well under 50 eval-commands, so the audit build parallelizes).
This thin aggregator re-imports those shards, conserving every gate and keeping
all existing importers (AuditTyped / AuditModal / AuditAll) resolving unchanged. -/

