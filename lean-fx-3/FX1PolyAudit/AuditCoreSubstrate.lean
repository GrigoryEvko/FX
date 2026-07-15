import FX1PolyAudit.Core.Equality.Eta.EtaRowFiringSubstrate
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.BoolElimStrongNormalization
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.IdentityEliminatorStrongNormalization
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationApplication
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationFormerCorpus
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationReflection
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationRenameForward
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSmokeCorpus
import FX1PolyAudit.Core.Metatheory.Reducibility.Candidates.KripkeCandidateRenameClosure
import FX1PolyAudit.Core.Metatheory.Reducibility.Members.ReducibleMemberNeutral
import FX1PolyAudit.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeRename
import FX1PolyAudit.Core.NamespaceSweep
import FX1PolyAudit.Core.Rewriting.Normalize.RawTermNF
import FX1PolyAudit.Core.Rewriting.Reduction.Step.StepRenameReflect
import FX1PolyAudit.Core.Rewriting.Reduction.Step.StepRenameReflectAssembly
import FX1PolyAudit.Core.Rewriting.Reduction.WeakHead.WeakHeadRowCommuteEngine
import FX1PolyAudit.Core.Rewriting.Reduction.WeakHead.WeakHeadRowCommuteEngineAxiomWitness
import FX1PolyAudit.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRename
import FX1PolyAudit.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRenameReflect
import FX1PolyAudit.Core.Substrate.Certifier.HorizontalCompositeAdmission
import FX1PolyAudit.Core.Substrate.Neutral.NeutralStepClosure
import FX1PolyAudit.Core.Substrate.Neutral.NeutralTermRename
import FX1PolyAudit.Tier0.Term.Core.RawTermFoldNonVarCommute
import FX1PolyAudit.Tier0.Term.Generator.GeneratorCountPinCoreCellsAudit

/-! # FX1PolyAudit.AuditCoreSubstrate — aggregator over the per-kernel-module audit shards

The Core/Foundation namespace floor sweeps (`Core.NamespaceSweep`) plus the
foundational term-substrate per-declaration gates, now mirrored
one-file-per-kernel-module under `FX1PolyAudit/Core/...` (auto-discovered by the
lakefile `.submodules` glob, elaborating in parallel).  This aggregator
re-imports them so `lake build FX1PolyAudit.AuditCoreSubstrate` still pulls the
whole foundational gate set with the full-closure namespace sweep. -/
