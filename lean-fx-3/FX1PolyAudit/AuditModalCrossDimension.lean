import FX1PolyAudit.Dimensions.Collision.DimensionMultiplicationContrast
import FX1PolyAudit.Dimensions.Collision.DimensionRepetitionContrast
import FX1PolyAudit.Dimensions.Collision.FlagshipMultiDimensionSignature
import FX1PolyAudit.Dimensions.Collision.PrecisionOverflowCollision
import FX1PolyAudit.Dimensions.Collision.SoundnessCollisionCatalog
import FX1PolyAudit.Dimensions.Collision.SoundnessCollisionCatalogComplete
import FX1PolyAudit.Dimensions.Collision.SoundnessCollisionSchema
import FX1PolyAudit.Dimensions.Collision.ThreeWayCollisionClassifiedAsyncSession
import FX1PolyAudit.Dimensions.Graded.GradedEvaluation
import FX1PolyAudit.Dimensions.Graded.GradedLogicalConsistency
import FX1PolyAudit.Dimensions.Graded.GradedNormalizerValue
import FX1PolyAudit.Dimensions.Graded.GradedProgress
import FX1PolyAudit.Dimensions.Graded.SelfApplicationUntypable
import FX1PolyAudit.Dimensions.Lattice.LatticeDistributivityClassification
import FX1PolyAudit.Dimensions.Lattice.ProvenanceLatticeDimension
import FX1PolyAudit.Dimensions.Lattice.VersionCategoryDimension
import FX1PolyAudit.Dimensions.Session.SessionCommunication
import FX1PolyAudit.Dimensions.Session.SessionDualityDimension

/-! # FX1PolyAudit/AuditModalCrossDimension — region-D aggregator (restructured)

This file's per-declaration zero-axiom gates were redistributed into mirror
shards that literally mirror the `FX1Poly` source tree (one audit file per
source module, each well under 50 eval-commands, so the audit build parallelizes).
This thin aggregator re-imports those shards, conserving every gate and keeping
all existing importers (AuditTyped / AuditModal / AuditAll) resolving unchanged. -/

