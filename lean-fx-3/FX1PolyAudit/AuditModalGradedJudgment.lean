import FX1PolyAudit.Dimensions.Graded.GradeErasureGeneric
import FX1PolyAudit.Dimensions.Graded.GradedGradeExactness
import FX1PolyAudit.Dimensions.Graded.GradedSubstitutionGeneric
import FX1PolyAudit.Dimensions.Graded.GradedTypingGeneric
import FX1PolyAudit.Dimensions.Graded.GradedWeakeningGeneric
import FX1PolyAudit.Dimensions.Lattice.BoundedJoinSemilatticeProductOrder
import FX1PolyAudit.Dimensions.Lattice.BoundedJoinSemilatticeUniversal
import FX1PolyAudit.Dimensions.Lattice.OverflowLatticeDimension
import FX1PolyAudit.Dimensions.Semiring.ComplexitySemiring
import FX1PolyAudit.Dimensions.Semiring.UnifiedGradeMonoid
import FX1PolyAudit.Tier0.Mode.GradeAlgebra.EffectLatticeClassification

/-! # FX1PolyAudit/AuditModalGradedJudgment — region-D aggregator (restructured)

This file's per-declaration zero-axiom gates were redistributed into mirror
shards that literally mirror the `FX1Poly` source tree (one audit file per
source module, each well under 50 eval-commands, so the audit build parallelizes).
This thin aggregator re-imports those shards, conserving every gate and keeping
all existing importers (AuditTyped / AuditModal / AuditAll) resolving unchanged. -/

