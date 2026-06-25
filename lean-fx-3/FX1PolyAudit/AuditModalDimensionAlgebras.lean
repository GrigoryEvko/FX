import FX1PolyAudit.Dimensions.Graded.GradeVector
import FX1PolyAudit.Dimensions.Graded.GradeVectorGeneric
import FX1PolyAudit.Dimensions.Graded.GradedLambdaTerm
import FX1PolyAudit.Dimensions.Security.UsageDiscipline
import FX1PolyAudit.Dimensions.Semiring.GradeSemiringFunctorial
import FX1PolyAudit.Dimensions.Semiring.GradeSemiringMonoidal
import FX1PolyAudit.Dimensions.Semiring.GradeSemiringProduct
import FX1PolyAudit.Tier0.Mode.GradeAlgebra.ResourceGraded
import FX1PolyAudit.Tier0.Mode.GradeAlgebra.ResourceGradedMore

/-! # FX1PolyAudit/AuditModalDimensionAlgebras — region-D aggregator (restructured)

This file's per-declaration zero-axiom gates were redistributed into mirror
shards that literally mirror the `FX1Poly` source tree (one audit file per
source module, each well under 50 eval-commands, so the audit build parallelizes).
This thin aggregator re-imports those shards, conserving every gate and keeping
all existing importers (AuditTyped / AuditModal / AuditAll) resolving unchanged. -/

