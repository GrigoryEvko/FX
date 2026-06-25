import FX1PolyAudit.Dimensions.Graded.GradedBinaryParametricity
import FX1PolyAudit.Dimensions.Graded.GradedCompositionGeneric
import FX1PolyAudit.Dimensions.Graded.GradedFundamentalTheorem
import FX1PolyAudit.Dimensions.Graded.GradedNormalization
import FX1PolyAudit.Dimensions.Graded.GradedReductionConfluence
import FX1PolyAudit.Dimensions.Graded.GradedReductionSubstitution
import FX1PolyAudit.Dimensions.Graded.GradedRelationScaling
import FX1PolyAudit.Dimensions.Graded.GradedSubjectReductionGeneric
import FX1PolyAudit.Dimensions.Graded.GradedSubstitutionAlgebra
import FX1PolyAudit.Dimensions.Graded.SimpleStrongNormalization
import FX1PolyAudit.Dimensions.Graded.SimpleTyping
import FX1PolyAudit.Dimensions.Lattice.ClockDomainLatticeDimension
import FX1PolyAudit.Dimensions.Lattice.MutationChainLatticeDimension
import FX1PolyAudit.Dimensions.Lattice.PreorderDimension
import FX1PolyAudit.Dimensions.Security.FractionalPermission

/-! # FX1PolyAudit/AuditModalGradedSubstitution — region-D aggregator (restructured)

This file's per-declaration zero-axiom gates were redistributed into mirror
shards that literally mirror the `FX1Poly` source tree (one audit file per
source module, each well under 50 eval-commands, so the audit build parallelizes).
This thin aggregator re-imports those shards, conserving every gate and keeping
all existing importers (AuditTyped / AuditModal / AuditAll) resolving unchanged. -/

