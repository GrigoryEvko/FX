import FX1PolyAudit.AuditGen
import FX1Poly.Core.PolyProfile

/-! # FX1PolyAudit/AuditProfile — namespace zero-axiom sweep for the axis substrate

Persistent zero-axiom gate for the PolyProfile axis closure migrated out
of lean-fx-2's `Foundation/PolyCell/<Axis>` directories.  `PolyProfile`
bundles the fourteen graded-modal axis structures the cell calculus
fibres over (the directed-complex shape, univalent algebra, thin
stratification, cubical saturation, rung enrichment, Gray tensor,
cohesive-focus modality, profile-fibration morphisms, omega-c-enriched
hom, SSC backbone, STC modalities, MTT mode theory, universe config).

Each axis file is self-contained (no Core / native-infra / MLTT
dependency).  The `#audit_namespace` sweeps walk every loaded
declaration under each axis namespace and fail the build at the first
axiom leak.
-/

#audit_namespace FX1Poly.Algebra
#audit_namespace FX1Poly.Enrichment
#audit_namespace FX1Poly.Gray
#audit_namespace FX1Poly.MTTNorm
#audit_namespace FX1Poly.Modal
#audit_namespace FX1Poly.OmegacE
#audit_namespace FX1Poly.ProfileFibration
#audit_namespace FX1Poly.SSC
#audit_namespace FX1Poly.STC
#audit_namespace FX1Poly.Saturation
#audit_namespace FX1Poly.Shape
#audit_namespace FX1Poly.Stratification
