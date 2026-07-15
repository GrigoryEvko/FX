import FX1PolyAudit.AuditGen
import FX1Poly.Core.Substrate.Profile.PolyProfile
import FX1Poly.Axis.Context.InternalSconing
import FX1Poly.Axis.Context.FireTriangle
import FX1Poly.Extension.ProfileExtension
import FX1Poly.Extension.AdmissibleProfileTensor
import FX1Poly.Extension.FxWithEtaCertifier
import FX1Poly.Extension.ProfileLens
import FX1Poly.STC.FxLogicalRelation
import FX1Poly.STC.FxBoolCanonicity
import FX1Poly.STC.FxNormalization
import FX1Poly.STC.FxIndependenceBoundary
import FX1Poly.Extension.AdmissionAdvanceBoundary
import FX1Poly.Core.Substrate.Profile.ProfileAdmission
import FX1Poly.Core.Substrate.Profile.StrengthCalibration
import FX1PolyAudit.Core.Substrate.Profile.PolyProfile
import FX1PolyAudit.Core.Substrate.Profile.ProfileAdmission
import FX1PolyAudit.Core.Substrate.Profile.StrengthCalibration
import FX1PolyAudit.Extension.AdmissibleProfileTensor
import FX1PolyAudit.Extension.AdmissionAdvanceBoundary
import FX1PolyAudit.Extension.FxWithEtaCertifier
import FX1PolyAudit.Extension.ProfileExtension
import FX1PolyAudit.Extension.ProfileLens
import FX1PolyAudit.STC.FxBoolCanonicity
import FX1PolyAudit.STC.FxIndependenceBoundary
import FX1PolyAudit.STC.FxLogicalRelation
import FX1PolyAudit.STC.FxNormalization
import FX1PolyAudit.STC.Modalities
import FX1PolyAudit.Axis.Context.AxisObligation

/-! # FX1PolyAudit/AuditProfile — region-D aggregator + namespace sweeps (restructured)

The per-declaration axis gates were redistributed into mirror shards (imported
above).  The whole-namespace `#audit_namespace` sweeps and their
`#assert_namespace_min_count` floors are RETAINED here together with the original
axis imports that give the sweeps their declaration coverage. -/

namespace FX1PolyAudit

#audit_namespace FX1Poly.Modal
#assert_namespace_min_count FX1Poly.Modal 106
#audit_namespace FX1Poly.OmegacE
#assert_namespace_min_count FX1Poly.OmegacE 124
#audit_namespace FX1Poly.ProfileFibration
#assert_namespace_min_count FX1Poly.ProfileFibration 72
#audit_namespace FX1Poly.SSC
#assert_namespace_min_count FX1Poly.SSC 30
#audit_namespace FX1Poly.STC
#assert_namespace_min_count FX1Poly.STC 95
#audit_namespace FX1Poly.Axis
#assert_namespace_min_count FX1Poly.Axis 439
#audit_namespace FX1Poly.Extension
#assert_namespace_min_count FX1Poly.Extension 197

end FX1PolyAudit
