import LeanFX2.Algo.Progress.CanonicalIntroductions
import LeanFX2.Algo.Progress.CanonicalTypeCodes
import LeanFX2.Algo.Progress.CanonicalInterval
import LeanFX2.Algo.Progress.CanonicalHoTTRefl
import LeanFX2.Algo.Progress.BetaIotaStepProvability
import LeanFX2.Algo.Progress.CongRuleLifters
import LeanFX2.Algo.Progress.Headline

/-! # LeanFX2.Algo.Progress — Wright-Felleisen Progress (M05) (shim)

This file is the Wright-Felleisen Progress half of type soundness
for the typed kernel. It was carved into 7 sub-modules along the
**theorem-family** axis (canonical-form inversions / β-ι step
provability / cong lifters / headline assembly):

| Sub-module                  | Family                                              |
| --------------------------- | --------------------------------------------------- |
| `CanonicalIntroductions`    | `headCtor_<intro>_raw` for value-introduction heads |
| `CanonicalTypeCodes`        | `headCtor_<typeCode>_raw` for type-code heads       |
| `CanonicalInterval`         | `headCtor_<intervalCtor>_raw` for cubical interval  |
| `CanonicalHoTTRefl`         | `headCtor_<hottCtor>_raw` for refl-fragment + oeq   |
| `BetaIotaStepProvability`   | `Term.<eliminator>_<intro>_steps` β/ι atoms (M05.B) |
| `CongRuleLifters`           | `Term.<elim>_<position>_steps_lift` (M05.C)         |
| `Headline`                  | `value_or_cong_only_progress` + `app_progress_or_step` (M05.D) |

Preservation (the dual half of type soundness) lives in
`Term/SubjectReduction.lean` and `Term/SubjectReductionGeneral.lean`
(M06/M07).

## Root status

Wright-Felleisen Progress theorem assembly; partial coverage of
the headline (full β cases for `Term.app`; remaining 16 conditional
eliminators deferred per documented gap analysis in
`Headline.lean`). Zero-axiom under strict policy. -/
