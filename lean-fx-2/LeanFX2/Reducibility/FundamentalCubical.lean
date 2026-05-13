import LeanFX2.Reducibility.FundamentalCubical.CubicalGlueEliminators
import LeanFX2.Reducibility.FundamentalCubical.RecordRefineCodataEndpoints
import LeanFX2.Reducibility.FundamentalCubical.IdentitySubstIntroForms
import LeanFX2.Reducibility.FundamentalCubical.IdentitySubstEliminators
import LeanFX2.Reducibility.FundamentalCubical.IdentitySubstModalIdentity

/-! # LeanFX2.Reducibility.FundamentalCubical — cubical + identity-subst
fundamentals (shim)

Carved into five sub-modules along the SN-direct vs
identity-substitution axis, then by destructor family:

| Sub-module                                                | Family                                          |
| --------------------------------------------------------- | ----------------------------------------------- |
| `FundamentalCubical.CubicalGlueEliminators`               | pathApp / glueElim / glueIntro at cubical types |
| `FundamentalCubical.RecordRefineCodataEndpoints`          | record / refine / codata intro + codataDest    |
| `FundamentalCubical.IdentitySubstIntroForms`              | identity-subst SN for intro / projection forms  |
| `FundamentalCubical.IdentitySubstEliminators`             | identity-subst SN for ι-eliminators             |
| `FundamentalCubical.IdentitySubstModalIdentity`           | identity-subst SN for modal + J-recursor forms  |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Final cubical + identity-subst
chapter of the fundamental-theorem cascade. -/
