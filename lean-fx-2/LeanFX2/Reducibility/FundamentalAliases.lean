import LeanFX2.Reducibility.FundamentalAliases.Aliases
import LeanFX2.Reducibility.FundamentalAliases.RawPayloads
import LeanFX2.Reducibility.FundamentalAliases.M04Cases
import LeanFX2.Reducibility.FundamentalAliases.M04Eliminators

/-! # LeanFX2.Reducibility.FundamentalAliases — SN aliases + K12.27 (shim)

Carved into four sub-modules along the K12.27 close-out cascade:

| Sub-module                            | Family                                  |
| ------------------------------------- | --------------------------------------- |
| `FundamentalAliases.Aliases`          | fundamental_*_at_* + Term.identity wraps |
| `FundamentalAliases.RawPayloads`      | Term.identity_*_of_rawPayloads family   |
| `FundamentalAliases.M04Cases`         | K12.27 direct leaf / recursive / cong   |
| `FundamentalAliases.M04Eliminators`   | K12.27 direct eliminator-form endpoints |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.FundamentalCubical`
and the top-level `Reducibility` shim. -/
