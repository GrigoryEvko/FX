import LeanFX2.Reducibility.FundamentalAliases.Aliases
import LeanFX2.Reducibility.FundamentalAliases.RawPayloads
import LeanFX2.Reducibility.FundamentalAliases.DirectCases
import LeanFX2.Reducibility.FundamentalAliases.EliminatorCases

/-! # LeanFX2.Reducibility.FundamentalAliases — SN aliases (shim)

Carved into four sub-modules along the strong-normalization
endpoint cascade:

| Sub-module                            | Family                                            |
| ------------------------------------- | ------------------------------------------------- |
| `FundamentalAliases.Aliases`          | `fundamental_*_at_*` + `Term.identity` wraps      |
| `FundamentalAliases.RawPayloads`      | `Term.identity_*_of_rawPayloads` family           |
| `FundamentalAliases.DirectCases`      | direct leaf / recursive-intro / cong endpoints    |
| `FundamentalAliases.EliminatorCases`  | direct eliminator-form endpoints                  |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.FundamentalCubical`
and the top-level `Reducibility` shim. -/
