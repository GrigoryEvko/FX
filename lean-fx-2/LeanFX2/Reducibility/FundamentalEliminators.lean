import LeanFX2.Reducibility.FundamentalEliminators.BetaEliminators
import LeanFX2.Reducibility.FundamentalEliminators.IotaEliminators
import LeanFX2.Reducibility.FundamentalEliminators.IdentityEliminators
import LeanFX2.Reducibility.FundamentalEliminators.ReflexivityIntroducers

/-! # LeanFX2.Reducibility.FundamentalEliminators — eliminator
fundamentals (shim)

Carved into four sub-modules along the reduction-rule axis:

| Sub-module                                       | Family                                          |
| ------------------------------------------------ | ----------------------------------------------- |
| `FundamentalEliminators.BetaEliminators`         | β-redex eliminators (app / fst / snd / appPi)   |
| `FundamentalEliminators.IotaEliminators`         | ι-redex eliminators on closed inductives        |
| `FundamentalEliminators.IdentityEliminators`     | J-style eliminators on identity types           |
| `FundamentalEliminators.ReflexivityIntroducers`  | refl / oeqRefl / idStrictRefl intro cases       |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Part of the fundamental-theorem
cascade.  Consumed by `Reducibility.FundamentalCubical` and the
top-level `Reducibility` shim. -/
