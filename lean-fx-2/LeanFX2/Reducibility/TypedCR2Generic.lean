import LeanFX2.Reducibility.TypedCR2Generic.GenericDispatch
import LeanFX2.Reducibility.TypedCR2Generic.HEqCasts
import LeanFX2.Reducibility.TypedCR2Generic.SubstSingleton
import LeanFX2.Reducibility.TypedCR2Generic.SubstLift
import LeanFX2.Reducibility.TypedCR2Generic.FundamentalLam

/-! # LeanFX2.Reducibility.TypedCR2Generic — generic CR3 dispatch (shim)

Carved into five sub-modules along the generic CR3 + ReducibleSubst
cascade:

| Sub-module                                | Family                                          |
| ----------------------------------------- | ----------------------------------------------- |
| `TypedCR2Generic.GenericDispatch`         | uniform CR3 + varShape dispatchers              |
| `TypedCR2Generic.HEqCasts`                | type-index / raw-index equality transports      |
| `TypedCR2Generic.SubstSingleton`          | ReducibleSubst singleton / cons-singleton / id  |
| `TypedCR2Generic.SubstLift`               | lift SN projections + identity-subst SN bridges |
| `TypedCR2Generic.FundamentalLam`          | Term.lam at arrow fundamental closure           |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.TypedCR2Compound`,
`Reducibility.TypedCR2Wrapup`, the fundamental theorem modules, and the
top-level `Reducibility` shim. -/
