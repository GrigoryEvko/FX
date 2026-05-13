import LeanFX2.Reducibility.TypedCR2Compound.IdentityLambda
import LeanFX2.Reducibility.TypedCR2Compound.FunctionLike
import LeanFX2.Reducibility.TypedCR2Compound.Eliminators

/-! # LeanFX2.Reducibility.TypedCR2Compound — K12.20.U4 compound cascade (shim)

Carved into three sub-modules along the compound-arm cascade:

| Sub-module                                       | Phase                              |
| ------------------------------------------------ | ---------------------------------- |
| `TypedCR2Compound.IdentityLambda`                | K12.20.U4 identity-λ SN-direct     |
| `TypedCR2Compound.FunctionLike`                  | K12.20.F-L function/inductive arms |
| `TypedCR2Compound.Eliminators`                   | K12.20.M-T eliminator/projection   |

Existing `import LeanFX2.Reducibility.TypedCR2Compound` consumers
see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.TypedCR2Wrapup`
and the top-level `Reducibility` shim. -/
