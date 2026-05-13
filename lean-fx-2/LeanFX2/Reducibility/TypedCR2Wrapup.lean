import LeanFX2.Reducibility.TypedCR2Wrapup.LeafFundamentals
import LeanFX2.Reducibility.TypedCR2Wrapup.IntervalSessionEffect
import LeanFX2.Reducibility.TypedCR2Wrapup.TypeCodesFundamental
import LeanFX2.Reducibility.TypedCR2Wrapup.TypeCodesSN

/-! # LeanFX2.Reducibility.TypedCR2Wrapup — K12.20.U cascade (shim)

Carved into four sub-modules along the K12.20.U headline cascade:

| Sub-module                                       | Family                                |
| ------------------------------------------------ | ------------------------------------- |
| `TypedCR2Wrapup.LeafFundamentals`                | `step_preserves` + nat/list/option/either |
| `TypedCR2Wrapup.IntervalSessionEffect`           | interval + session + effect           |
| `TypedCR2Wrapup.TypeCodesFundamental`            | universe / arrow / piTy / sigma / etc |
| `TypedCR2Wrapup.TypeCodesSN`                     | identity-M04 SN + cumulUp             |

Existing `import LeanFX2.Reducibility.TypedCR2Wrapup` consumers
see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.Fundamental*`
modules and the top-level `Reducibility` shim. -/
