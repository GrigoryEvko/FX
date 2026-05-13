import LeanFX2.Reducibility.TypedCR2Direct.StepPreservesDirect
import LeanFX2.Reducibility.TypedCR2Direct.VarShapeDirect
import LeanFX2.Reducibility.TypedCR2Direct.VarShapeCompoundCubical
import LeanFX2.Reducibility.TypedCR2Direct.VarShapeCompoundParametric

/-! # LeanFX2.Reducibility.TypedCR2Direct — K12.20.D / E / U2 / AZ (shim)

Carved into four sub-modules along the K12.20.D/E/U2/AZ cascade:

| Sub-module                                       | Family                                       |
| ------------------------------------------------ | -------------------------------------------- |
| `TypedCR2Direct.StepPreservesDirect`             | K12.20.D step_preserves SN-direct arms       |
| `TypedCR2Direct.VarShapeDirect`                  | K12.20.E + U2 SN-direct CR3 closures         |
| `TypedCR2Direct.VarShapeCompoundCubical`         | K12.20.AZ arrow / sigmaTy / path / glue arms |
| `TypedCR2Direct.VarShapeCompoundParametric`      | K12.20.AZ equiv / refine / record / codata + parametric + HoTT arms |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.TypedCR2Generic`,
`Reducibility.TypedCR2Compound`, and the top-level `Reducibility` shim. -/
