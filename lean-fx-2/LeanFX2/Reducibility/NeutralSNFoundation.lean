import LeanFX2.Reducibility.NeutralSNFoundation.PiSigma
import LeanFX2.Reducibility.NeutralSNFoundation.BoolNat
import LeanFX2.Reducibility.NeutralSNFoundation.ListOptionEither
import LeanFX2.Reducibility.NeutralSNFoundation.CubicalRecord
import LeanFX2.Reducibility.NeutralSNFoundation.EquivHott

/-! # LeanFX2.Reducibility.NeutralSNFoundation — neutral & natSucc SN (shim)

Carved into five sub-modules along the neutral-head SN cascade:

| Sub-module                                       | Family                                  |
| ------------------------------------------------ | --------------------------------------- |
| `NeutralSNFoundation.PiSigma`                    | var + Π/Σ neutral-head preservation     |
| `NeutralSNFoundation.BoolNat`                    | boolElim / natElim / natRec recursors   |
| `NeutralSNFoundation.ListOptionEither`           | parametric inductive recursors          |
| `NeutralSNFoundation.CubicalRecord`              | pathApp + glueElim + refineElim + recordProj + codataDest |
| `NeutralSNFoundation.EquivHott`                  | equivApp + equivApply + idJ             |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.NeutralSNHott`,
`Reducibility.NeutralSNIntro`, `Reducibility.NeutralSNClosure`, and
the top-level `Reducibility` shim. -/
