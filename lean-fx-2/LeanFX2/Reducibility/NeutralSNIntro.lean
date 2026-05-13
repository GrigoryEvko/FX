import LeanFX2.Reducibility.NeutralSNIntro.Sums
import LeanFX2.Reducibility.NeutralSNIntro.Modal
import LeanFX2.Reducibility.NeutralSNIntro.Lists
import LeanFX2.Reducibility.NeutralSNIntro.Codes

/-! # LeanFX2.Reducibility.NeutralSNIntro — K12.20.C ctor intros (shim)

Carved into four sub-modules along ctor families:

| Sub-module                          | Family                              |
| ----------------------------------- | ----------------------------------- |
| `NeutralSNIntro.Sums`               | `eitherInl` / `eitherInr` + matches |
| `NeutralSNIntro.Modal`              | `modIntro` / `modElim` + Σ products |
| `NeutralSNIntro.Lists`              | `listCons` / `listNil` + options    |
| `NeutralSNIntro.Codes`              | reflexivities + type codes          |

This shim re-exports every sub-module so existing consumers of
`import LeanFX2.Reducibility.NeutralSNIntro` see the full set without
modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.NeutralSNClosure`
and the top-level `Reducibility` shim. -/
