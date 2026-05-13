import LeanFX2.Reducibility.NeutralSNHott.HottJ
import LeanFX2.Reducibility.NeutralSNHott.ElimVarShape
import LeanFX2.Reducibility.NeutralSNHott.NatElim
import LeanFX2.Reducibility.NeutralSNHott.NatRecAndOption

/-! # LeanFX2.Reducibility.NeutralSNHott — K12.20.C HOTT-J recursors (shim)

Carved into four sub-modules along the K12.20.C HOTT cascade:

| Sub-module                                | Family                              |
| ----------------------------------------- | ----------------------------------- |
| `NeutralSNHott.HottJ`                     | oeqJ + idJ + idStrictRec recursors  |
| `NeutralSNHott.ElimVarShape`              | var-shape eliminators + natSucc     |
| `NeutralSNHott.NatElim`                   | natElim ι-rules                     |
| `NeutralSNHott.NatRecAndOption`           | natRec ι-rules + optionMatch        |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.NeutralSNIntro*`
and the top-level `Reducibility` shim. -/
