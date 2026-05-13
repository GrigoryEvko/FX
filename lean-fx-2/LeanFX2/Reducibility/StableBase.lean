import LeanFX2.Reducibility.StableBase.ClosedWeakens
import LeanFX2.Reducibility.StableBase.LamFundamentals
import LeanFX2.Reducibility.StableBase.CubicalSN
import LeanFX2.Reducibility.StableBase.SubtermSN

/-! # LeanFX2.Reducibility.StableBase — K12.20.U4 stable base (shim)

Carved into four sub-modules along the stable-fundamental cascade:

| Sub-module                            | Family                          |
| ------------------------------------- | ------------------------------- |
| `StableBase.ClosedWeakens`            | 10 closed-leaf weakens + stable |
| `StableBase.LamFundamentals`          | compound weakens + λ at arrow   |
| `StableBase.CubicalSN`                | path / transport / hcomp SN     |
| `StableBase.SubtermSN`                | shape-specialized subterm SN    |

Existing `import LeanFX2.Reducibility.StableBase` consumers see the
full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by NeutralSN* cascade and
top-level `Reducibility` shim. -/
