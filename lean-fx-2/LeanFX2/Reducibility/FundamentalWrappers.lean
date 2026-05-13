import LeanFX2.Reducibility.FundamentalWrappers.ModalDestructorBase
import LeanFX2.Reducibility.FundamentalWrappers.SubsumeAtRichTypes
import LeanFX2.Reducibility.FundamentalWrappers.ModIntroAtRichTypes
import LeanFX2.Reducibility.FundamentalWrappers.SubsumeIntroAtSimpleTypes
import LeanFX2.Reducibility.FundamentalWrappers.ModElimAtAllTypes

/-! # LeanFX2.Reducibility.FundamentalWrappers — modal-destructor
fundamentals (shim)

Carved into five sub-modules along the modal Term destructor +
type-family axis:

| Sub-module                                            | Family                                          |
| ----------------------------------------------------- | ----------------------------------------------- |
| `FundamentalWrappers.ModalDestructorBase`             | base SN-direct + stable for all 3 destructors   |
| `FundamentalWrappers.SubsumeAtRichTypes`              | subsume at unit / universe / session / modal    |
| `FundamentalWrappers.ModIntroAtRichTypes`             | modIntro at unit / universe / session / modal   |
| `FundamentalWrappers.SubsumeIntroAtSimpleTypes`       | subsume + modIntro at simple closed-leaf types  |
| `FundamentalWrappers.ModElimAtAllTypes`               | modElim at every closed-leaf type               |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by
`Reducibility.FundamentalEliminators`, `FundamentalAliases`, and
the eventual SN headline corollary. -/
