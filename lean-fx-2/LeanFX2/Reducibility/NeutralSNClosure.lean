import LeanFX2.Reducibility.NeutralSNClosure.TypeCodeSN
import LeanFX2.Reducibility.NeutralSNClosure.IntervalSN
import LeanFX2.Reducibility.NeutralSNClosure.RecordRefineCodata
import LeanFX2.Reducibility.NeutralSNClosure.HottCompose
import LeanFX2.Reducibility.NeutralSNClosure.GlueEquiv

/-! # LeanFX2.Reducibility.NeutralSNClosure — K12.20.C closure (shim)

Carved into five sub-modules along the K12.20.C closure cascade:

| Sub-module                                | Family                              |
| ----------------------------------------- | ----------------------------------- |
| `NeutralSNClosure.TypeCodeSN`             | type-code raw + Term SN witnesses   |
| `NeutralSNClosure.IntervalSN`             | interval ops + path/oeqFunext       |
| `NeutralSNClosure.RecordRefineCodata`     | record / refine / codata families   |
| `NeutralSNClosure.HottCompose`            | groupoid + Layer-1 session/effect   |
| `NeutralSNClosure.GlueEquiv`              | glue / equivIntro                   |

Existing consumers see the full set without modification.

## Root status

Layer 3 metatheory aggregator.  Consumed by `Reducibility.TypedCR2*`
and the top-level `Reducibility` shim. -/
