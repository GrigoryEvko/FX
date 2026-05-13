import LeanFX2.Reduction.ConvCumulHomo.Relation
import LeanFX2.Reduction.ConvCumulHomo.Bridge
import LeanFX2.Reduction.ConvCumulHomo.BentonHeadlines
import LeanFX2.Reduction.ConvCumulHomo.CumulSide
import LeanFX2.Reduction.ConvCumulHomo.Dispatch

/-! # LeanFX2.Reduction.ConvCumulHomo — homogeneous cumulativity Conv (shim)

Sister inductive to `ConvCumul` (in `Reduction/Cumul.lean`) that
excludes the cross-context `viaUp` constructor.  Plus Pattern 2
(Benton-Hur-Kennedy-McBride JAR'12) recursive `rename` / `subst`
compatibility headlines, complementary viaUp helpers, and a Pattern 2
dispatch-sum + 4 route theorems for unified caller-evidence routing.

| Sub-module      | Family                                                        |
| --------------- | ------------------------------------------------------------- |
| Relation        | Inductive `ConvCumulHomo` with 26 ctors                       |
| Bridge          | `toCumul` + BHKM cast-elim primitives                         |
| BentonHeadlines | Recursive Pattern 2 rename/subst Benton headlines             |
| CumulSide       | ConvCumul-output BHKM headlines + viaUp outer-side helpers    |
| Dispatch        | `SubstDispatch` sum + 4 per-branch route theorems             |

A unified `ConvCumul a b → ConvCumul (a.subst σ) (b.subst σ)` is
ill-typed for `viaUp` (heterogeneous endpoint scopes); the
`*_homo_benton` / `*_viaUp` pair covers all ConvCumul shapes at the
correct typing.

## Root status

Layer 3 reduction aggregator. -/
