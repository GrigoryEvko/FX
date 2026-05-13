import LeanFX2.Reduction.Cumul.Relation
import LeanFX2.Reduction.Cumul.Promotion
import LeanFX2.Reduction.Cumul.BackwardCompat
import LeanFX2.Reduction.Cumul.SubstOuter
import LeanFX2.Reduction.Cumul.SubstCompatCases
import LeanFX2.Reduction.Cumul.SubstCompatCong
import LeanFX2.Reduction.Cumul.SubstCompatTerm

/-! # LeanFX2.Reduction.Cumul — cross-level universe cumulativity (shim)

Real cross-level universe cumulativity (Option C), carved into six
sub-modules along the function-of-the-theorems axis.  The original
parent file was a 2075-line monolith; this shim re-exports the
same declarations through topical sub-files so that downstream
consumers (`LeanFX2.Reduction.CumulSubstCompat`,
`LeanFX2.Reduction.CumulAllais`, `LeanFX2.Reduction.CumulBenton`,
`LeanFX2.Smoke.AuditPhase12A2Cumul`, …) see the full set without
modification.

| Sub-module                              | Contents                                                    |
| --------------------------------------- | ----------------------------------------------------------- |
| `Cumul.Relation`                        | The substantive `inductive ConvCumul` relation              |
| `Cumul.Promotion`                       | Real term-promotion + raw-form projection                   |
| `Cumul.BackwardCompat`                  | Old Option A theorems preserved for downstream callers      |
| `Cumul.SubstOuter`                      | Phase 6 closed-source subst-compatibility + `cumul_outer_eq` |
| `Cumul.SubstCompatCases`                | Phase 6-finish refl / sym / trans subst-compat helpers      |
| `Cumul.SubstCompatCong`                 | Per-cong-ctor subst-compat building blocks                  |
| `Cumul.SubstCompatTerm`                 | CUMUL-1.7 per-Term-shape `subst_compatible_*` helpers       |

## Root status

Layer 3 reduction aggregator. -/
