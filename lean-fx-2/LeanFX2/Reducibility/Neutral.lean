import LeanFX2.Reducibility.Neutral.NeutralCore
import LeanFX2.Reducibility.Neutral.EliminatorPreservation
import LeanFX2.Reducibility.Neutral.CubicalIdentityPreservation
import LeanFX2.Reducibility.Neutral.ModalAdvancedPreservation

/-! # LeanFX2.Reducibility.Neutral — neutral terms (shim)

Carved into four sub-modules along the inductive-definition vs
preservation axis, then by destructor family within preservation:

| Sub-module                                       | Family                                          |
| ------------------------------------------------ | ----------------------------------------------- |
| `Neutral.NeutralCore`                            | inductive predicate + not-<ctor> impossibility  |
| `Neutral.EliminatorPreservation`                 | par preservation for Π / Σ / ι eliminators      |
| `Neutral.CubicalIdentityPreservation`            | par preservation for cubical + identity         |
| `Neutral.ModalAdvancedPreservation`              | par preservation for modal + advanced + master  |

`RawTerm.IsNeutral` is the inductive predicate over `RawTerm scope`
that classifies the neutral fragment — variables and terms stuck on
an eliminator whose principal scrutinee is neutral.  CR3 needs the
closure property because the generic compound CR3 step argues "if
`term` reduces to some `term'`, then `term'` is still neutral and
the IH on the reduct re-applies".

## Root status

Layer 3 metatheory aggregator.  Consumed by the top-level
`Reducibility.lean`'s compound CR3 arms (arrow / sigmaTy / piTy /
interval / refine etc.). -/
