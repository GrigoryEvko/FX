import LeanFX2.Reducibility.Basic
import LeanFX2.Reducibility.Neutral.ModalAdvancedPreservation
import LeanFX2.Reducibility.SNHelpers
import LeanFX2.Reducibility.StableBase.SubtermSN
import LeanFX2.Reducibility.NeutralSNFoundation.EquivHott
import LeanFX2.Reducibility.NeutralSNHott.NatRecAndOption
import LeanFX2.Reducibility.NeutralSNIntro.Codes
import LeanFX2.Reducibility.NeutralSNClosure.GlueEquiv
import LeanFX2.Term.SN.DirectCases
import LeanFX2.Reducibility.Kripke.Headline

/-! # LeanFX2.Reducibility — strong-normalization predicate layer

The legacy `Reducible` Tait predicate (defined by recursion on Ty)
plus its `Classifier` / `Foundation` / `StableBase` / `TypedCR2*` /
`FundamentalWrappers` / `FundamentalEliminators` / `FundamentalCubical`
cascade has been deleted in favor of the bypass-free Kripke
step-indexed predicate at `Reducibility.Kripke`.  This aggregator
re-exports only the surviving bypass-free modules:

| Module                                | Role                                              |
| ------------------------------------- | ------------------------------------------------- |
| `Reducibility.Basic`                  | `RawTerm.isStronglyNormalizing` base inductive    |
| `Reducibility.Neutral.*`              | `RawTerm.IsNeutral` neutrality predicate          |
| `Reducibility.SNHelpers`              | pure SN preservation lemmas (closed leaves / cong)|
| `Reducibility.StableBase.SubtermSN`   | shape-specialized subterm SN inversions           |
| `Reducibility.NeutralSNFoundation.*`  | per-ctor neutral SN preservation (foundation)     |
| `Reducibility.NeutralSNHott.*`        | HoTT / J-family neutral SN closures               |
| `Reducibility.NeutralSNIntro.*`       | Σ / modal / list-cons neutral SN closures         |
| `Reducibility.NeutralSNClosure.*`     | type-code / cubical / record cong SN closures     |
| `Term.SN.DirectCases` | Term-level SN endpoints (intro / cong / elim) |
| `Reducibility.Kripke.Headline`        | Kripke step-indexed reducibility + fundamental    |

## Root status

Layer 3 metatheory aggregator.  Bypass-free since the K12.20 Kripke
refactor: every shipped declaration is a `theorem` / `lemma` / `def`
over the bypass-free surface above.  Consumers (notably
`LeanFX2.Kernel`) import this aggregator to pick up the Kripke
headline + the per-ctor SN preservation lemmas without naming each
sub-module. -/
