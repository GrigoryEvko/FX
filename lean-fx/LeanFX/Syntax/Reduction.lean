import LeanFX.Syntax.Reduction.Compatible
import LeanFX.Syntax.Reduction.ParSubst
import LeanFX.Syntax.Reduction.RawPar
import LeanFX.Syntax.Reduction.RawParInversion
import LeanFX.Syntax.Reduction.RawParCompatible
import LeanFX.Syntax.Reduction.RawCdLemma
import LeanFX.Syntax.Reduction.RawConfluence

/-! # Reduction theory umbrella module.

Re-exports the typed and raw reduction layers in dependency order:

  * `Compatible` — `Step` rename/subst compatibility.
  * `ParSubst` — `Step.par` rename/subst compatibility plus
    `Step.parStar` chain congruences (`lam_cong`, `app_cong`,
    `pair_cong`, etc.).
  * `RawPar` — `RawTerm`-level parallel reduction.
  * `RawParInversion` — source-direction inversion lemmas at
    raw level (no dep-elim wall — RawTerm has no Ty index).
  * `RawParCompatible` — raw-level rename/subst compatibility.
  * `RawCdLemma` — raw-level cd_lemma (parallel reduct of any
    parStep lands in `RawTerm.cd t`).
  * `RawConfluence` — raw-level diamond + Church-Rosser via
    `RawCdLemma`.

The typed reduction layer (`Step`, `StepStar`, `Conv`,
`Step.par`, `Step.parStar`, `Step.par.isBi`, etc.) lives under
`Reduction/` and is re-exported transitively via these imports.
The raw layer is the safety net for typed proofs: when typed
dep-elim walls block a proof, the same lemma at the raw level
plus a `toRawBridge` lift discharges it.

The cd-development pair (`Term.cd` + `Step.par.cd_dominates`)
is in `CompleteDevelopment.lean` and `CdDominates.lean`, NOT
under `Reduction/`, because they construct the development
function rather than reason about the reduction relation. -/
