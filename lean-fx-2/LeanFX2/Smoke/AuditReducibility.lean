import LeanFX2.Smoke.AuditReducibility.Base
import LeanFX2.Smoke.AuditReducibility.Weakening
import LeanFX2.Smoke.AuditReducibility.VarShape
import LeanFX2.Smoke.AuditReducibility.CumulModalLam
import LeanFX2.Smoke.AuditReducibility.PiPathSigma
import LeanFX2.Smoke.AuditReducibility.IdentityHoTT
import LeanFX2.Smoke.AuditReducibility.NaturalsAndIntervals
import LeanFX2.Smoke.AuditReducibility.NeutralsAndCodes
import LeanFX2.Smoke.AuditReducibility.TermSN
import LeanFX2.Smoke.AuditReducibility.SubstHEq
import LeanFX2.Smoke.AuditReducibility.StableAndVarShape

/-! # LeanFX2.Smoke.AuditReducibility — Tait reducibility audit log (shim)

This module aggregates the per-family smoke audit logs for the Tait
reducibility metatheory (K12.1-K12.20+).  The original 1437-line flat
log was split into eleven focused sub-modules; this shim re-exports
them so existing import sites continue to resolve.

| Sub-module                | Coverage                                                                                  |
| ------------------------- | ----------------------------------------------------------------------------------------- |
| `Base`                    | Base predicates + closed-leaf RC arms + nullary-introducer fundamentals (K12.1-K12.4)     |
| `Weakening`               | `Reducible.weaken_*`, `IsRenamingStable*`, cast/HEq glue, app/pair SN aux                 |
| `VarShape`                | Variable-shape SN gates + per-Ty `_of_varShape` headlines                                 |
| `CumulModalLam`           | `cumulUp`/`subsume`/`modIntro`/`modElim` fundamentals + `lam_at_arrow` cascade            |
| `PiPathSigma`             | dep-Pi/path/sigma/record/refine fundamentals + boolElim/idJ/oeqJ/idStrictRec              |
| `IdentityHoTT`            | HoTT identity / oeq / idStrict / equiv / pathApp / glue / codata fundamentals             |
| `NaturalsAndIntervals`    | Nat eliminators, list/option/either matchers, interval/session/effect SN + fundamentals   |
| `NeutralsAndCodes`        | `IsNeutral` + `par_preserves` + type-code SN (universe/arrow/piTy/sigma/...)              |
| `TermSN`                  | Term-level SN per ctor + `step_preserves` closed leaves + neutral-closure family          |
| `SubstHEq`                | `Term.weaken_subst_singleton_*_heq` family + cast glue + `TermSubst.*`                    |
| `StableAndVarShape`       | `ReducibleSubst` lifts + identity-subst chain + per-Ty varShape/progress + `_stable` set  |

Total: 813 `#print axioms` gates, identical to the pre-split file.

## Root status

Layer S smoke aggregator.  Pre-merge gating fires when each sub-module
elaborates; this shim contains no gates of its own. -/
