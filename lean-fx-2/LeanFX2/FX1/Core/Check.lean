prelude
import LeanFX2.FX1.Core.Check.CheckEntry

/-! # LeanFX2.FX1.Core.Check — FX1 minimal-kernel type checker (shim)

Carved into six sub-modules along the checker-pipeline axis:

| Sub-module | Family |
| --- | --- |
| `CheckBeq` | Option / Level / Expr checker equality + soundness |
| `CheckLookup` | Environment + Context witness-producing lookup + soundness |
| `CheckReduction` | Weak-head normalization + weak-head def-eq + soundness |
| `CheckInferCore` | `InferResult` envelope, `inferCore?` driver, bvar/sort/const/pi/lam branch soundness |
| `CheckInferApp` | App-branch soundness, impossible-branch lemma, `inferCore_sound` aggregate |
| `CheckEntry` | `checkCore?` + proof-carrying `inferResult?` / `infer?` / `check?` entry points + smoke battery |

## Root status

Root-FX1 checker shim. -/
