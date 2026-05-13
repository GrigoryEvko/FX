import LeanFX2.Reduction.Compat.HoTT.IdentityFamily
import LeanFX2.Reduction.Compat.HoTT.EquivalenceFamily
import LeanFX2.Reduction.Compat.HoTT.FunextFamily
import LeanFX2.Reduction.Compat.HoTT.UnivalenceFamily

/-! # LeanFX2.Reduction.Compat.HoTT — HoTT rename/subst compat (shim)

Aggregator for the typed compositional `rename`/`subst` compat
lemmas of HoTT-layer cong constructors.  The body was split into
four per-family sub-modules under `LeanFX2/Reduction/Compat/HoTT/`
(REFACTOR-COMPAT #1556) to keep this file under the 1000-line
ceiling; this shim re-exports them so existing call sites can
continue to `import LeanFX2.Reduction.Compat.HoTT` and reference
`LeanFX2.Step.par.XCong.{rename,subst}_compatible` unchanged.

| Sub-module           | Family                                                 |
| -------------------- | ------------------------------------------------------ |
| `IdentityFamily`     | `oeqReflCong`, `oeqJCong`, `oeqFunextCong`, `reflCong` |
| `EquivalenceFamily`  | `equivAppCong`, `equivIntroCong`, `equivIntroHetCong`  |
| `FunextFamily`       | `funextReflCong`, `funextReflAtIdCong`, `funextIntroHetCong` |
| `UnivalenceFamily`   | `uaIntroHetCong`, `uaToEquivCong`, `equivApplyCong`    |

Total: 13 per-ctor namespaces × 2 (rename + subst) = 26 theorems,
all zero-axiom under `#print axioms` and namespace-stable across
the split.

## Root status

Layer 2 reduction-compat aggregator. -/
