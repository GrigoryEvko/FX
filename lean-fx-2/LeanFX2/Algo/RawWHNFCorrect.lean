import LeanFX2.Algo.RawWHNFCorrect.Base
import LeanFX2.Algo.RawWHNFCorrect.ElimInversions
import LeanFX2.Algo.RawWHNFCorrect.Headline
import LeanFX2.Algo.RawWHNFCorrect.Corollary

/-! # LeanFX2.Algo.RawWHNFCorrect — raw WHNF correctness (shim)

Soundness of the raw WHNF evaluator: every output of
`RawTerm.whnf` is reachable from its input via the
reflexive-transitive closure of parallel reduction.  Combined
with confluence (Phase 6.C), this yields a fuel-bounded
convertibility checker on raw terms.

| Sub-module       | Contents                                       |
| ---------------- | ---------------------------------------------- |
| `Base`           | `lamBody?` / `pairComponents?` / `natSuccPred?` inversions |
| `ElimInversions` | `listConsParts?` / `optionSomeValue?` / `either*Value?` inversions |
| `Headline`       | `RawTerm.whnf_reaches` — the soundness theorem |
| `Corollary`      | `whnf_agreement_join`, `checkConv`, soundness, refl |

## Root status

Layer 3 algorithm aggregator. -/
