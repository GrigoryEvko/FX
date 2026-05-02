import LeanFX2.Algo.WHNF
import LeanFX2.Reduction.Step

/-! # Algo/Eval — fuel-bounded evaluator

```lean
def Term.eval (fuel : Nat) (term : Term ctx ty raw) :
    Σ (raw' : RawTerm scope), Term ctx ty raw'
```

Reduces a typed Term by repeatedly firing β/ι rules.  Fuel parameter
ensures termination even before SN is proven.

## Why fuel-bounded

Strong normalization is a separate metatheorem (Tait's reducibility).
Until SN is proven for the full kernel (with all 19 dimensions), the
evaluator must guard against non-termination via explicit fuel.

For Tot effect terms (default): fuel suffices (SN guaranteed).
For `Div`-effect terms: fuel is essential (terms may diverge).

## Reduction strategy

Call-by-name to start (head reduction first); switch to call-by-value
when needed for performance.  The reduction order doesn't affect
correctness (Church-Rosser confluence) but affects evaluator speed.

## Dependencies

* `Algo/WHNF.lean`
* `Reduction/Step.lean`

## Downstream

* `Pipeline.lean` — end-to-end pipeline runs eval at the end
* User-level tests / smoke

## Implementation plan (Layer 9)

1. Define `Term.eval` recursive (with fuel parameter)
2. Each Term ctor: dispatch based on β/ι fireability
3. Smoke: identity application, addition on naturals, list reduction

Target: ~300 lines.
-/

namespace LeanFX2.Algo

-- TODO Layer 9: Term.eval with fuel
-- TODO Layer 9: smoke tests

end LeanFX2.Algo
