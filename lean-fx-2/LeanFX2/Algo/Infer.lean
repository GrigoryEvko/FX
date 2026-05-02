import LeanFX2.Term
import LeanFX2.Algo.DecConv

/-! # Algo/Infer — type inference for synthesizable Term forms

Bidirectional type checking has two modes:
* `infer` — type can be synthesized from the term's structure
* `check` — type is given, term must match it

This file handles **inference**.  `Algo/Check.lean` handles **checking**.

## Synthesizable forms

Inference works for forms whose result type is determined by
sub-term types:
* `var i` — type from `varType ctx i`
* `app fn arg` — infer fn's arrow type, check arg against domain,
  return codomain
* `appPi fn arg` — infer fn's piTy, check arg against domain,
  substitute and return
* `fst pairTerm` — infer pairTerm's sigmaTy, return first component type
* `snd pairTerm` — return second component substituted with first
* `idJ baseCase witness` — infer witness's id type, infer base's type
* `boolElim/natElim/listElim/etc.` — synth scrutinee type, return
  branch type (when branches have explicit type annotation)
* `Term.refl rawWitness` — needs context (no inference; check mode only)

## Synthesis function signature

```lean
def Term.infer (ctx : Ctx mode level scope) (raw : RawTerm scope) :
    Option (Σ ty, Term ctx ty raw)
```

Given a raw term + context, attempts to infer a typed Term whose raw
form is `raw`.  Returns `Option` because:
* Some raw terms are not well-typed in the given context
* Some forms are check-only (lam without type annotation)

## Dependencies

* `Term.lean`
* `Algo/DecConv.lean` — Conv check at sub-term boundaries

## Downstream

* `Algo/Check.lean` — infer is a sub-routine of check
* `Algo/Synth.lean` — atomic synthesis cases
* `Surface/Elab.lean` — elaboration uses infer/check

## Implementation plan (Layer 9)

1. Define `Term.infer` by structural recursion on `raw`
2. Each ctor case: synthesize sub-term types, build typed Term
3. Smoke: identity function applied to unit

Target: ~400 lines.
-/

namespace LeanFX2.Algo

-- TODO Layer 9: Term.infer per RawTerm ctor
-- TODO Layer 9: handle synth-only forms cleanly

end LeanFX2.Algo
