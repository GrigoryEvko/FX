import LeanFX2.Algo.Infer

/-! # Algo/Synth — atomic synthesis for individual constructors

Helper module for `Algo/Infer.lean`.  Each typed-Term constructor
has a small synthesis lemma that, given typed sub-components,
produces the typed Term whose raw form aligns.

## Per-ctor synth helpers

```lean
def Term.synthVar (ctx : Ctx mode level scope) (i : Fin scope) :
    Term ctx (varType ctx i) (RawTerm.var i)
  := Term.var i

def Term.synthApp (fn : Term ctx (Ty.arrow dom cod) fnRaw)
    (arg : Term ctx dom argRaw) :
    Term ctx cod (RawTerm.app fnRaw argRaw)
  := Term.app fn arg

-- ... one per ctor
```

## Why a separate module

In lean-fx-2's raw-aware Term, synthesis IS construction — each ctor
produces a typed Term whose raw form is the type index.  Atomic
synth helpers wrap the ctor + provide consistent name/signature for
elaboration to call.

## Dependencies

* `Algo/Infer.lean`

## Downstream

* `Algo/Infer.lean` — the inference algorithm dispatches to these
* `Surface/Elab.lean` — elaboration also calls synth

## Implementation plan (Layer 9)

1. One synth helper per Term ctor (~28 helpers)
2. Each is a 1-line wrapper around the ctor
3. Smoke: each helper round-trips (synth then re-extract)

Target: ~250 lines.
-/

namespace LeanFX2.Algo

-- TODO Layer 9: synth helpers per Term ctor

end LeanFX2.Algo
