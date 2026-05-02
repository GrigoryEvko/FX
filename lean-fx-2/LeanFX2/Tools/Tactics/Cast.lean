/-! # Tools/Tactics/Cast — cast helpers for Step / Step.par

`Step.castBoth`, `Step.castSource`, `Step.castTarget`, and
`Step.par.cast{Both,Source,Target}` thread Eq through Step inhabitants
when types align via Eq.  These show up frequently in subst β-arms.

## Helpers

```lean
def Step.castBoth (typeEq : ty1 = ty2) (sourceEq : raw1 = raw1')
    (targetEq : raw2 = raw2')
    (s : Step (ctx := ctx) (ty := ty1) src tgt) :
    Step (ctx := ctx) (ty := ty2) ... := ...

def Step.castSource (sourceEq : raw1 = raw1')
    (s : Step (ctx := ctx) (ty := ty) src tgt) :
    Step (ctx := ctx) (ty := ty) ... := ...

def Step.castTarget (targetEq : raw2 = raw2')
    (s : Step (ctx := ctx) (ty := ty) src tgt) :
    Step (ctx := ctx) (ty := ty) ... := ...
```

Plus parallel `Step.par.cast*` variants.

## Why cast helpers

In β-rule's RHS (e.g., `Term.subst0 body arg`), the resulting type
sometimes needs cast through `Ty.weaken_subst_singleton` or similar.
Threading these casts through Step inhabitants keeps the proofs
clean.

## In lean-fx-2

Casts are needed less than in lean-fx because:
* Subst is unified — no `subst0` vs `subst0_term` distinction
* β-rule RHS uses `Term.subst0` directly with raw indices propagating
* Only the `Ty.weaken_subst_singleton` cast remains (intrinsic to
  the algebra)

## Dependencies

* `Reduction/Step.lean`, `Reduction/ParRed.lean`

## Downstream

* `Reduction/Compat.lean`
* `Confluence/CdLemma.lean`

## Implementation plan (Layer 12)

1. Define `Step.cast*` and `Step.par.cast*` helpers
2. Smoke: round-trip cast (cast + reverse-cast = identity)

Target: ~200 lines.
-/

namespace LeanFX2.Tools.Tactics

-- TODO Layer 12: Step.castBoth/Source/Target
-- TODO Layer 12: Step.par.cast{Both,Source,Target}

end LeanFX2.Tools.Tactics
