import LeanFX2.Algo.WHNF
import LeanFX2.Reduction.Conv
import LeanFX2.Confluence.CanonicalForm

/-! # Algo/DecConv — decidable definitional conversion

```lean
instance : Decidable (Conv t1 t2)
```

Given the ∃-StepStar definition of Conv (per `Reduction/Conv.lean`)
and Church-Rosser confluence (per `Confluence/ChurchRosser.lean`),
decidable conversion follows the standard algorithm:

1. WHNF both sides
2. If heads disagree → not convertible
3. If heads agree → recurse on sub-terms
4. At binders, descend under (`alpha`-equivalence handled by de Bruijn)

## Why this works

Conv = ∃-StepStar is decidable iff WHNF terminates (it does — Step
is strongly normalizing on well-typed terms, given confluence + SN).
Church-Rosser ensures the WHNF reached from t1 and t2 is unique up
to structural equality.

## Termination

Decidable conversion needs strong normalization of the typed
calculus.  This is a separate metatheoretic theorem (Layer 9.5 —
`Algo/SN.lean` if added) usually proved by Tait's logical relations
or Girard's reducibility.  For lean-fx-2's βι-only fragment with η
isolated, SN is provable.

## Dependencies

* `Algo/WHNF.lean`
* `Reduction/Conv.lean`
* `Confluence/CanonicalForm.lean` — the canonical form lemma underwrites
  the algorithm

## Downstream

* `Algo/Check.lean` — bidirectional checker uses `Decidable Conv`
* `Surface/Elab.lean` — elaboration uses Conv to discharge type
  ambiguity

## Implementation plan (Layer 9)

1. Define decidable conversion algorithm
2. Provide `Decidable (Conv t1 t2)` instance
3. Smoke: trivial conversion (refl), β-conversion, η-rejection
4. Performance smoke: complex term conversion is sub-second

Target: ~300 lines.

## Diff from lean-fx

lean-fx had this on the roadmap as task #909.  Decidable Conv was
deferred until Wave 10 (Conv as ∃-StepStar refactor) lands.  In
lean-fx-2, Conv IS ∃-StepStar from day 1, so DecConv lands directly.
-/

namespace LeanFX2.Algo

-- TODO Layer 9: WHNF-based conversion algorithm
-- TODO Layer 9: Decidable instance
-- TODO Layer 9: alpha-equivalence handling (de Bruijn — should be free)

end LeanFX2.Algo
