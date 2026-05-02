import LeanFX2.Confluence.Diamond

/-! # Confluence/ChurchRosser — multi-step confluence

Step.parStar (the RT closure of Step.par) is confluent:

```lean
theorem Step.parStar.confluence
    (chain1 : Step.parStar t t1) (chain2 : Step.parStar t t2) :
    ∃ t', Step.parStar t1 t' ∧ Step.parStar t2 t'
```

## Proof — Tait-Martin-Löf strip lemma

By induction on `chain1`:
* refl: take `t' := t2`, both chains end there
* trans (Step.par t a) (chain a t1):
  * From the diamond on the first par step (`Step.par t a` and
    chain2 starting from t), get a join point
  * Recurse on chain1's tail to extend

Diamond on parallel reduction strictifies to multi-step confluence.

## Confluence on Step (single-step) follows

Because:
* Each `Step` is a `Step.par` (every single-step reduction is also
  a parallel-reduction with all-other-positions held by refl)
* `StepStar` is the RT closure of Step
* `Step.parStar` (RT closure of Step.par) coincides with StepStar

So:

```lean
theorem StepStar.confluence
    (chain1 : StepStar t t1) (chain2 : StepStar t t2) :
    ∃ t', StepStar t1 t' ∧ StepStar t2 t'
```

falls out of `Step.parStar.confluence`.

## Dependencies

* `Confluence/Diamond.lean`

## Downstream consumers

* `Confluence/CanonicalForm.lean` — `Conv.canonical_form`
* `Reduction/Conv.lean` — `Conv.trans` (proved here, not in Conv.lean,
  to avoid circular dep — Conv.trans needs confluence)
* `Algo/DecConv.lean` — decidable conversion

## Implementation plan (Phase 4)

Port from `lean-fx/LeanFX/Syntax/Reduction/Confluence.lean`.  Strip
lemma is ~50 lines, multi-step confluence is the standard induction.
-/

namespace LeanFX2

end LeanFX2
