import LeanFX2.Confluence.CdLemma

/-! # Confluence/Diamond — diamond property for Step.par

Step.par is "diamond":

```lean
theorem Step.par.diamond
    (s1 : Step.par t t1) (s2 : Step.par t t2) :
    ∃ t', Step.par t1 t' ∧ Step.par t2 t'
```

If `t` parallel-reduces to both `t1` and `t2`, there's a common
reduct `t'` reachable from both in one parallel step.

## Proof

Take `t' := Term.cd t`.  By `Step.par.cd_lemma`:
* `Step.par t1 (Term.cd t)`
* `Step.par t2 (Term.cd t)`

Done.

## Why diamond, not "joinable in many steps"

Diamond is a *single-step* convergence property of parallel
reduction.  It's strictly stronger than the multi-step property
of single Step.  This stronger property is what makes the Tait-
Martin-Löf strip lemma work for proving multi-step Step
confluence.

## Dependencies

* `Confluence/CdLemma.lean`

## Downstream consumers

* `Confluence/ChurchRosser.lean` — multi-step confluence via strip
  lemma applied to diamond

## Implementation plan (Phase 4)

Port from `lean-fx/LeanFX/Syntax/Reduction/Confluence.lean`'s
diamond section.  Tiny file (~30 lines).
-/

namespace LeanFX2

end LeanFX2
