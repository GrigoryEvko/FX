import LeanFX2.Confluence.Cd

/-! # Confluence/CdLemma — every parallel reduct lands in cd t

The headline lemma:

```lean
theorem Step.par.cd_lemma : Step.par t t' → Step.par t' (Term.cd t)
```

If `t` parallel-reduces to `t'`, then `t'` further reduces to
`Term.cd t` (the complete development).  Equivalently: cd is a
"maximal" parallel reduct.

## Why

This is half of the diamond property.  Combined with reflexivity
(`Step.par t (Term.cd t)`), it gives:
* From `t`, reach `t1` and `t2` via two Step.par chains
* Both `t1` and `t2` reach `Term.cd t` via cd_lemma
* Diamond: common reduct is `Term.cd t`

## Proof shape

Structural induction on `Step.par t t'`.  ~54 cases (one per ctor
+ Deep variants).  Each case proves: given that the subtrees
parallel-reduce, the cd of the original term reduces to the cd of
the parallel reduct.

* refl t: cd_lemma's chain is `Step.par.refl (Term.cd t)`.
* cong rules: structural — apply cd to subtrees, use IH.
* β-rules: the β-redex contracts in cd, so the parallel reduct
  reaches `subst0 cd_body cd_arg` via Step.par chains using
  `subst_compatible` on the body chain + argument-side pointwise lift.

## Dependencies

* `Confluence/Cd.lean`
* `Reduction/Compat.lean` — for subst_compatible in β-arms

## Downstream consumers

* `Confluence/Diamond.lean` — diamond
* `Confluence/ChurchRosser.lean` — multi-step confluence

## Diff from lean-fx

In lean-fx, this was W8.3 — the "cd_monotone aggregator" — proved
across 13 sub-tasks (W8.3a through W8.3i) totaling ~3000 lines of
Lean.  Major chunks were:
* parStarWithBi paired-predicate machinery (~2000 lines)
* W8.3d β-shallow cases (4 cases via parWithBi)
* W8.3e ι-shallow cases (13)
* W8.3f Deep βι cases (17)
* W8.3g aggregator
* W8.3h cdIter chain

In lean-fx-2:
* No paired-predicate workaround (raw-aware Term has direct typed
  inversions)
* β-cases are direct (no `subst0_term_subst_HEq` needed; raw indices
  align)
* Total target ~800-1000 lines (vs ~3000 in lean-fx)

## Implementation plan (Phase 4)

Port from lean-fx's `Reduction/CdParMono.lean` + `Reduction/CdLemmaStar.lean`
+ `Reduction/CdLemmaStarWithBi.lean`, but:
* Use direct typed inversions (lean-fx-2's raw-aware Term)
* Drop parWithBi machinery
* β-arms use Term.subst0 directly
-/

namespace LeanFX2

end LeanFX2
