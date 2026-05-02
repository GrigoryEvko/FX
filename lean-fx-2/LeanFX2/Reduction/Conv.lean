import LeanFX2.Reduction.StepStar

/-! # Reduction/Conv — definitional conversion (∃-StepStar form)

**Architectural decision**: Conv is defined as the existential
"common reduct" relation, NOT as an inductive with cong rules.

```lean
def Conv (t1 t2 : Term ctx ty raw) : Prop :=
  ∃ t', StepStar t1 t' ∧ StepStar t2 t'
```

Wait — but `t1` and `t2` may have different raws.  Conv allows
them.  The `t'` has both source raws reduce to its raw.  More
precisely:

```lean
def Conv {raw1 raw2 : RawTerm scope}
    (t1 : Term ctx ty raw1) (t2 : Term ctx ty raw2) : Prop :=
  ∃ rawCommon (t' : Term ctx ty rawCommon),
    StepStar t1 t' ∧ StepStar t2 t'
```

## Why ∃-StepStar instead of inductive Conv

In lean-fx (W14 mapStep refactor era), `Conv` was inductive with
13 cong rules + refl + sym + trans.  Each cong rule was a 4-line
induction that the W14 refactor collapsed into a 1-line `mapStep`
application.

But the deeper observation: **Conv is uniquely characterized as
∃-StepStar** (this is the Church-Rosser corollary's actual content).
Defining it that way:

1. **Decidable conversion** is direct: WHNF both sides, compare,
   recurse.  No inductive Conv structure to navigate.
2. **Cong rules become 1-line** corollaries of `StepStar.mapStep`
   (3-line proofs):
   ```lean
   theorem Conv.app_cong (h : Conv f f') (a) : Conv (Term.app f a) (Term.app f' a) := by
     obtain ⟨_, t', s1, s2⟩ := h
     exact ⟨_, Term.app t' a, StepStar.mapStep _ Step.appLeft s1, StepStar.mapStep _ Step.appLeft s2⟩
   ```
3. **Trans, sym are direct**: ∃-flavored, no induction.
4. **Decidability** (Layer 9 `Algo/DecConv.lean`) reduces to
   StepStar termination + WHNF equality — clean separation.

## Refl, sym, trans

```lean
theorem Conv.refl (t : Term ctx ty raw) : Conv t t :=
  ⟨_, t, StepStar.refl t, StepStar.refl t⟩

theorem Conv.sym (h : Conv t1 t2) : Conv t2 t1 := by
  obtain ⟨_, t', s1, s2⟩ := h; exact ⟨_, t', s2, s1⟩

theorem Conv.trans (h12 : Conv t1 t2) (h23 : Conv t2 t3) : Conv t1 t3 := by
  -- requires Church-Rosser confluence: from h12 reach common t12',
  --   from h23 reach common t23'.  Confluence between t12' and t23'
  --   gives a final common reduct.
  ...
```

Trans **needs Church-Rosser** to combine two convergence triangles.
This is fine — Church-Rosser is proved in Layer 3 (`Confluence/`),
which we depend on.

## Cong rules (1-line each via mapStep)

* `Conv.app_cong_left/right`, `Conv.lam_cong`
* `Conv.appPi_cong`, `Conv.lamPi_cong`
* `Conv.pair_cong`, `Conv.fst_cong`, `Conv.snd_cong`
* `Conv.boolElim_cong`, `Conv.natElim_cong`, etc.
* `Conv.idJ_cong`

Each is a `obtain ⟨_, t', s1, s2⟩` destructure + `StepStar.mapStep`
on each chain.  ~3 lines per cong.

## Dependencies

* `Reduction/StepStar.lean`
* (`Confluence/ChurchRosser.lean` for `Conv.trans` — circular?
  Solved by stating `Conv.trans` AFTER Church-Rosser, in Layer 4
  or moving it to `Confluence/CanonicalForm.lean`.)

## Downstream consumers

* `Algo/DecConv.lean` — decidable Conv instance
* `Algo/Check.lean` — bidirectional check uses Conv
* All elaboration — Conv determines type equality

## Diff from lean-fx

* lean-fx's `Conv` is inductive with 13 cong rules + refl/sym/trans
  ctors (~330 lines)
* lean-fx-2's `Conv` is `def` ≅ ∃-StepStar (~80 lines)
* `Conv.trans` is proved (not a constructor) using Church-Rosser
* `Decidable Conv` (lean-fx task #909) becomes algorithmically
  natural

## Implementation plan (Phase 3)

1. Define `Conv` as `def ... := ∃ t', StepStar t1 t' ∧ StepStar t2 t'`
2. `Conv.refl`, `Conv.sym` directly
3. `Conv.trans` deferred to Layer 4 (`Confluence/`)
4. Cong shortcuts as `mapStep` corollaries
-/

namespace LeanFX2

end LeanFX2
