import LeanFX2.Confluence.ChurchRosser

/-! # Confluence/CanonicalForm — Conv.canonical_form

```lean
theorem Conv.canonical_form (h : Conv t1 t2) :
    ∃ t', StepStar t1 t' ∧ StepStar t2 t'
```

If two terms are convertible, they have a common reduct.  Direct
corollary of `Conv := ∃-StepStar` (the lean-fx-2 design):

```lean
theorem Conv.canonical_form (h : Conv t1 t2) := h
```

(That is, `canonical_form` is the *definitional content* of Conv
in lean-fx-2.)

## And Conv.trans

`Conv.trans` requires Church-Rosser to compose two convergence
triangles:

```lean
theorem Conv.trans (h12 : Conv t1 t2) (h23 : Conv t2 t3) : Conv t1 t3 := by
  obtain ⟨t12', s1, s2⟩ := h12
  obtain ⟨t23', s2', s3⟩ := h23
  obtain ⟨t', join1, join2⟩ := StepStar.confluence s2 s2'
  exact ⟨_, t', s1.append join1, s3.append join2⟩
```

Lives here because it depends on `StepStar.confluence` (Layer 3).

## Dependencies

* `Confluence/ChurchRosser.lean`

## Downstream consumers

* `Algo/DecConv.lean`
* `Algo/Check.lean` — Conv.trans is used in elaboration

## Diff from lean-fx

* lean-fx's `Conv.canonical_form` was W8.4 — non-trivial in lean-fx
  because `Conv` was inductive (not ∃-StepStar).  In lean-fx-2 it's
  the identity function (one line: `:= h`).
* `Conv.trans` is proved here (lean-fx had it as a constructor of
  the inductive Conv).
-/

namespace LeanFX2

end LeanFX2
