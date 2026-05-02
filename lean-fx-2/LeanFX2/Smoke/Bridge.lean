import LeanFX2.Bridge

/-! # Smoke/Bridge — typed↔raw roundtrip examples.

```lean
-- toRaw of a built Term recovers via rfl
example (i : Fin scope) :
    (Term.var (ctx := ctx) i).toRaw = RawTerm.var i := rfl

-- toRaw of β-redex recovers raw β-redex
example :
    (Term.app (Term.lam body) arg).toRaw = RawTerm.app (RawTerm.lam body.toRaw) arg.toRaw := rfl

-- typed Step.par lifts to raw RawStep.par via the bridge
example {parallelStep : Step.par t1 t2} (biW : Step.par.isBi parallelStep) :
    RawStep.par t1.toRaw t2.toRaw :=
  Step.par.toRawBridge parallelStep biW
```

## Critical edge case: refl-bearing β-redex

```lean
-- This SHOULD work in lean-fx-2 (where it doesn't in lean-fx)
example {arg : Term ctx ty argRaw} :
    (Term.app
      (Term.lam (Term.refl (RawTerm.var ⟨0, _⟩))) arg).toRaw
    = RawTerm.app (RawTerm.lam (RawTerm.refl (RawTerm.var ⟨0, _⟩))) argRaw := rfl

-- After β-reduction, the typed substitute matches raw substitute:
-- typed:  Term.refl argRaw   (after subst, refl's witness is argRaw)
-- raw:    RawTerm.refl argRaw  (singleton substitution puts argRaw at pos 0)
-- Both match because Subst.singleton.forRaw = RawTermSubst.singleton (arg.toRaw)
```

## Dependencies

* `Bridge.lean`

## Implementation plan (Layer 14)

1. toRaw round-trip on each Term ctor
2. Bridge on simple β-redex
3. Bridge on refl-bearing β-redex (the LOAD-BEARING test)
4. Bridge on idJ-bearing β-redex
-/

namespace LeanFX2.Smoke

-- TODO: bridge smoke examples — including the refl-bearing β-redex case

end LeanFX2.Smoke
