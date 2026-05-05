/-! # Surface/ElabCompleteness — elaboration completeness

Every kernel Term has a surface preimage that elaborates to it:

```lean
theorem Elab.surface_preimage_exists (t : Term ctx ty raw) :
    ∃ (ast : Expr),
        Elab.elabExpr ctx (some ty) ast = .ok ⟨ty, raw, t⟩
```

## Why this matters

Completeness ensures the surface language is **expressive enough** to
denote every typed Term.  If some Term has no surface preimage, we
have a "hidden" kernel construct that can never be written by users.

For lean-fx-2 v0.1, this is straightforward: every Term ctor has a
surface form (var → identifier, app → function call, lam → lambda
expr, etc.).

For advanced features (HoTT J with full motive, modal subsume), the
surface form may be more elaborate (J via type ascription + path
syntax, subsume via implicit modality coercion).

## Dependencies

* `Surface/ElabSoundness.lean`

## Downstream

* User-level guarantee that the surface syntax covers the kernel

## Implementation plan (Layer 10)

1. State theorem
2. Prove by structural induction on Term
3. Each case: produce a canonical surface AST + show elab maps it
   to the original Term
-/

namespace LeanFX2.Surface

-- TODO Layer 10: surface_preimage_exists theorem

end LeanFX2.Surface
