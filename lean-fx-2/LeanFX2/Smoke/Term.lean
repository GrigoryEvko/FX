import LeanFX2.Term
import LeanFX2.Term.Subst

/-! # Smoke/Term — concrete typed Term examples.

```lean
-- Identity function: λx. x
example : Term Ctx.empty (Ty.arrow Ty.unit Ty.unit) (RawTerm.lam (RawTerm.var ⟨0, _⟩))
  := Term.lam (Term.var ⟨0, _⟩)

-- Application: (λx. x) ()
example : Term Ctx.empty Ty.unit (RawTerm.app (RawTerm.lam (RawTerm.var ⟨0, _⟩)) RawTerm.unit)
  := Term.app (Term.lam (Term.var ⟨0, _⟩)) Term.unit

-- toRaw is rfl
example (t : Term ctx ty raw) : t.toRaw = raw := rfl
```

## Dependencies

* `Term.lean`, `Term/Subst.lean`

## Implementation plan (Layer 14)

1. Identity function, identity application, β-redex
2. Each Term ctor exemplified
3. toRaw projection demonstrated as rfl
4. subst0 reduction demonstrated
-/

namespace LeanFX2.Smoke

-- TODO: example typed terms

end LeanFX2.Smoke
