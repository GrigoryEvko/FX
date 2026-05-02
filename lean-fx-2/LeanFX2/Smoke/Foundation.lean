import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.Context

/-! # Smoke/Foundation — RawTerm / Ty / Subst sanity examples.

Concrete examples demonstrating Layer 0 components work as designed.
Each `example` is a small proof obligation that compiles iff the
underlying definitions are correct.

## Examples planned

```lean
-- Identity raw substitution
example : (RawTerm.var i).subst RawTermSubst.identity = RawTerm.var i := rfl

-- Singleton substitution at position 0
example : (RawTerm.var ⟨0, _⟩).subst (RawTermSubst.singleton arg) = arg := rfl

-- Type substitution preserves structure
example : (Ty.arrow A B).subst σ = Ty.arrow (A.subst σ) (B.subst σ) := rfl

-- ... etc
```

## Dependencies

* All Layer 0 (Foundation/*)

## Implementation plan (Layer 14)

1. ~10-20 small `example` proofs covering each Layer 0 op
2. Each compiles iff the underlying op is correct
3. AuditAll-gated zero-axiom
-/

namespace LeanFX2.Smoke

-- TODO: example proofs for Foundation layer

end LeanFX2.Smoke
