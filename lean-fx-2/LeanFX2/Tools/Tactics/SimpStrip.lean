/-! # Tools/Tactics/SimpStrip — bridge-rfl simp set

A curated `simp` lemma set that strips `Term.toRaw`-related casts
from goals.  Useful when proving Bridge theorems where multiple
`toRaw_<op>` rfls compose.

## The simp set

```lean
attribute [simp_strip] Term.toRaw_cast
attribute [simp_strip] Term.toRaw_rename     -- rfl
attribute [simp_strip] Term.toRaw_subst      -- rfl
attribute [simp_strip] Term.toRaw_subst0     -- rfl
attribute [simp_strip] Term.toRaw_var
attribute [simp_strip] Term.toRaw_lam
-- ... (all toRaw projections)
```

## Usage

```lean
example : (Term.lam body).toRaw.subst σ.forRaw = ... := by
  simp only [simp_strip]
  ...
```

## Why a separate simp set

`simp` with arbitrary lemmas can rewrite too aggressively, breaking
proofs.  A scoped set (`simp_strip`) only fires the rfl-collapsing
lemmas, keeping intent explicit.

## Dependencies

* `Term/ToRaw.lean`

## Downstream

* `Bridge.lean` — uses simp_strip to discharge rfl-equal raw forms
* `Reduction/Compat.lean`

## Implementation plan (Layer 12)

1. Define `simp_strip` attribute
2. Tag all toRaw_<op> lemmas
3. Smoke: trivial bridge proof closes via `simp only [simp_strip]`

Target: ~100 lines.
-/

namespace LeanFX2.Tools.Tactics

-- TODO Layer 12: simp_strip attribute + tagged lemmas

end LeanFX2.Tools.Tactics
