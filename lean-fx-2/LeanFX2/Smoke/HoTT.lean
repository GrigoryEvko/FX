import LeanFX2.HoTT.Identity
import LeanFX2.HoTT.J
import LeanFX2.HoTT.Transport

/-! # Smoke/HoTT — Identity types, J, transport, HIT examples.

```lean
-- J on refl reduces to base
example (baseCase : Term ctx P (RawTerm.var ⟨0, _⟩)) :
    Step (Term.idJ baseCase (Term.refl ...)) baseCase :=
  Step.iotaIdJRefl baseCase

-- Transport along refl is identity
example (P : ...) (a : ...) (witness : ...) :
    transport P (refl a) witness = witness := by simp ...
```

## Dependencies

* `HoTT/Identity.lean`, `HoTT/J.lean`, `HoTT/Transport.lean`

## Implementation plan (Layer 14)

1. J on refl
2. transport along refl
3. Path composition + groupoid laws
4. S¹ via setoid encoding (small example)
-/

namespace LeanFX2.Smoke

-- TODO: HoTT smoke examples

end LeanFX2.Smoke
