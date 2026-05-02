import LeanFX2.Modal.Foundation

/-! # Modal/Cap — Capability modality

Capability-label data + lattice + intro/elim/subsumption.  Used by
fx_design.md's capability tracking (e.g., file system, network,
syscall capabilities).

## Modality

```lean
def Modality.cap (label : CapabilityLabel) : Modality
```

## Lattice

Capabilities form a lattice (e.g., `read ⊏ readWrite`,
`localFile ⊏ anyFile`).  The lattice is structure-respected by
TwoCells (`Modal/TwoCell` — already in `Foundation/Mode.lean`).

## Subsumption

```lean
theorem Cap.subsume_lower :
    capLow ≤ capHigh →
    Term ctx (Ty.modal (Modality.cap capLow) ty) raw →
    Term ctx (Ty.modal (Modality.cap capHigh) ty) raw'
```

Always-allowed: weaken-cap subsumption.

## Smoke

Filesystem capability example: a function with `Cap(filesystem.read)`
cannot perform `Cap(filesystem.write)` operations.

## Dependencies

* `Modal/Foundation.lean`

## Downstream consumers

* User-level capability-aware code
-/

namespace LeanFX2

end LeanFX2
