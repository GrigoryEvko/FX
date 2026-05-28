import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExact

/-! # Foundation/PolyCell/Core/CertifyRawCellExactCompHRejects — totality off compH

This file ships `certifyRawCellExact?_compH_rejects`: the
totality-off-`horizontalComposite` theorem.  For any
`.horizontalComposite left right` input, the certifier rejects with
`.unsupportedCompH` — at every dimension, scope, and profile.

Direct v2 counterpart to v1's `certifyRawCellExact?_compH_rejects`
(`Core/CertifyExact.lean:201`).

## Why `horizontalComposite` rejects unconditionally

Per `polycell.md` §4's rejection taxonomy:

> | raw `compH` before Axis 6 certification | reject `unsupportedCompH` |

Horizontal composition (the Gray-tensor cellular pairing) requires
Gray boundary semantics tracked as M-horizComposite-admission
#384 + Axis 6 of the `polycell.md` roadmap (the "infinite
scaling" extension calculus work).  Until those semantics are mechanized, the certifier has no
admissible PolyCell constructor for compH, and any raw input
containing a `.horizontalComposite` at the OUTER ctor is structurally
unsupportable.

The certifier matches this in its dispatch:

```
| .horizontalComposite _ _ => .error .unsupportedCompH
```

Closing the totality story: every well-formed input either
certifies cleanly OR rejects with one of the seven rejection
classes.  This theorem proves that `horizontalComposite` at the
TOP ctor always lands in the `.unsupportedCompH` rejection class.

## Why `rfl`

The top-level `certifyRawCellExact? scope raw` unfolds to
`certifyRawCellExactFueled? (raw.size + 1) scope raw`.  For
`raw := .horizontalComposite left right`:

* `raw.size = left.size + right.size + 1` (by RawCell.size's
  `.horizontalComposite` arm)
* `raw.size + 1 = left.size + right.size + 2`, definitionally
  `Nat.succ (left.size + right.size + 1)` — matches the fuel
  function's `fuel' + 1` arm.
* Inside the succ arm, the inner `match raw with` hits the
  `.horizontalComposite _ _ => .error .unsupportedCompH` arm.

All reductions are definitional; `rfl` closes the chain.

## Zero-axiom verification

Proof is `rfl`.  Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- The recursive certifier rejects horizontal composition at every
dimension, pending Gray-tensor semantics (Axis 6).

For any `(left right : RawCell scope)`, calling the certifier on
`.horizontalComposite left right` returns
`Except.error .unsupportedCompH` — regardless of the operands'
internal structure, dimension, or sort.

Closes by `rfl` because the certifier's `.horizontalComposite _ _`
match arm produces `.error .unsupportedCompH` directly, and the
top-level wrapper's fuel allocation `raw.size + 1` is always
positive for a `.horizontalComposite` (it equals `left.size +
right.size + 2 ≥ 2`), so the fuel guard never triggers
`.fuelExhausted`. -/
theorem certifyRawCellExact?_compH_rejects {profile : PolyProfile}
    {scope : Nat} (left right : RawCell scope) :
    certifyRawCellExact? (profile := profile) scope
      (.horizontalComposite left right) =
      Except.error .unsupportedCompH :=
  rfl

end LeanFX2.Foundation.PolyCell.Core
