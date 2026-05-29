/-! # FX1Poly.Foundation.RawSubst.RenameDefs — positional renaming substrate

Native-infra clean cut from lean-fx-2's
`LeanFX2.Foundation.RawSubst.RenameDefs`.

## What this file carries (and what it deliberately drops)

lean-fx-2's `RawSubst/RenameDefs` mixed two unrelated things:

1. **`RawRenaming`** — the purely positional renaming type
   `Fin source → Fin target` plus `identity` / `lift` / `weaken` /
   `compose`.  This is what the PolyCell cell calculus actually consumes
   (the `Fold` engine's variable case applies a `RawRenaming` to a `Fin`
   position and re-wraps as a `gen_var` cell).  It carries NO dependency
   on any raw-term type — it is first-order data over `Fin`.

2. `RawTerm.rename` / `RawTerm.weaken` over the **legacy MLTT `RawTerm`**
   (`.var` / `.lam` / `.app` / …).  Those operated on lean-fx-2's
   intrinsic-MLTT raw term and are NOT used by the PolyCell substrate —
   PolyCell's own `RawTerm` (`FX1Poly.Core.RawTerm`, a `.mkGen`-cell
   term) defines its rename via `FX1Poly.Core.Fold`, not here.

The clean cut keeps (1) and SEVERS (2): the legacy MLTT raw term is NOT
a dependency of FX1Poly.  This file therefore has zero imports.

## Root status

Layer 0 raw-syntax definitions.  Strict zero-axiom. -/

namespace FX1Poly.Foundation

/-! ## Renamings -/

/-- A raw rawRenaming: `Fin source → Fin target`. -/
@[reducible] def RawRenaming (source target : Nat) : Type := Fin source → Fin target

/-- Identity rawRenaming. -/
@[reducible] def RawRenaming.identity {scope : Nat} : RawRenaming scope scope :=
  fun position => position

/-- Lift rawRenaming under a binder: position 0 stays, others shift. -/
@[reducible] def RawRenaming.lift {source target : Nat}
    (rawRenaming : RawRenaming source target) : RawRenaming (source + 1) (target + 1)
  | ⟨0, _⟩      => ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => Fin.succ (rawRenaming ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- Weakening rawRenaming: shift all positions by 1. -/
@[reducible] def RawRenaming.weaken {scope : Nat} : RawRenaming scope (scope + 1) :=
  fun position => Fin.succ position

/-- Compose two rawRenamings. -/
@[reducible] def RawRenaming.compose {scopeA scopeB scopeC : Nat}
    (firstRenaming : RawRenaming scopeA scopeB)
    (secondRenaming : RawRenaming scopeB scopeC) :
    RawRenaming scopeA scopeC :=
  fun position => secondRenaming (firstRenaming position)

end FX1Poly.Foundation
