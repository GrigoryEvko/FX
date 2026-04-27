import FX.Kernel.Grade.Representation

/-!
# Representation dimension tests

Covers `fx_design.md` §6.3 dim 10 and §8.5.

`Representation.LessEq` is a `Prop`-valued inductive without a
`decLe` instance (unlike Usage / Trust etc.), so `LessEq` tests
construct the proof directly via `LessEq.refl` / `LessEq.nativeLe` /
`LessEq.leNoSpec`.
-/

namespace Tests.Kernel.Grade.Representation

open FX.Kernel
open FX.Kernel.Representation

/-! ## Add truth table — 25 cells -/

example : add native    native    = some native    := by decide
example : add native    cCompat         = some cCompat         := by decide
example : add native    packed    = some packed    := by decide
example : add native    bigEndian = some bigEndian := by decide
example : add native    noSpec    = some noSpec    := by decide

example : add cCompat         native    = some cCompat         := by decide
example : add cCompat         cCompat         = some cCompat         := by decide
example : add cCompat         packed    = none           := by decide
example : add cCompat         bigEndian = some cCompat         := by decide
example : add cCompat         noSpec    = some noSpec    := by decide

example : add packed    native    = some packed    := by decide
example : add packed    cCompat         = none           := by decide
example : add packed    packed    = some packed    := by decide
example : add packed    bigEndian = some packed    := by decide
example : add packed    noSpec    = some noSpec    := by decide

example : add bigEndian native    = some bigEndian := by decide
example : add bigEndian cCompat         = some cCompat         := by decide
example : add bigEndian packed    = some packed    := by decide
example : add bigEndian bigEndian = some bigEndian := by decide
example : add bigEndian noSpec    = some noSpec    := by decide

example : add noSpec    native    = some noSpec    := by decide
example : add noSpec    cCompat         = some noSpec    := by decide
example : add noSpec    packed    = some noSpec    := by decide
example : add noSpec    bigEndian = some noSpec    := by decide
example : add noSpec    noSpec    = some noSpec    := by decide

/-! ## Commutativity -/

example : ∀ x y : Representation, add x y = add y x := by
  intro x y; cases x <;> cases y <;> rfl

/-! ## LessEq — bottom, top, reflexive

`Representation.LessEq` is `Prop`, not `Bool` — no `decLe`, so we
construct proofs via constructors. -/

example : LessEq native native       := LessEq.refl _
example : LessEq native cCompat            := LessEq.nativeLe _
example : LessEq native packed       := LessEq.nativeLe _
example : LessEq native bigEndian    := LessEq.nativeLe _
example : LessEq native noSpec       := LessEq.nativeLe _

example : LessEq cCompat noSpec            := LessEq.leNoSpec _
example : LessEq packed noSpec       := LessEq.leNoSpec _
example : LessEq bigEndian noSpec    := LessEq.leNoSpec _

example : ∀ x : Representation, LessEq x x := LessEq.refl
example : ∀ x : Representation, LessEq native x := LessEq.nativeLe
example : ∀ x : Representation, LessEq x noSpec := LessEq.leNoSpec

example : ∀ x y z : Representation,
    LessEq x y → LessEq y z → LessEq x z := fun _ _ _ => LessEq.trans

end Tests.Kernel.Grade.Representation
