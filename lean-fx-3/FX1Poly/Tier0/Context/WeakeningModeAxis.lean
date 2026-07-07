import FX1Poly.Tier0.Context.ModalLock

/-! # FX1Poly/Tier0/Context/WeakeningModeAxis — fib-3 #3: the first NON-trivial `ContextAxis.lockOn`
instantiation (the weakening lock threaded into the slot)

`ContextAxis.lockOn` (`Context.lean`) is the abstract lock slot: each modality acts on the substitution category
by an endofunctor.  Until now the ONLY inhabited axis is `fxContextAxis` at `trivialMode` (one mode, only the
identity modality), whose `lockOn` deposits `RawEndofunctor.identity` at every modality — the slot has never
carried a genuinely non-identity lock (`fxContextAxis_lockOn_eq_identityLock`).

This file ships the FIRST non-trivial instantiation, ADDITIVELY (it touches neither `Context.lean` nor
`ModalLock.lean` — `fxContextAxis` stays exactly as-is).  `weakeningModeData` is a one-mode theory whose
modalities are the WEAKENING amounts (`weaken-by-K`, `Modality := Nat`, identity = `weaken-by-0`), and
`fxWeakeningContextAxis` is a `ContextAxis` over it whose `lockOn` deposits the shipped `fxWeakeningLock K`
(`A ↦ A + K`, context extension by `K` fresh variables) at modality `K`.  The wiring theorems
(`fxWeakeningContextAxis_lockOn_eq_weakeningLock`, the analogue of `fxContextAxis_lockOn_eq_identityLock`) certify
the slot now carries a real, non-identity endofunctor.

## HONESTY — carrier only, DRA WALLED

This threads the lock CARRIER (a `RawEndofunctor`) into the `lockOn` slot, whose codomain is exactly
`RawEndofunctor substMode`, so no adjunction is needed for the instantiation to type-check.  It delivers NO new
dependent right adjoint: `(− + K)` has no endo-right-adjoint in the bare context category — its DRA is the
type-level `∀`-over-`K` living over the `Core/` type fibration (`fib-1`'s fibred-Π right adjoint promoted to an
endo-adjunction), a genuine adjoint-existence wall (`ModalLock` RAPL note).  So `fxWeakeningLock` is threaded as a
carrier, NOT bundled into a `ContextLock`.  The DRA upgrade, Gratzer's dimension-2 decidable-2-cell keystone
(`fxMode_hasDecidableTwoCellEquality` / `fxMode_hasModeRelativeConvDecision`), and the transpension presheaf
adjunction all remain honestly walled.

## Zero-axiom

A `ContextModeData` (`Unit` modes, `Nat` modalities), a `ContextAxis` reusing the shipped renaming/substitution
categories and global sections, and `rfl`-closed wiring / non-triviality theorems.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Tier0

/-- The **weakening mode theory**: ONE mode, whose modalities are the WEAKENING amounts — `Modality := Nat`, a
modality `K` is "weaken by `K` fresh variables", and the identity modality is `weaken-by-0`.  The minimal
`ContextModeData` carrying a genuinely non-identity modality (any `K > 0`), so its `lockOn` can deposit a
non-identity lock. -/
def weakeningModeData : ContextModeData where
  Mode := Unit
  Modality := fun _ _ => Nat
  idModality := fun _ => 0

/-- ★ **The first NON-trivial context axis.**  A `ContextAxis` over `weakeningModeData` reusing the shipped
renaming/substitution categories and global sections, whose `lockOn` deposits the weakening lock
`fxWeakeningLock K` (`A ↦ A + K`) at modality `K` — the first inhabitant of the abstract lock slot carrying a
non-identity endofunctor.  Additive: `fxContextAxis` (the trivial-mode axis) is untouched. -/
def fxWeakeningContextAxis : ContextAxis weakeningModeData where
  renamingMode := fxBaseRenamingVecRMC
  substMode := fxBaseSubstCategory
  renamingGlobalSections := fxBaseRenamingVecGlobalSections
  substGlobalSections := fxBaseSubstGlobalSections
  lockOn := fun {_ _} extraScope => fxWeakeningLock extraScope
  fireTriangleLeg := none

/-- The substitution-mode of the weakening axis is the shipped CwF base category (reused, not rebuilt). -/
theorem fxWeakeningContextAxis_substMode :
    fxWeakeningContextAxis.substMode = fxBaseSubstCategory := rfl

/-- The weakening axis restricts no Fire-Triangle leg (like the substrate). -/
theorem fxWeakeningContextAxis_fireTriangleLeg :
    fxWeakeningContextAxis.fireTriangleLeg = none := rfl

/-- ★ **The wiring theorem** (the analogue of `fxContextAxis_lockOn_eq_identityLock`).  The lock the weakening
axis deposits at modality `extraScope` IS the shipped `fxWeakeningLock extraScope` — the abstract lock slot
`lockOn` now carries a real weakening endofunctor `A ↦ A + extraScope`. -/
theorem fxWeakeningContextAxis_lockOn_eq_weakeningLock (extraScope : Nat) :
    (@ContextAxis.lockOn weakeningModeData fxWeakeningContextAxis () () extraScope)
      = fxWeakeningLock extraScope := rfl

/-- At the IDENTITY modality (`weaken-by-0`) the axis deposits `fxWeakeningLock 0` (`A ↦ A + 0`) — the neutral
weakening.  The weakening-axis counterpart of `fxContextAxis`'s trivial identity lock. -/
theorem fxWeakeningContextAxis_lockOn_id_eq_weakeningLockZero :
    (@ContextAxis.lockOn weakeningModeData fxWeakeningContextAxis () ()
        (weakeningModeData.idModality ())) = fxWeakeningLock 0 := rfl

/-- The deposited weakening lock acts on objects by adding the weakening amount: at modality `extraScope`,
`lockOn`'s endofunctor sends scope `scope` to `scope + extraScope`. -/
theorem fxWeakeningContextAxis_lockOn_mapObject (extraScope scope : Nat) :
    ((@ContextAxis.lockOn weakeningModeData fxWeakeningContextAxis () () extraScope).mapObject scope)
      = scope + extraScope := rfl

/-- ★ **Non-triviality witness.**  The lock the weakening axis deposits at modality `1` is GENUINELY
non-identity: it sends scope `0` to `1`, whereas the identity endofunctor fixes `0`.  So `lockOn` carries an
endofunctor that actually moves objects — the first non-identity lock in the slot, in contrast to
`fxContextAxis`'s identity lock. -/
theorem fxWeakeningContextAxis_lockOn_one_isNonTrivial :
    ((@ContextAxis.lockOn weakeningModeData fxWeakeningContextAxis () () (1 : Nat)).mapObject (0 : Nat)
        = (1 : Nat)) ∧
      ((RawEndofunctor.identity fxBaseSubstCategory).mapObject (0 : Nat) = (0 : Nat)) :=
  ⟨rfl, rfl⟩

end FX1Poly.Tier0
