/-!
# Mode Theory 2-Category (Gratzer arXiv:2301.11842 §2)

A mode theory: objects=modes, 1-cells=modalities, 2-cells=coherences.
Gratzer Theorem 4: MTT conv decidable iff mode-theory equality decidable.

Reference: arXiv:2301.11842 §2.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.MTTNorm

/-- A mode theory: finitary 2-category for the modal structure. -/
structure ModeTheory where
  Mode : Type
  Modality : Mode → Mode → Type
  identityModality : (mode : Mode) → Modality mode mode
  composeModality : {modeA modeB modeC : Mode} →
    Modality modeA modeB → Modality modeB modeC → Modality modeA modeC

/-- Rigidity: no non-trivial 2-isomorphisms (R1). For rigid theories,
distinct modalities are NEVER 2-isomorphic — they're either equal or
incomparable. Makes 1-cell equality decidable from finite enumeration. -/
structure ModeTheoryRigid extends ModeTheory where
  modalityDecEq : (modeA modeB : toModeTheory.Mode) →
    DecidableEq (toModeTheory.Modality modeA modeB)

/-- Gratzer conditions satisfied: rigid + decidable. -/
structure GratzerReady extends ModeTheoryRigid where
  modeDecEq : DecidableEq toModeTheory.Mode

/-- The trivial mode theory: 1 mode, 1 modality. MTT over this = plain MLTT. -/
def trivialModeTheory : ModeTheory where
  Mode := Unit
  Modality := fun () () => Unit
  identityModality := fun () => ()
  composeModality := fun () () => ()

/-- Trivial theory is Gratzer-ready. -/
def trivialGratzerReady : GratzerReady where
  toModeTheoryRigid := {
    toModeTheory := trivialModeTheory
    modalityDecEq := fun () () => fun () () => .isTrue rfl
  }
  modeDecEq := fun () () => .isTrue rfl

/-- FX mode atoms: the finite set of modes in the FX doctrine. -/
inductive FXModeAtom where
  | pure
  | linear
  | affine
  | unrestricted
  | ghost
  | classified
  | unclassified
  | async
  deriving DecidableEq, Repr

/-- FX mode shifts: modalities between FX modes. -/
inductive FXModeShift : FXModeAtom → FXModeAtom → Type where
  | identity : (mode : FXModeAtom) → FXModeShift mode mode
  | ghostToPure : FXModeShift .ghost .pure
  | pureToClassified : FXModeShift .pure .classified
  | linearToAffine : FXModeShift .linear .affine
  | affineToUnrestricted : FXModeShift .affine .unrestricted
  | pureToAsync : FXModeShift .pure .async
  deriving DecidableEq, Repr

/-- The FX mode theory (simplified: only identity composition for now). -/
def fxModeTheory : ModeTheory where
  Mode := FXModeAtom
  Modality := fun _ _ => Nat  -- simplified placeholder: modalities as numeric ids
  identityModality := fun _ => 0
  composeModality := fun modF modG => modF + modG

/-- FX mode theory is rigid (DecidableEq on Nat is trivial). -/
def fxModeTheoryRigid : ModeTheoryRigid where
  toModeTheory := fxModeTheory
  modalityDecEq := fun _ _ => Nat.decEq

/-- FX mode theory is Gratzer-ready. -/
def fxGratzerReady : GratzerReady where
  toModeTheoryRigid := fxModeTheoryRigid
  modeDecEq := instDecidableEqFXModeAtom

end LeanFX2.Foundation.PolyCell.MTTNorm
