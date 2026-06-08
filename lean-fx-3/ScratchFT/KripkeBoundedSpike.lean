import FX1Poly.Core.KripkeCandidateRenameClosure

/-! # ScratchFT/KripkeBoundedSpike — KB-01 GO/NO-GO probe (NEVER committed)

Question: can the fuel/bound become a SECOND presheaf index on KripkeCand so that fuel-monotonicity
of the dependent arrow is `Iff.rfl`, exactly as renaming-transport is?  The renaming axis is `Iff.rfl`
because `RawRenaming = Fin → Fin` composes DEFINITIONALLY-associatively.  This file tests whether a
`Nat`-offset bound axis threads the same way.

PROBE A: transport functoriality over the bound axis — is it `rfl`, or does it need `Nat.add_assoc`?
PROBE B: the dependent-arrow transport over the bound axis — `Iff.rfl` or not?
PROBE C: does Lean accept the merged candidate's shape at all (well-formedness)?
-/

namespace FX1Poly.Core.Spike
open FX1Poly.Foundation

/-- Merged candidate: renaming index AND a `Nat` bound-offset index. -/
def KBCand (sourceScope : Nat) :=
  ∀ {targetScope : Nat}, RawRenaming sourceScope targetScope → Nat → RawTerm targetScope → Prop

/-- Transport over BOTH axes: precompose renaming, ADD the bound offset. -/
def KBCand.transport {sourceScope renamedScope : Nat}
    (forwardRenaming : RawRenaming sourceScope renamedScope) (boundOffset : Nat)
    (candidate : KBCand sourceScope) : KBCand renamedScope :=
  fun {_targetScope} indexRenaming indexBound term =>
    candidate (RawRenaming.compose forwardRenaming indexRenaming) (boundOffset + indexBound) term

-- PROBE A1 RESULT: `Iff.rfl` FAILS here (confirmed). The renaming index threads by definitional
-- function-composition associativity, but the bound index needs `firstBound + (secondBound + indexBound)
-- = (firstBound + secondBound) + indexBound`, which is `Nat.add_assoc` — a THEOREM, not `rfl`.

/-- PROBE A2: same functoriality, proved via `Nat.add_assoc` (the honest, zero-axiom form). -/
theorem KBCand.transport_transport {sourceScope middleScope renamedScope : Nat}
    (firstRenaming : RawRenaming sourceScope middleScope) (firstBound : Nat)
    (secondRenaming : RawRenaming middleScope renamedScope) (secondBound : Nat)
    (candidate : KBCand sourceScope)
    {targetScope : Nat} (indexRenaming : RawRenaming renamedScope targetScope) (indexBound : Nat)
    (term : RawTerm targetScope) :
    KBCand.transport secondRenaming secondBound (KBCand.transport firstRenaming firstBound candidate)
        indexRenaming indexBound term ↔
      KBCand.transport (RawRenaming.compose firstRenaming secondRenaming) (firstBound + secondBound)
        candidate indexRenaming indexBound term := by
  unfold KBCand.transport
  rw [Nat.add_assoc]

end FX1Poly.Core.Spike
