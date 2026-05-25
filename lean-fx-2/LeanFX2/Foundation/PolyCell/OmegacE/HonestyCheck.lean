import LeanFX2.Foundation.PolyCell.OmegacE.Word
/-!
# Honesty Check HC.5: ωcE cell count verification

Verify the current OmegacECell generator scaffold:
- dim 0: 2 cells (sourceVertex, targetVertex)
- dim 1: 2 cells (quasiIso, quasiInverse)
- dim 2: 2 cells (alphaUnit, betaCounit)
- dim k+3: 2 cells (higherCoherence _ 0, higherCoherence _ 1)
- countAtDim = 2 for all dimensions
- atDeclaredIndex selects through the declared per-dimension count
- suspend maps a scaffold generator to the same declared slot one dimension up
- declaredIndexOf reads generators back into the declared index type
- slotValueOf and declaredIndexValueOf expose proof-free Nat indices
- slotKindOf/isFirstSlot/isSecondSlot classify the two declared slots
- OmegacEWord packages finite scaffold-generator lists and preserves length
  and slot readback under suspension
- OmegacEWordCode serializes scaffold words as normalized Nat slot lists;
  this is still not Makkai word equality
- totalUpTo 0 = 2, totalUpTo 1 = 4, totalUpTo 2 = 6

This is a scaffold check, not a proof of the full HLOR construction.
-/

namespace LeanFX2.Foundation.PolyCell.OmegacE

-- Verify countAtDim is 2 for dimensions 0, 1, 2, 3, 4
example : OmegacECell.countAtDim 0 = 2 := rfl
example : OmegacECell.countAtDim 1 = 2 := rfl
example : OmegacECell.countAtDim 2 = 2 := rfl
example : OmegacECell.countAtDim 3 = 2 := rfl
example : OmegacECell.countAtDim 4 = 2 := rfl
example : OmegacECell.countAtDim 100 = 2 := rfl

-- Verify the explicit two-generator enumeration
example : OmegacECell.firstAtDim 0 = OmegacECell.sourceVertex := rfl
example : OmegacECell.secondAtDim 0 = OmegacECell.targetVertex := rfl
example : OmegacECell.firstAtDim 1 = OmegacECell.quasiIso := rfl
example : OmegacECell.secondAtDim 1 = OmegacECell.quasiInverse := rfl
example : OmegacECell.firstAtDim 2 = OmegacECell.alphaUnit := rfl
example : OmegacECell.secondAtDim 2 = OmegacECell.betaCounit := rfl
example : OmegacECell.firstAtDim 3 =
    OmegacECell.higherCoherence 0 ⟨0, by decide⟩ := rfl
example : OmegacECell.secondAtDim 3 =
    OmegacECell.higherCoherence 0 ⟨1, by decide⟩ := rfl
example : OmegacECell.atSlot 3 ⟨0, by decide⟩ =
    OmegacECell.firstAtDim 3 := rfl
example : OmegacECell.atSlot 3 ⟨1, by decide⟩ =
    OmegacECell.secondAtDim 3 := rfl
example : OmegacECell.atDeclaredIndex 3 OmegacECell.slotZero =
    OmegacECell.firstAtDim 3 := rfl
example : OmegacECell.atDeclaredIndex 3 OmegacECell.slotOne =
    OmegacECell.secondAtDim 3 := rfl
example : OmegacECell.suspend OmegacECell.sourceVertex =
    OmegacECell.quasiIso := rfl
example : OmegacECell.suspend OmegacECell.targetVertex =
    OmegacECell.quasiInverse := rfl
example : OmegacECell.suspend OmegacECell.quasiIso =
    OmegacECell.alphaUnit := rfl
example : OmegacECell.suspend OmegacECell.quasiInverse =
    OmegacECell.betaCounit := rfl
example : OmegacECell.suspend OmegacECell.alphaUnit =
    OmegacECell.higherCoherence 0 OmegacECell.slotZero := rfl
example : OmegacECell.suspend OmegacECell.betaCounit =
    OmegacECell.higherCoherence 0 OmegacECell.slotOne := rfl
example : OmegacECell.suspend
      (OmegacECell.higherCoherence 0 OmegacECell.slotZero) =
    OmegacECell.higherCoherence 1 OmegacECell.slotZero := rfl
example : OmegacECell.suspendAtDeclaredIndex 3 OmegacECell.slotZero =
    OmegacECell.firstAtDim 4 := rfl
example : OmegacECell.suspendAtDeclaredIndex 3 OmegacECell.slotOne =
    OmegacECell.secondAtDim 4 := rfl
example : OmegacECell.slotValueOf
      (OmegacECell.suspend (OmegacECell.firstAtDim 3)) =
    OmegacECell.slotValueOf (OmegacECell.firstAtDim 3) := by
  exact OmegacECell.slotValueOf_suspend (OmegacECell.firstAtDim 3)
example : OmegacECell.declaredIndexValueOf
      (OmegacECell.suspend (OmegacECell.secondAtDim 3)) =
    OmegacECell.declaredIndexValueOf (OmegacECell.secondAtDim 3) := by
  exact OmegacECell.declaredIndexValueOf_suspend
    (OmegacECell.secondAtDim 3)
example : OmegacECell.declaredIndexOf (OmegacECell.firstAtDim 3) =
    OmegacECell.slotZero := rfl
example : OmegacECell.declaredIndexOf (OmegacECell.secondAtDim 3) =
    OmegacECell.slotOne := rfl
example : OmegacECell.declaredIndexOf
      (OmegacECell.atDeclaredIndex 3 OmegacECell.slotZero) =
    OmegacECell.slotZero := rfl
example : OmegacECell.declaredIndexOf
      (OmegacECell.atDeclaredIndex 3 OmegacECell.slotOne) =
    OmegacECell.slotOne := rfl
example : OmegacECell.slotValueOf (OmegacECell.firstAtDim 3) = 0 := rfl
example : OmegacECell.slotValueOf (OmegacECell.secondAtDim 3) = 1 := rfl
example : OmegacECell.declaredIndexValueOf
      (OmegacECell.atDeclaredIndex 3 OmegacECell.slotZero) = 0 := rfl
example : OmegacECell.declaredIndexValueOf
      (OmegacECell.atDeclaredIndex 3 OmegacECell.slotOne) = 1 := rfl
example : OmegacECell.slotKindOf (OmegacECell.firstAtDim 3) =
    OmegacECell.SlotKind.first := rfl
example : OmegacECell.slotKindOf (OmegacECell.secondAtDim 3) =
    OmegacECell.SlotKind.second := rfl
example : OmegacECell.slotKindOf
      (OmegacECell.atDeclaredIndex 3 OmegacECell.slotZero) =
    OmegacECell.SlotKind.first := rfl
example : OmegacECell.slotKindOf
      (OmegacECell.atDeclaredIndex 3 OmegacECell.slotOne) =
    OmegacECell.SlotKind.second := rfl
example : OmegacECell.isFirstSlot (OmegacECell.firstAtDim 3) = true := rfl
example : OmegacECell.isFirstSlot (OmegacECell.secondAtDim 3) = false := rfl
example : OmegacECell.isSecondSlot (OmegacECell.firstAtDim 3) = false := rfl
example : OmegacECell.isSecondSlot (OmegacECell.secondAtDim 3) = true := rfl
example : OmegacECell.slotValueOf (OmegacECell.firstAtDim 3) <
    OmegacECell.countAtDim 3 := by
  exact OmegacECell.slotValueOf_lt_countAtDim (OmegacECell.firstAtDim 3)
example : OmegacECell.declaredIndexValueOf (OmegacECell.secondAtDim 3) <
    OmegacECell.countAtDim 3 := by
  exact OmegacECell.declaredIndexValueOf_lt_countAtDim
    (OmegacECell.secondAtDim 3)
example : (OmegacECell.cellsAtDim 3).length =
    OmegacECell.countAtDim 3 := rfl
example : (OmegacEWord.empty 3).length = 0 := rfl
example : (OmegacEWord.singleton (OmegacECell.firstAtDim 3)).length =
    1 := rfl
example :
    (OmegacEWord.append
        (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
        (OmegacEWord.singleton (OmegacECell.secondAtDim 3))).length =
      2 := by
  exact OmegacEWord.length_append
    (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
    (OmegacEWord.singleton (OmegacECell.secondAtDim 3))
example :
    (OmegacEWord.suspend
        (OmegacEWord.append
          (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
          (OmegacEWord.singleton (OmegacECell.secondAtDim 3)))).length =
      2 := by
  exact OmegacEWord.length_suspend
    (OmegacEWord.append
      (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
      (OmegacEWord.singleton (OmegacECell.secondAtDim 3)))
example :
    (OmegacEWord.singleton (OmegacECell.firstAtDim 3)).slotValues =
      [0] := rfl
example :
    (OmegacEWord.suspend
        (OmegacEWord.append
          (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
          (OmegacEWord.singleton (OmegacECell.secondAtDim 3)))).slotValues =
      (OmegacEWord.append
        (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
        (OmegacEWord.singleton (OmegacECell.secondAtDim 3))).slotValues := by
  exact OmegacEWord.slotValues_suspend
    (OmegacEWord.append
      (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
      (OmegacEWord.singleton (OmegacECell.secondAtDim 3)))
example : (OmegacEWordCode.singleton 7).normalize.slotValues = [1] := rfl
example :
    (OmegacEWordCode.append
        (OmegacEWordCode.singleton 0)
        (OmegacEWordCode.singleton 7)).normalize.slotValues =
      [0, 1] := rfl
example :
    ((OmegacEWordCode.append
        (OmegacEWordCode.singleton 0)
        (OmegacEWordCode.singleton 1)).toWord 3).slotValues =
      [0, 1] := rfl
example :
    ((OmegacEWordCode.append
        (OmegacEWordCode.singleton 0)
        (OmegacEWordCode.singleton 7)).toWord 3).slotValues =
      [0, 1] := rfl
example :
    OmegacEWordCode.ofWord
        ((OmegacEWordCode.append
          (OmegacEWordCode.singleton 0)
          (OmegacEWordCode.singleton 7)).toWord 3) =
      (OmegacEWordCode.append
        (OmegacEWordCode.singleton 0)
        (OmegacEWordCode.singleton 7)).normalize := by
  exact OmegacEWordCode.ofWord_toWord 3
    (OmegacEWordCode.append
      (OmegacEWordCode.singleton 0)
      (OmegacEWordCode.singleton 7))
example :
    OmegacEWordCode.ofWord
        (OmegacEWord.suspend
          (OmegacEWord.append
            (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
            (OmegacEWord.singleton (OmegacECell.secondAtDim 3)))) =
      OmegacEWordCode.ofWord
        (OmegacEWord.append
          (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
          (OmegacEWord.singleton (OmegacECell.secondAtDim 3))) := by
  exact OmegacEWordCode.ofWord_suspend
    (OmegacEWord.append
      (OmegacEWord.singleton (OmegacECell.firstAtDim 3))
      (OmegacEWord.singleton (OmegacECell.secondAtDim 3)))

-- Verify totalUpTo cumulative counts
example : OmegacECell.totalUpTo 0 = 2 := rfl
example : OmegacECell.totalUpTo 1 = 4 := rfl
example : OmegacECell.totalUpTo 2 = 6 := rfl
example : OmegacECell.totalUpTo 3 = 8 := rfl

-- Verify concrete cell construction at each dimension
example : (OmegacECell.sourceVertex).dimension = 0 := rfl
example : (OmegacECell.targetVertex).dimension = 0 := rfl
example : (OmegacECell.quasiIso).dimension = 1 := rfl
example : (OmegacECell.quasiInverse).dimension = 1 := rfl
example : (OmegacECell.alphaUnit).dimension = 2 := rfl
example : (OmegacECell.betaCounit).dimension = 2 := rfl
example : (OmegacECell.higherCoherence 0 0).dimension = 3 := rfl
example : (OmegacECell.higherCoherence 0 1).dimension = 3 := rfl
example : (OmegacECell.higherCoherence 1 0).dimension = 4 := rfl

-- Verify DecidableEq works (cells are computationally comparable)
example : (OmegacECell.sourceVertex == OmegacECell.targetVertex) = false := rfl
example : (OmegacECell.quasiIso == OmegacECell.quasiIso) = true := rfl
example : (OmegacECell.alphaUnit == OmegacECell.betaCounit) = false := rfl

-- HONESTY ASSESSMENT: Our encoding gives 2 cells per dimension uniformly.
-- HLOR Construction 1.22 actually has a more complex pushout structure
-- where the cell count grows. Our simplified encoding captures the
-- GENERATOR count (2 per dim) but not the full free-category cells
-- generated by composition. This is correct for the POLYGRAPH
-- (generators only) — the free category F(ωcE) has infinitely many
-- cells per dim from composition, but the generating polygraph has 2.

end LeanFX2.Foundation.PolyCell.OmegacE
