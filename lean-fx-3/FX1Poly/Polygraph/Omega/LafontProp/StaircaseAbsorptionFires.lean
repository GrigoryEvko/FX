import FX1Poly.Polygraph.Omega.LafontProp.StaircaseCompleteness

/-! # Polygraph/Omega/LafontProp/StaircaseAbsorptionFires — concrete fires for the
wire/eta/epsilon absorption ladder (LAFONT-REPAIR stage 2 phase 2, fire file)

Split from `StaircaseCompleteness` so the fire instantiations (which force concrete
canonical-form computations) elaborate against the compiled staircase module.  Contents: one
concrete absorption per closed cell kind consumed through soundness, the kernel-`rfl` matrix
pins, the fan-annihilation and zero-fan fires, and the distinct-matrix negative control.

Raw Lean 4 + Init only; zero-axiom; audit twin with per-decl `#assert_no_axioms` plus an
independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-- The concrete fire matrix (arbitrary nonzero entries, junk-total). -/
def lstFireMatrix : MatrixEntries :=
  fun rowIndex colIndex => rowIndex + 2 * colIndex + 1

/-- FIRE (eta): the deep-eta absorption at pad (1, 0) over a 2x2 rectangle — the fresh zero
column of the 2x2 fire matrix is deleted. -/
theorem lstEtaAbsorptionFire :
    SldAreConvertibleLayers 1
      (sldPadLayer 1 0 [SldCell.generatorEta] :: lstCanonicalLayerList 2 2 lstFireMatrix)
      (lstCanonicalLayerList 1 2
        (composeEntries 2 lstFireMatrix
          (sldLayerEntries (sldPadLayer 1 0 [SldCell.generatorEta])))) :=
  lstEtaCellAbsorbs 1 0 2 lstFireMatrix

/-- FIRE (eta) consumed through soundness: both sides of the fire denote the SAME matrix on
the 2x1 rectangle. -/
theorem lstEtaAbsorptionFireDenotesEqually :
    doEntriesAgreeUpTo 2 1
      (sldLayersDenote
        (sldPadLayer 1 0 [SldCell.generatorEta] :: lstCanonicalLayerList 2 2 lstFireMatrix))
      (sldLayersDenote
        (lstCanonicalLayerList 1 2
          (composeEntries 2 lstFireMatrix
            (sldLayerEntries (sldPadLayer 1 0 [SldCell.generatorEta]))))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo lstEtaAbsorptionFire 2

/-- FIRE (eta) matrix pin, kernel `rfl`: deleting the fresh column recovers the fire matrix
prefix — the absorbed product agrees with the plain matrix on the surviving rectangle. -/
theorem lstEtaAbsorptionMatrixPin :
    doEntriesAgreeUpTo 2 1
      (composeEntries 2 lstFireMatrix
        (sldLayerEntries (sldPadLayer 1 0 [SldCell.generatorEta])))
      lstFireMatrix = true := rfl

/-- FIRE (epsilon): the deep-discard absorption at pad (0, 1) — a zero column is inserted
BEFORE the surviving column of the 1x1 fire matrix. -/
theorem lstEpsilonAbsorptionFire :
    SldAreConvertibleLayers 2
      (sldPadLayer 0 1 [SldCell.generatorEpsilon] :: lstCanonicalLayerList 1 1 lstFireMatrix)
      (lstCanonicalLayerList 2 1
        (composeEntries 1 lstFireMatrix
          (sldLayerEntries (sldPadLayer 0 1 [SldCell.generatorEpsilon])))) :=
  lstEpsilonCellAbsorbs 0 1 1 lstFireMatrix

/-- FIRE (epsilon) matrix pin, kernel `rfl`: the inserted column IS zero and the survivor
carries the original entry — `[1] * (eps | wire) = [0, 1]`. -/
theorem lstEpsilonAbsorptionMatrixPin :
    (Nat.beq
        (composeEntries 1 lstFireMatrix
          (sldLayerEntries (sldPadLayer 0 1 [SldCell.generatorEpsilon])) 0 0) 0
      && Nat.beq
          (composeEntries 1 lstFireMatrix
            (sldLayerEntries (sldPadLayer 0 1 [SldCell.generatorEpsilon])) 0 1)
          (lstFireMatrix 0 0)) = true := rfl

/-- FIRE (wire): the all-wire padded layer at pad (1, 1) deletes over a 2x3 canonical form. -/
theorem lstWireAbsorptionFire :
    SldAreConvertibleLayers 3
      (sldPadLayer 1 1 [SldCell.wire] :: lstCanonicalLayerList 3 2 lstFireMatrix)
      (lstCanonicalLayerList 3 2
        (composeEntries 3 lstFireMatrix
          (sldLayerEntries (sldPadLayer 1 1 [SldCell.wire])))) :=
  lstWireCellAbsorbs 1 1 2 lstFireMatrix

/-- FIRE (wire) matrix pin, kernel `rfl`: the wire sandwich is the identity — the product is
the fire matrix itself on the full 2x3 rectangle. -/
theorem lstWireAbsorptionMatrixPin :
    doEntriesAgreeUpTo 2 3
      (composeEntries 3 lstFireMatrix (sldLayerEntries (sldPadLayer 1 1 [SldCell.wire])))
      lstFireMatrix = true := rfl

/-- FIRE (fan annihilation) consumed through soundness: a fresh zero into the 2-fan of the
constant-3 column denotes the identity — `acc_i + 3 * 0 = acc_i` at the matrix level. -/
theorem lstFreshZeroFanFireDenotesIdentity :
    doEntriesAgreeUpTo 2 2
      (sldLayersDenote
        (sldAppendCells (sldWireLayerOfArity 2) [SldCell.generatorEta]
          :: lstFanLayerList 2 (fun _sourceRow => 3)))
      identityEntries = true :=
  sldConvertibleLayersDenoteAgreeUpTo
    (lstFreshZeroAnnihilatesFan 2 (fun _sourceRow => 3)) 2

/-- FIRE (zero-column fan) consumed through soundness: the zero-column 2-fan denotes the same
matrix as the padded discard on the 2x3 rectangle. -/
theorem lstZeroFanFireDenotesPaddedDiscard :
    doEntriesAgreeUpTo 2 3
      (sldLayersDenote (lstFanLayerList 2 (fun _sourceRow => 0)))
      (sldLayersDenote
        [sldAppendCells (sldWireLayerOfArity 2) [SldCell.generatorEpsilon]]) = true :=
  sldConvertibleLayersDenoteAgreeUpTo (lstZeroColumnFanIsDiscard 2) 2

/-- NEGATIVE CONTROL: canonical forms of DISTINCT matrices stay non-convertible — the
absorption machinery did not collapse the semantics. -/
theorem lstDistinctCanonicalFormsStayApart :
    SldAreConvertibleLayers 1
      (lstCanonicalLayerList 1 1 (fun _rowIndex _colIndex => 1))
      (lstCanonicalLayerList 1 1 (fun _rowIndex _colIndex => 2)) -> False :=
  sldNotConvertibleOfDistinctDenotes
    (lstCanonicalLayerList 1 1 (fun _rowIndex _colIndex => 1))
    (lstCanonicalLayerList 1 1 (fun _rowIndex _colIndex => 2)) 1 rfl

#eval decide (doEntriesAgreeUpTo 2 1
  (composeEntries 2 lstFireMatrix (sldLayerEntries (sldPadLayer 1 0 [SldCell.generatorEta])))
  lstFireMatrix = true)
#eval decide (composeEntries 1 lstFireMatrix
  (sldLayerEntries (sldPadLayer 0 1 [SldCell.generatorEpsilon])) 0 0 = 0)
#eval decide (composeEntries 1 lstFireMatrix
  (sldLayerEntries (sldPadLayer 0 1 [SldCell.generatorEpsilon])) 0 1 = 1)
#eval decide (doEntriesAgreeUpTo 1 1
  (sldLayersDenote (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorEta]
    :: lstFanLayerList 1 (fun _sourceRow => 1))) identityEntries = true)
#eval decide (doEntriesAgreeUpTo 1 2 (sldLayersDenote (lstFanLayerList 1 (fun _sourceRow => 0)))
  (sldLayersDenote [sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorEpsilon]]) = true)
#eval decide (doEntriesAgreeUpTo 1 1
  (sldLayersDenote (lstCanonicalLayerList 1 1 (fun _rowIndex _colIndex => 1)))
  (sldLayersDenote (lstCanonicalLayerList 1 1 (fun _rowIndex _colIndex => 2))) = false)
#eval decide (sldLayersAreComposableFrom 2
  (sldPadLayer 1 0 [SldCell.generatorEta] :: lstCanonicalLayerList 2 2 lstFireMatrix) = false)
#eval decide (sldLayersAreComposableFrom 1
  (sldPadLayer 1 0 [SldCell.generatorEta] :: lstCanonicalLayerList 2 2 lstFireMatrix) = true)

end FX1Poly.Polygraph.Omega.LafontProp
