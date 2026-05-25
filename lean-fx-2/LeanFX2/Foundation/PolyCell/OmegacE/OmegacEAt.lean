/-!
# ωcE Polygraph — Walking Coherent ω-Equivalence (HLOR Construction 1.22)

This file contains only the finite generator scaffold for the walking
coherent equivalence.  It does not construct the HLOR pushout presentation,
contractibility theorem, universal classifier, or Makkai word-equality
procedure.

For FX: cells are coherent ω-equivalences iff there exists an
ω-functor from Σ^(n-1)(ωcE) factoring them.  That classifier is an Axis 9
target, not a theorem supplied by this scaffold.

Reference: arXiv:2404.14509 Construction 1.22.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.OmegacE

/-- How much of Axis 9 has actually been constructed.

The current file supplies a small indexed generator family.  The real HLOR
construction, its finite-type package, contractibility theorem, universal
classifier, and Makkai word-equality algorithm are separate proof packages. -/
inductive OmegacEConstructionLevel where
  /-- Only the indexed generator scaffold has been constructed. -/
  | finiteGeneratorScaffold
  /-- Source and target boundaries for the generators have been supplied. -/
  | boundaryPresented
  /-- The HLOR pushout construction has been formalized. -/
  | hlorPushoutConstruction
  /-- A finite-type family has been tied to the generated polygraph. -/
  | finiteTypeFamily
  /-- Contractibility of the coherent equivalence has been proved. -/
  | contractibilityTheorem
  /-- The universal classifier theorem has been proved. -/
  | universalClassifier
  /-- A word-equality decision procedure has been supplied. -/
  | makkaiWordEquality
  deriving DecidableEq, Repr

/-- Whether this Axis 9 level includes generator boundary data. -/
def OmegacEConstructionLevel.hasBoundaryPresentation :
    OmegacEConstructionLevel → Bool
  | .finiteGeneratorScaffold => false
  | .boundaryPresented => true
  | .hlorPushoutConstruction => true
  | .finiteTypeFamily => true
  | .contractibilityTheorem => true
  | .universalClassifier => true
  | .makkaiWordEquality => true

/-- Whether this Axis 9 level includes the HLOR pushout construction. -/
def OmegacEConstructionLevel.hasHLORPushout :
    OmegacEConstructionLevel → Bool
  | .finiteGeneratorScaffold => false
  | .boundaryPresented => false
  | .hlorPushoutConstruction => true
  | .finiteTypeFamily => true
  | .contractibilityTheorem => true
  | .universalClassifier => true
  | .makkaiWordEquality => true

/-- Whether this Axis 9 level includes a finite-type family theorem. -/
def OmegacEConstructionLevel.hasFiniteTypeFamily :
    OmegacEConstructionLevel → Bool
  | .finiteGeneratorScaffold => false
  | .boundaryPresented => false
  | .hlorPushoutConstruction => false
  | .finiteTypeFamily => true
  | .contractibilityTheorem => true
  | .universalClassifier => true
  | .makkaiWordEquality => true

/-- Whether this Axis 9 level includes contractibility. -/
def OmegacEConstructionLevel.hasContractibility :
    OmegacEConstructionLevel → Bool
  | .finiteGeneratorScaffold => false
  | .boundaryPresented => false
  | .hlorPushoutConstruction => false
  | .finiteTypeFamily => false
  | .contractibilityTheorem => true
  | .universalClassifier => true
  | .makkaiWordEquality => true

/-- Whether this Axis 9 level includes the universal classifier theorem. -/
def OmegacEConstructionLevel.hasUniversalClassifier :
    OmegacEConstructionLevel → Bool
  | .finiteGeneratorScaffold => false
  | .boundaryPresented => false
  | .hlorPushoutConstruction => false
  | .finiteTypeFamily => false
  | .contractibilityTheorem => false
  | .universalClassifier => true
  | .makkaiWordEquality => true

/-- Whether this Axis 9 level includes Makkai word equality. -/
def OmegacEConstructionLevel.hasMakkaiWordEquality :
    OmegacEConstructionLevel → Bool
  | .finiteGeneratorScaffold => false
  | .boundaryPresented => false
  | .hlorPushoutConstruction => false
  | .finiteTypeFamily => false
  | .contractibilityTheorem => false
  | .universalClassifier => false
  | .makkaiWordEquality => true

/-- Current FX Axis 9 construction level. -/
def fxOmegacEConstructionLevel : OmegacEConstructionLevel :=
  .finiteGeneratorScaffold

/-- The ωcE generator scaffold at dimension k.
This is not yet the full free higher-category presentation.

dim 0: 2 vertices (source/target of the walking equivalence)
dim 1: 2 cells (the quasi-isomorphism and its formal reverse)
dim 2: 2 cells α β (unit/counit 2-cells) + extends of dim-1
dim k+1: 2 new cells (higher coherence) + extends of dim-k -/
inductive OmegacECell : (dimension : Nat) → Type where
  /-- Source vertex of the walking equivalence. -/
  | sourceVertex : OmegacECell 0
  /-- Target vertex of the walking equivalence. -/
  | targetVertex : OmegacECell 0
  /-- The quasi-isomorphism cell (the "walking" 1-equivalence). -/
  | quasiIso : OmegacECell 1
  /-- The quasi-inverse (reverse direction). -/
  | quasiInverse : OmegacECell 1
  /-- Alpha cell: unit 2-cell (id → q∘q⁻¹). -/
  | alphaUnit : OmegacECell 2
  /-- Beta cell: counit 2-cell (q⁻¹∘q → id). -/
  | betaCounit : OmegacECell 2
  /-- Higher coherence at dim k+3: witnesses that alpha/beta satisfy
  triangle identities up to coherent homotopy. -/
  | higherCoherence : (baseDim : Nat) → (cellIndex : Fin 2) → OmegacECell (baseDim + 3)
  deriving DecidableEq, Repr

/-- Count cells at each dimension. -/
def OmegacECell.countAtDim (_dimension : Nat) : Nat :=
  2

/-- Canonical first slot in the two-generator scaffold. -/
def OmegacECell.slotZero : Fin 2 :=
  ⟨0, Nat.zero_lt_succ 1⟩

/-- Canonical second slot in the two-generator scaffold. -/
def OmegacECell.slotOne : Fin 2 :=
  ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩

/-- The first scaffold generator at a dimension. -/
def OmegacECell.firstAtDim : (dimension : Nat) → OmegacECell dimension
  | 0 => .sourceVertex
  | 1 => .quasiIso
  | 2 => .alphaUnit
  | Nat.succ (Nat.succ (Nat.succ baseDimension)) =>
    .higherCoherence baseDimension OmegacECell.slotZero

/-- The second scaffold generator at a dimension. -/
def OmegacECell.secondAtDim : (dimension : Nat) → OmegacECell dimension
  | 0 => .targetVertex
  | 1 => .quasiInverse
  | 2 => .betaCounit
  | Nat.succ (Nat.succ (Nat.succ baseDimension)) =>
    .higherCoherence baseDimension OmegacECell.slotOne

/-- Select one of the two scaffold generators at a dimension. -/
def OmegacECell.atSlot (dimension : Nat) (slot : Fin 2) :
    OmegacECell dimension :=
  if slot.val == 0 then
    OmegacECell.firstAtDim dimension
  else
    OmegacECell.secondAtDim dimension

/-- Select a scaffold generator using the declared count at that dimension. -/
def OmegacECell.atDeclaredIndex (dimension : Nat)
    (declaredIndex : Fin (OmegacECell.countAtDim dimension)) :
    OmegacECell dimension :=
  OmegacECell.atSlot dimension declaredIndex

/-- Recover the canonical slot for a scaffold generator.

This is finite scaffold readback only.  It says every currently represented
generator is one of the two explicit slots at its dimension; it does not add
boundary data or any coherent-equivalence theorem. -/
def OmegacECell.slotOf : {dimension : Nat} →
    OmegacECell dimension → Fin 2
  | _, .sourceVertex => OmegacECell.slotZero
  | _, .targetVertex => OmegacECell.slotOne
  | _, .quasiIso => OmegacECell.slotZero
  | _, .quasiInverse => OmegacECell.slotOne
  | _, .alphaUnit => OmegacECell.slotZero
  | _, .betaCounit => OmegacECell.slotOne
  | _, .higherCoherence _ cellIndex =>
      cellIndex

/-- Recover the declared-count index for a scaffold generator. -/
def OmegacECell.declaredIndexOf : {dimension : Nat} →
    OmegacECell dimension → Fin (OmegacECell.countAtDim dimension)
  | _, cell => OmegacECell.slotOf cell

/-- Recover the numeric table slot for a scaffold generator. -/
def OmegacECell.slotValueOf : {dimension : Nat} →
    OmegacECell dimension → Nat
  | _, cell => (OmegacECell.slotOf cell).val

/-- Recover the numeric declared-count table index for a scaffold generator. -/
def OmegacECell.declaredIndexValueOf : {dimension : Nat} →
    OmegacECell dimension → Nat
  | _, cell => (OmegacECell.declaredIndexOf cell).val

/-- The two declared slots in the current generator scaffold. -/
inductive OmegacECell.SlotKind where
  /-- The first declared generator at a dimension. -/
  | first
  /-- The second declared generator at a dimension. -/
  | second
  deriving DecidableEq, Repr

/-- Recover a proof-free slot classifier for a scaffold generator. -/
def OmegacECell.slotKindOf : {dimension : Nat} →
    OmegacECell dimension → OmegacECell.SlotKind
  | _, cell =>
    if OmegacECell.slotValueOf cell == 0 then
      .first
    else
      .second

/-- Whether a scaffold generator is in the first declared slot. -/
def OmegacECell.isFirstSlot : {dimension : Nat} →
    OmegacECell dimension → Bool
  | _, cell => OmegacECell.slotKindOf cell == .first

/-- Whether a scaffold generator is in the second declared slot. -/
def OmegacECell.isSecondSlot : {dimension : Nat} →
    OmegacECell dimension → Bool
  | _, cell => OmegacECell.slotKindOf cell == .second

/-- The two scaffold generators at a dimension, in canonical order. -/
def OmegacECell.cellsAtDim (dimension : Nat) :
    List (OmegacECell dimension) :=
  [OmegacECell.firstAtDim dimension, OmegacECell.secondAtDim dimension]

/-- Total cells up to and including dimension k. -/
def OmegacECell.totalUpTo : Nat → Nat
  | 0 => 2
  | n + 1 => totalUpTo n + countAtDim (n + 1)

/-- ωcE at dim 0 has exactly 2 cells. -/
theorem OmegacECell.count_dim0 : OmegacECell.countAtDim 0 = 2 := rfl

/-- ωcE at dim 1 has exactly 2 cells. -/
theorem OmegacECell.count_dim1 : OmegacECell.countAtDim 1 = 2 := rfl

/-- ωcE at dim 2 has exactly 2 cells. -/
theorem OmegacECell.count_dim2 : OmegacECell.countAtDim 2 = 2 := rfl

/-- Total up to dim 0 = 2. -/
theorem OmegacECell.total_dim0 : OmegacECell.totalUpTo 0 = 2 := rfl

/-- Total up to dim 1 = 4. -/
theorem OmegacECell.total_dim1 : OmegacECell.totalUpTo 1 = 4 := rfl

/-- Total up to dim 2 = 6. -/
theorem OmegacECell.total_dim2 : OmegacECell.totalUpTo 2 = 6 := rfl

/-- Dimension of a cell (projection from the index). -/
def OmegacECell.dimension : {dim : Nat} → OmegacECell dim → Nat
  | dim, _ => dim

/-- The zero slot selects the first scaffold generator. -/
theorem OmegacECell.atSlot_zero (dimension : Nat) :
    OmegacECell.atSlot dimension ⟨0, by decide⟩ =
      OmegacECell.firstAtDim dimension := rfl

/-- The one slot selects the second scaffold generator. -/
theorem OmegacECell.atSlot_one (dimension : Nat) :
    OmegacECell.atSlot dimension ⟨1, by decide⟩ =
      OmegacECell.secondAtDim dimension := rfl

/-- The canonical zero slot selects the first scaffold generator. -/
theorem OmegacECell.atSlot_slotZero (dimension : Nat) :
    OmegacECell.atSlot dimension OmegacECell.slotZero =
      OmegacECell.firstAtDim dimension := rfl

/-- The canonical one slot selects the second scaffold generator. -/
theorem OmegacECell.atSlot_slotOne (dimension : Nat) :
    OmegacECell.atSlot dimension OmegacECell.slotOne =
      OmegacECell.secondAtDim dimension := rfl

/-- The declared zero index selects the first scaffold generator. -/
theorem OmegacECell.atDeclaredIndex_slotZero (dimension : Nat) :
    OmegacECell.atDeclaredIndex dimension OmegacECell.slotZero =
      OmegacECell.firstAtDim dimension := rfl

/-- The declared one index selects the second scaffold generator. -/
theorem OmegacECell.atDeclaredIndex_slotOne (dimension : Nat) :
    OmegacECell.atDeclaredIndex dimension OmegacECell.slotOne =
      OmegacECell.secondAtDim dimension := rfl

/-- The first scaffold generator reads back to slot zero. -/
theorem OmegacECell.slotOf_firstAtDim (dimension : Nat) :
    OmegacECell.slotOf (OmegacECell.firstAtDim dimension) =
      OmegacECell.slotZero := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- The second scaffold generator reads back to slot one. -/
theorem OmegacECell.slotOf_secondAtDim (dimension : Nat) :
    OmegacECell.slotOf (OmegacECell.secondAtDim dimension) =
      OmegacECell.slotOne := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- Selecting the canonical zero slot reads back to that same slot. -/
theorem OmegacECell.slotOf_atSlot_slotZero (dimension : Nat) :
    OmegacECell.slotOf
      (OmegacECell.atSlot dimension OmegacECell.slotZero) =
      OmegacECell.slotZero :=
  OmegacECell.slotOf_firstAtDim dimension

/-- Selecting the canonical one slot reads back to that same slot. -/
theorem OmegacECell.slotOf_atSlot_slotOne (dimension : Nat) :
    OmegacECell.slotOf
      (OmegacECell.atSlot dimension OmegacECell.slotOne) =
      OmegacECell.slotOne :=
  OmegacECell.slotOf_secondAtDim dimension

/-- The first scaffold generator has declared index zero. -/
theorem OmegacECell.declaredIndexOf_firstAtDim (dimension : Nat) :
    OmegacECell.declaredIndexOf (OmegacECell.firstAtDim dimension) =
      OmegacECell.slotZero :=
  OmegacECell.slotOf_firstAtDim dimension

/-- The second scaffold generator has declared index one. -/
theorem OmegacECell.declaredIndexOf_secondAtDim (dimension : Nat) :
    OmegacECell.declaredIndexOf (OmegacECell.secondAtDim dimension) =
      OmegacECell.slotOne :=
  OmegacECell.slotOf_secondAtDim dimension

/-- Selecting declared index zero reads back to declared index zero. -/
theorem OmegacECell.declaredIndexOf_atDeclaredIndex_slotZero
    (dimension : Nat) :
    OmegacECell.declaredIndexOf
      (OmegacECell.atDeclaredIndex dimension OmegacECell.slotZero) =
      OmegacECell.slotZero :=
  OmegacECell.slotOf_atSlot_slotZero dimension

/-- Selecting declared index one reads back to declared index one. -/
theorem OmegacECell.declaredIndexOf_atDeclaredIndex_slotOne
    (dimension : Nat) :
    OmegacECell.declaredIndexOf
      (OmegacECell.atDeclaredIndex dimension OmegacECell.slotOne) =
      OmegacECell.slotOne :=
  OmegacECell.slotOf_atSlot_slotOne dimension

/-- Numeric slots are bounded by the declared scaffold count. -/
theorem OmegacECell.slotValueOf_lt_countAtDim {dimension : Nat}
    (cell : OmegacECell dimension) :
    OmegacECell.slotValueOf cell < OmegacECell.countAtDim dimension :=
  (OmegacECell.slotOf cell).isLt

/-- Numeric declared indices are bounded by the declared scaffold count. -/
theorem OmegacECell.declaredIndexValueOf_lt_countAtDim {dimension : Nat}
    (cell : OmegacECell dimension) :
    OmegacECell.declaredIndexValueOf cell <
      OmegacECell.countAtDim dimension :=
  (OmegacECell.declaredIndexOf cell).isLt

/-- The first scaffold generator has numeric slot zero. -/
theorem OmegacECell.slotValueOf_firstAtDim (dimension : Nat) :
    OmegacECell.slotValueOf (OmegacECell.firstAtDim dimension) = 0 := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- The second scaffold generator has numeric slot one. -/
theorem OmegacECell.slotValueOf_secondAtDim (dimension : Nat) :
    OmegacECell.slotValueOf (OmegacECell.secondAtDim dimension) = 1 := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- Selecting declared index zero reads back to numeric slot zero. -/
theorem OmegacECell.declaredIndexValueOf_atDeclaredIndex_slotZero
    (dimension : Nat) :
    OmegacECell.declaredIndexValueOf
      (OmegacECell.atDeclaredIndex dimension OmegacECell.slotZero) = 0 := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- Selecting declared index one reads back to numeric slot one. -/
theorem OmegacECell.declaredIndexValueOf_atDeclaredIndex_slotOne
    (dimension : Nat) :
    OmegacECell.declaredIndexValueOf
      (OmegacECell.atDeclaredIndex dimension OmegacECell.slotOne) = 1 := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- The first scaffold generator classifies as the first slot. -/
theorem OmegacECell.slotKindOf_firstAtDim (dimension : Nat) :
    OmegacECell.slotKindOf (OmegacECell.firstAtDim dimension) =
      OmegacECell.SlotKind.first := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- The second scaffold generator classifies as the second slot. -/
theorem OmegacECell.slotKindOf_secondAtDim (dimension : Nat) :
    OmegacECell.slotKindOf (OmegacECell.secondAtDim dimension) =
      OmegacECell.SlotKind.second := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- Selecting declared index zero classifies as the first slot. -/
theorem OmegacECell.slotKindOf_atDeclaredIndex_slotZero
    (dimension : Nat) :
    OmegacECell.slotKindOf
      (OmegacECell.atDeclaredIndex dimension OmegacECell.slotZero) =
      OmegacECell.SlotKind.first := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- Selecting declared index one classifies as the second slot. -/
theorem OmegacECell.slotKindOf_atDeclaredIndex_slotOne
    (dimension : Nat) :
    OmegacECell.slotKindOf
      (OmegacECell.atDeclaredIndex dimension OmegacECell.slotOne) =
      OmegacECell.SlotKind.second := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- The first scaffold generator is detected by the first-slot predicate. -/
theorem OmegacECell.isFirstSlot_firstAtDim (dimension : Nat) :
    OmegacECell.isFirstSlot (OmegacECell.firstAtDim dimension) = true := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- The second scaffold generator is not detected by the first-slot predicate. -/
theorem OmegacECell.isFirstSlot_secondAtDim (dimension : Nat) :
    OmegacECell.isFirstSlot (OmegacECell.secondAtDim dimension) = false := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- The first scaffold generator is not detected by the second-slot predicate. -/
theorem OmegacECell.isSecondSlot_firstAtDim (dimension : Nat) :
    OmegacECell.isSecondSlot (OmegacECell.firstAtDim dimension) = false := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- The second scaffold generator is detected by the second-slot predicate. -/
theorem OmegacECell.isSecondSlot_secondAtDim (dimension : Nat) :
    OmegacECell.isSecondSlot (OmegacECell.secondAtDim dimension) = true := by
  cases dimension with
  | zero => rfl
  | succ dimensionTail =>
    cases dimensionTail with
    | zero => rfl
    | succ dimensionTail =>
      cases dimensionTail with
      | zero => rfl
      | succ _ => rfl

/-- The explicit generator list has the declared scaffold count. -/
theorem OmegacECell.cellsAtDim_length_eq_countAtDim (dimension : Nat) :
    (OmegacECell.cellsAtDim dimension).length =
      OmegacECell.countAtDim dimension := rfl

/-- The two canonical scaffold generators are distinct at every dimension. -/
theorem OmegacECell.firstAtDim_ne_secondAtDim (dimension : Nat) :
    OmegacECell.firstAtDim dimension ≠
      OmegacECell.secondAtDim dimension := by
  cases dimension with
  | zero =>
    intro equalityProof
    cases equalityProof
  | succ dimensionTail =>
    cases dimensionTail with
    | zero =>
      intro equalityProof
      cases equalityProof
    | succ dimensionTail =>
      cases dimensionTail with
      | zero =>
        intro equalityProof
        cases equalityProof
      | succ baseDimension =>
        intro equalityProof
        cases equalityProof

/-- The scaffold ledger records two generators at every dimension. -/
theorem OmegacECell.countAtDim_eq_two (dimension : Nat) :
    OmegacECell.countAtDim dimension = 2 := rfl

/-- The scaffold count is bounded by two at every dimension. -/
theorem OmegacECell.countAtDim_le_two (dimension : Nat) :
    OmegacECell.countAtDim dimension ≤ 2 :=
  Nat.le_refl 2

/-- FX Axis 9 currently has only the finite generator scaffold. -/
theorem fxOmegacEConstructionLevel_eq :
    fxOmegacEConstructionLevel =
      OmegacEConstructionLevel.finiteGeneratorScaffold := rfl

/-- FX Axis 9 currently has no generator boundary presentation. -/
theorem fxOmegacE_hasNoBoundaryPresentation :
    fxOmegacEConstructionLevel.hasBoundaryPresentation = false := rfl

/-- FX Axis 9 currently has no HLOR pushout construction. -/
theorem fxOmegacE_hasNoHLORPushout :
    fxOmegacEConstructionLevel.hasHLORPushout = false := rfl

/-- FX Axis 9 currently has no finite-type family theorem. -/
theorem fxOmegacE_hasNoFiniteTypeFamily :
    fxOmegacEConstructionLevel.hasFiniteTypeFamily = false := rfl

/-- FX Axis 9 currently has no contractibility theorem. -/
theorem fxOmegacE_hasNoContractibility :
    fxOmegacEConstructionLevel.hasContractibility = false := rfl

/-- FX Axis 9 currently has no universal classifier theorem. -/
theorem fxOmegacE_hasNoUniversalClassifier :
    fxOmegacEConstructionLevel.hasUniversalClassifier = false := rfl

/-- FX Axis 9 currently has no Makkai word-equality procedure. -/
theorem fxOmegacE_hasNoMakkaiWordEquality :
    fxOmegacEConstructionLevel.hasMakkaiWordEquality = false := rfl

end LeanFX2.Foundation.PolyCell.OmegacE
