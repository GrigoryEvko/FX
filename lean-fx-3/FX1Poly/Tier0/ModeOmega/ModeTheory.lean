/-! # Tier0/ModeOmega/ModeTheory — the native mode-theory substrate (mode axis)

The **canonical, Tier-0-native home** of the mode 2-category: objects are modes, 1-cells are modalities,
2-cells are coherences (Gratzer arXiv:2301.11842 §2).  This file builds the mode-category interface, the
trivial one-object instance, and the concrete finite FX mode theory `fxModeTheory` — the dim-0/dim-1 core
of the mode ω-category (`Interface.lean`).  It does NOT decide FX conversion; that is the future Gratzer
normalization route.

Previously this substrate lived under `MTTNorm/ModeTheory.lean`, forcing the sealed `Tier0/ModeOmega`
namespace to import the higher `MTTNorm` layer.  It is now native to Tier 0; `MTTNorm/ModeTheory.lean`
re-exports it, so the dependency arrow points Core/MTTNorm → Tier0 (not the reverse).

Reference: arXiv:2301.11842 §2.  Zero external dependencies; raw Lean 4 + Init only.  All declarations are
structures, total functions, and constructor witnesses. -/

namespace FX1Poly.Tier0.ModeOmega

/-- A mode theory: finitary 2-category for the modal structure. -/
structure ModeTheory where
  Mode : Type
  Modality : Mode → Mode → Type
  identityModality : (mode : Mode) → Modality mode mode
  composeModality : {modeA modeB modeC : Mode} →
    Modality modeA modeB → Modality modeB modeC → Modality modeA modeC
  composeAssoc : {modeA modeB modeC modeD : Mode} →
    (modalityF : Modality modeA modeB) →
    (modalityG : Modality modeB modeC) →
    (modalityH : Modality modeC modeD) →
    composeModality (composeModality modalityF modalityG) modalityH =
      composeModality modalityF (composeModality modalityG modalityH)
  identityLeft : {modeA modeB : Mode} →
    (modalityF : Modality modeA modeB) →
    composeModality (identityModality modeA) modalityF = modalityF
  identityRight : {modeA modeB : Mode} →
    (modalityF : Modality modeA modeB) →
    composeModality modalityF (identityModality modeB) = modalityF

/-- Rigidity input record: each modality fiber has decidable equality.
This is mode-category data only; it is not a normalization theorem. -/
structure ModeTheoryRigid extends ModeTheory where
  modalityDecEq : (modeA modeB : toModeTheory.Mode) →
    DecidableEq (toModeTheory.Modality modeA modeB)

/-- Readiness record for the future Gratzer formalization.  Populating this
record does not construct MTT syntax or decide conversion. -/
structure GratzerReady extends ModeTheoryRigid where
  modeDecEq : DecidableEq toModeTheory.Mode

/-- The single object of the trivial mode theory. -/
inductive TrivialMode where
  | mode
  deriving DecidableEq, Repr

/-- The single identity modality of the trivial mode theory. -/
inductive TrivialModality : TrivialMode → TrivialMode → Type where
  | identity : TrivialModality .mode .mode

def TrivialModality.compose {modeA modeB modeC : TrivialMode} :
    TrivialModality modeA modeB →
    TrivialModality modeB modeC →
    TrivialModality modeA modeC := by
  intro modalityF modalityG
  cases modalityF
  cases modalityG
  exact .identity

theorem TrivialModality.compose_assoc
    {modeA modeB modeC modeD : TrivialMode}
    (modalityF : TrivialModality modeA modeB)
    (modalityG : TrivialModality modeB modeC)
    (modalityH : TrivialModality modeC modeD) :
    TrivialModality.compose (TrivialModality.compose modalityF modalityG) modalityH =
      TrivialModality.compose modalityF (TrivialModality.compose modalityG modalityH) := by
  cases modalityF
  cases modalityG
  cases modalityH
  rfl

theorem TrivialModality.identity_left
    {modeA modeB : TrivialMode}
    (modalityF : TrivialModality modeA modeB) :
    TrivialModality.compose TrivialModality.identity modalityF = modalityF := by
  cases modalityF
  rfl

theorem TrivialModality.identity_right
    {modeA modeB : TrivialMode}
    (modalityF : TrivialModality modeA modeB) :
    TrivialModality.compose modalityF TrivialModality.identity = modalityF := by
  cases modalityF
  rfl

/-- The trivial mode theory: 1 mode, 1 modality. MTT over this = plain MLTT. -/
def trivialModeTheory : ModeTheory where
  Mode := TrivialMode
  Modality := TrivialModality
  identityModality := fun _ => .identity
  composeModality := TrivialModality.compose
  composeAssoc := TrivialModality.compose_assoc
  identityLeft := TrivialModality.identity_left
  identityRight := TrivialModality.identity_right

/-- Trivial theory supplies the readiness input record. -/
def trivialGratzerReady : GratzerReady where
  toModeTheoryRigid := {
    toModeTheory := trivialModeTheory
    modalityDecEq := by
      intro modeA modeB
      cases modeA
      cases modeB
      intro modalityA modalityB
      cases modalityA
      cases modalityB
      exact .isTrue rfl
  }
  modeDecEq := by
    intro modeA modeB
    cases modeA
    cases modeB
    exact .isTrue rfl

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
  | ghostToPure : FXModeShift .ghost .pure
  | pureToClassified : FXModeShift .pure .classified
  | linearToAffine : FXModeShift .linear .affine
  | affineToUnrestricted : FXModeShift .affine .unrestricted
  | pureToAsync : FXModeShift .pure .async
  deriving DecidableEq, Repr

/-- Free modality paths generated by the finite FX mode shifts. -/
inductive FXModePath : FXModeAtom → FXModeAtom → Type where
  | identity : (mode : FXModeAtom) → FXModePath mode mode
  | cons {modeA modeB modeC : FXModeAtom} : FXModeShift modeA modeB →
      FXModePath modeB modeC → FXModePath modeA modeC
  deriving DecidableEq, Repr

/-- Path composition for FX modalities. -/
def FXModePath.compose {modeA modeB modeC : FXModeAtom} :
    FXModePath modeA modeB →
    FXModePath modeB modeC →
    FXModePath modeA modeC
  | .identity _, pathG => pathG
  | .cons shiftF pathF, pathG => .cons shiftF (pathF.compose pathG)

theorem FXModePath.compose_assoc
    {modeA modeB modeC modeD : FXModeAtom}
    (pathF : FXModePath modeA modeB)
    (pathG : FXModePath modeB modeC)
    (pathH : FXModePath modeC modeD) :
    (pathF.compose pathG).compose pathH =
      pathF.compose (pathG.compose pathH) := by
  induction pathF with
  | identity _ => rfl
  | cons shiftF pathTail inductionHypothesis =>
      dsimp only [compose]
      rw [inductionHypothesis]

theorem FXModePath.identity_left
    {modeA modeB : FXModeAtom}
    (pathF : FXModePath modeA modeB) :
    (FXModePath.identity modeA).compose pathF = pathF := rfl

theorem FXModePath.identity_right
    {modeA modeB : FXModeAtom}
    (pathF : FXModePath modeA modeB) :
    pathF.compose (FXModePath.identity modeB) = pathF := by
  induction pathF with
  | identity _ => rfl
  | cons shiftF pathTail inductionHypothesis =>
      dsimp only [compose]
      rw [inductionHypothesis]

/-- The FX mode theory: the free finite-path category over the accepted
mode shifts. -/
def fxModeTheory : ModeTheory where
  Mode := FXModeAtom
  Modality := FXModePath
  identityModality := FXModePath.identity
  composeModality := FXModePath.compose
  composeAssoc := FXModePath.compose_assoc
  identityLeft := FXModePath.identity_left
  identityRight := FXModePath.identity_right

/-- FX mode theory supplies decidable equality for finite modality paths. -/
def fxModeTheoryRigid : ModeTheoryRigid where
  toModeTheory := fxModeTheory
  modalityDecEq := by
    intro modeA modeB
    change DecidableEq (FXModePath modeA modeB)
    infer_instance

/-- FX mode theory supplies the readiness input record.  This is not the
Gratzer normalization theorem and not an FX conversion procedure. -/
def fxGratzerReady : GratzerReady where
  toModeTheoryRigid := fxModeTheoryRigid
  modeDecEq := by
    change DecidableEq FXModeAtom
    infer_instance

end FX1Poly.Tier0.ModeOmega
