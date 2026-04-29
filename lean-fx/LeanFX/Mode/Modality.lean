import LeanFX.Mode.Defn

/-! # Abstract mode 1-category data.

This file contains only the axiom-free 1-cell substrate for later
modal typing rules.  Concrete FX modalities and 2-cells land in later
files; this layer is deliberately independent of `Syntax`.
-/

namespace LeanFX.Mode

universe modeUniverse modalityUniverse

/-- A category of modes and modalities.

`ModeCarrier` is intentionally abstract here.  The concrete four-mode
FX instance will use `LeanFX.Mode.Mode` as its carrier later; this
structure is the reusable law package for any mode category.
-/
structure ModalityCat where
  /-- Objects of the mode category. -/
  ModeCarrier : Type modeUniverse
  /-- 1-cells between modes. -/
  Modality : ModeCarrier → ModeCarrier → Type modalityUniverse
  /-- Identity modality at a mode. -/
  idMod : (sourceMode : ModeCarrier) → Modality sourceMode sourceMode
  /-- Modality composition, ordered left-to-right. -/
  compMod :
    {sourceMode middleMode targetMode : ModeCarrier} →
      Modality sourceMode middleMode →
      Modality middleMode targetMode →
      Modality sourceMode targetMode
  /-- Left identity law for modality composition. -/
  idLeft :
    {sourceMode targetMode : ModeCarrier} →
      (modality : Modality sourceMode targetMode) →
        compMod (idMod sourceMode) modality = modality
  /-- Right identity law for modality composition. -/
  idRight :
    {sourceMode targetMode : ModeCarrier} →
      (modality : Modality sourceMode targetMode) →
        compMod modality (idMod targetMode) = modality
  /-- Associativity law for modality composition. -/
  compAssoc :
    {firstMode secondMode thirdMode fourthMode : ModeCarrier} →
      (firstModality : Modality firstMode secondMode) →
      (secondModality : Modality secondMode thirdMode) →
      (thirdModality : Modality thirdMode fourthMode) →
        compMod (compMod firstModality secondModality) thirdModality =
          compMod firstModality (compMod secondModality thirdModality)

namespace ModalityCat

/-- Object carrier of a modality category. -/
abbrev ModeObject (modeCategory : ModalityCat) : Type modeUniverse :=
  modeCategory.ModeCarrier

/-- Identity modality wrapper. -/
@[inline]
def identityModality (modeCategory : ModalityCat)
    (sourceMode : modeCategory.ModeCarrier) :
    modeCategory.Modality sourceMode sourceMode :=
  modeCategory.idMod sourceMode

/-- Modality composition wrapper. -/
@[inline]
def composeModality (modeCategory : ModalityCat)
    {sourceMode middleMode targetMode : modeCategory.ModeCarrier}
    (firstModality : modeCategory.Modality sourceMode middleMode)
    (secondModality : modeCategory.Modality middleMode targetMode) :
    modeCategory.Modality sourceMode targetMode :=
  modeCategory.compMod firstModality secondModality

/-- Left identity through the wrapper API. -/
theorem compose_identity_left (modeCategory : ModalityCat)
    {sourceMode targetMode : modeCategory.ModeCarrier}
    (modality : modeCategory.Modality sourceMode targetMode) :
    modeCategory.composeModality
      (modeCategory.identityModality sourceMode) modality = modality :=
  modeCategory.idLeft modality

/-- Right identity through the wrapper API. -/
theorem compose_identity_right (modeCategory : ModalityCat)
    {sourceMode targetMode : modeCategory.ModeCarrier}
    (modality : modeCategory.Modality sourceMode targetMode) :
    modeCategory.composeModality
      modality (modeCategory.identityModality targetMode) = modality :=
  modeCategory.idRight modality

/-- Associativity through the wrapper API. -/
theorem compose_assoc (modeCategory : ModalityCat)
    {firstMode secondMode thirdMode fourthMode : modeCategory.ModeCarrier}
    (firstModality : modeCategory.Modality firstMode secondMode)
    (secondModality : modeCategory.Modality secondMode thirdMode)
    (thirdModality : modeCategory.Modality thirdMode fourthMode) :
    modeCategory.composeModality
        (modeCategory.composeModality firstModality secondModality)
        thirdModality =
      modeCategory.composeModality
        firstModality
        (modeCategory.composeModality secondModality thirdModality) :=
  modeCategory.compAssoc firstModality secondModality thirdModality

end ModalityCat

namespace SmokeTestModalityCat

/-- The terminal one-mode modality category. -/
def unitModalityCat : ModalityCat where
  ModeCarrier := Unit
  Modality := fun _ _ => Unit
  idMod := fun _ => ()
  compMod := fun _ _ => ()
  idLeft := fun _ => rfl
  idRight := fun _ => rfl
  compAssoc := fun _ _ _ => rfl

/-- Identity modality in the one-mode category. -/
example : unitModalityCat.Modality () () :=
  unitModalityCat.identityModality ()

/-- Composition in the one-mode category. -/
example :
    unitModalityCat.composeModality
      (unitModalityCat.identityModality ())
      (unitModalityCat.identityModality ()) = () :=
  rfl

/-- Left identity law smoke. -/
example (modality : unitModalityCat.Modality () ()) :
    unitModalityCat.composeModality
      (unitModalityCat.identityModality ()) modality = modality :=
  unitModalityCat.compose_identity_left modality

/-- Right identity law smoke. -/
example (modality : unitModalityCat.Modality () ()) :
    unitModalityCat.composeModality
      modality (unitModalityCat.identityModality ()) = modality :=
  unitModalityCat.compose_identity_right modality

/-- Associativity law smoke. -/
example
    (firstModality secondModality thirdModality :
      unitModalityCat.Modality () ()) :
    unitModalityCat.composeModality
        (unitModalityCat.composeModality firstModality secondModality)
        thirdModality =
      unitModalityCat.composeModality
        firstModality
        (unitModalityCat.composeModality secondModality thirdModality) :=
  unitModalityCat.compose_assoc firstModality secondModality thirdModality

end SmokeTestModalityCat

end LeanFX.Mode
