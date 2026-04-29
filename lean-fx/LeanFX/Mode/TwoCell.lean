import LeanFX.Mode.Modality

/-! # Abstract mode 2-cell preorder.

`TwoCellCat` extends the mode 1-category with Prop-valued 2-cells.
Concrete FX subsumption and collision rules are later instances; this
file only fixes the reusable preorder and horizontal-composition data.
-/

namespace LeanFX.Mode

universe modeUniverse modalityUniverse

/-- A mode category equipped with Prop-valued 2-cells between parallel
modalities. -/
structure TwoCellCat extends ModalityCat.{modeUniverse, modalityUniverse} where
  /-- 2-cells between parallel modalities. -/
  TwoCell :
    {sourceMode targetMode : ModeCarrier} →
      Modality sourceMode targetMode →
      Modality sourceMode targetMode →
      Prop
  /-- Reflexivity of the 2-cell preorder. -/
  twoCellRefl :
    {sourceMode targetMode : ModeCarrier} →
      (modality : Modality sourceMode targetMode) →
        TwoCell modality modality
  /-- Transitivity of the 2-cell preorder. -/
  twoCellTrans :
    {sourceMode targetMode : ModeCarrier} →
      {firstModality secondModality thirdModality :
        Modality sourceMode targetMode} →
      TwoCell firstModality secondModality →
      TwoCell secondModality thirdModality →
        TwoCell firstModality thirdModality
  /-- Horizontal composition of 2-cells. -/
  twoCellWhisker :
    {sourceMode middleMode targetMode : ModeCarrier} →
      {firstLeftModality firstRightModality :
        Modality sourceMode middleMode} →
      {secondLeftModality secondRightModality :
        Modality middleMode targetMode} →
      TwoCell firstLeftModality firstRightModality →
      TwoCell secondLeftModality secondRightModality →
        TwoCell
          (compMod firstLeftModality secondLeftModality)
          (compMod firstRightModality secondRightModality)

namespace TwoCellCat

/-- Reflexive 2-cell wrapper. -/
@[inline]
def identityTwoCell (twoCellCategory : TwoCellCat)
    {sourceMode targetMode : twoCellCategory.ModeCarrier}
    (modality : twoCellCategory.Modality sourceMode targetMode) :
    twoCellCategory.TwoCell modality modality :=
  twoCellCategory.twoCellRefl modality

/-- Transitive composition of 2-cells. -/
@[inline]
def composeTwoCell (twoCellCategory : TwoCellCat)
    {sourceMode targetMode : twoCellCategory.ModeCarrier}
    {firstModality secondModality thirdModality :
      twoCellCategory.Modality sourceMode targetMode}
    (firstTwoCell : twoCellCategory.TwoCell firstModality secondModality)
    (secondTwoCell : twoCellCategory.TwoCell secondModality thirdModality) :
    twoCellCategory.TwoCell firstModality thirdModality :=
  twoCellCategory.twoCellTrans firstTwoCell secondTwoCell

/-- Horizontal composition of 2-cells through modality composition. -/
@[inline]
def whiskerTwoCell (twoCellCategory : TwoCellCat)
    {sourceMode middleMode targetMode : twoCellCategory.ModeCarrier}
    {firstLeftModality firstRightModality :
      twoCellCategory.Modality sourceMode middleMode}
    {secondLeftModality secondRightModality :
      twoCellCategory.Modality middleMode targetMode}
    (firstTwoCell :
      twoCellCategory.TwoCell firstLeftModality firstRightModality)
    (secondTwoCell :
      twoCellCategory.TwoCell secondLeftModality secondRightModality) :
    twoCellCategory.TwoCell
      (twoCellCategory.composeModality firstLeftModality secondLeftModality)
      (twoCellCategory.composeModality firstRightModality secondRightModality) :=
  twoCellCategory.twoCellWhisker firstTwoCell secondTwoCell

/-- Transitivity exposed as a theorem for rewriting and search. -/
theorem twoCell_trans (twoCellCategory : TwoCellCat)
    {sourceMode targetMode : twoCellCategory.ModeCarrier}
    {firstModality secondModality thirdModality :
      twoCellCategory.Modality sourceMode targetMode}
    (firstTwoCell : twoCellCategory.TwoCell firstModality secondModality)
    (secondTwoCell : twoCellCategory.TwoCell secondModality thirdModality) :
    twoCellCategory.TwoCell firstModality thirdModality :=
  twoCellCategory.composeTwoCell firstTwoCell secondTwoCell

/-- Horizontal composition exposed as a theorem for later modal rules. -/
theorem twoCell_whisker (twoCellCategory : TwoCellCat)
    {sourceMode middleMode targetMode : twoCellCategory.ModeCarrier}
    {firstLeftModality firstRightModality :
      twoCellCategory.Modality sourceMode middleMode}
    {secondLeftModality secondRightModality :
      twoCellCategory.Modality middleMode targetMode}
    (firstTwoCell :
      twoCellCategory.TwoCell firstLeftModality firstRightModality)
    (secondTwoCell :
      twoCellCategory.TwoCell secondLeftModality secondRightModality) :
    twoCellCategory.TwoCell
      (twoCellCategory.composeModality firstLeftModality secondLeftModality)
      (twoCellCategory.composeModality firstRightModality secondRightModality) :=
  twoCellCategory.whiskerTwoCell firstTwoCell secondTwoCell

end TwoCellCat

namespace SmokeTestTwoCellCat

/-- The terminal 2-cell category: one mode, one modality, one 2-cell. -/
def unitTwoCellCat : TwoCellCat where
  ModeCarrier := Unit
  Modality := fun _ _ => Unit
  idMod := fun _ => ()
  compMod := fun _ _ => ()
  idLeft := fun _ => rfl
  idRight := fun _ => rfl
  compAssoc := fun _ _ _ => rfl
  TwoCell := fun _ _ => True
  twoCellRefl := fun _ => True.intro
  twoCellTrans := fun _ _ => True.intro
  twoCellWhisker := fun _ _ => True.intro

/-- Reflexive 2-cell smoke. -/
example (modality : unitTwoCellCat.Modality () ()) :
    unitTwoCellCat.TwoCell modality modality :=
  unitTwoCellCat.identityTwoCell modality

/-- Transitive 2-cell smoke. -/
example
    {firstModality secondModality thirdModality :
      unitTwoCellCat.Modality () ()}
    (firstTwoCell : unitTwoCellCat.TwoCell firstModality secondModality)
    (secondTwoCell : unitTwoCellCat.TwoCell secondModality thirdModality) :
    unitTwoCellCat.TwoCell firstModality thirdModality :=
  unitTwoCellCat.composeTwoCell firstTwoCell secondTwoCell

/-- Horizontal 2-cell composition smoke. -/
example
    {firstLeftModality firstRightModality secondLeftModality secondRightModality :
      unitTwoCellCat.Modality () ()}
    (firstTwoCell :
      unitTwoCellCat.TwoCell firstLeftModality firstRightModality)
    (secondTwoCell :
      unitTwoCellCat.TwoCell secondLeftModality secondRightModality) :
    unitTwoCellCat.TwoCell
      (unitTwoCellCat.composeModality firstLeftModality secondLeftModality)
      (unitTwoCellCat.composeModality firstRightModality secondRightModality) :=
  unitTwoCellCat.whiskerTwoCell firstTwoCell secondTwoCell

end SmokeTestTwoCellCat

end LeanFX.Mode
