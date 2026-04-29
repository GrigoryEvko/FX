import LeanFX.Mode.TwoCell

/-! # Composable modal edges.

This layer records which adjacent modalities are admitted by the FX
discipline.  The underlying category still has total mathematical
composition; kernel rules that need physically valid mode movement
should use `composeIfComposable`, which requires an explicit
`Composable` proof.
-/

namespace LeanFX.Mode

universe modeUniverse modalityUniverse

/-- A 2-cell category with a decidable predicate selecting the modality
compositions that kernel rules are allowed to form. -/
structure ComposableTwoCellCat
    extends TwoCellCat.{modeUniverse, modalityUniverse} where
  /-- Admissibility of adjacent modality composition. -/
  Composable :
    {sourceMode middleMode targetMode : ModeCarrier} →
      Modality sourceMode middleMode →
      Modality middleMode targetMode →
      Prop
  /-- The admissibility predicate is decidable for finite FX instances. -/
  isComposableDecidable :
    {sourceMode middleMode targetMode : ModeCarrier} →
      (firstModality : Modality sourceMode middleMode) →
      (secondModality : Modality middleMode targetMode) →
        Decidable (Composable firstModality secondModality)

namespace ComposableTwoCellCat

instance (modeCategory : ComposableTwoCellCat)
    {sourceMode middleMode targetMode : modeCategory.ModeCarrier}
    (firstModality : modeCategory.Modality sourceMode middleMode)
    (secondModality : modeCategory.Modality middleMode targetMode) :
    Decidable (modeCategory.Composable firstModality secondModality) :=
  modeCategory.isComposableDecidable firstModality secondModality

/-- Compose two modalities only when the admissibility proof exists. -/
@[inline]
def composeIfComposable (modeCategory : ComposableTwoCellCat)
    {sourceMode middleMode targetMode : modeCategory.ModeCarrier}
    (firstModality : modeCategory.Modality sourceMode middleMode)
    (secondModality : modeCategory.Modality middleMode targetMode)
    (_ : modeCategory.Composable firstModality secondModality) :
    modeCategory.Modality sourceMode targetMode :=
  modeCategory.composeModality firstModality secondModality

/-- A proof-producing checker for admissible composition. -/
def checkComposable (modeCategory : ComposableTwoCellCat)
    {sourceMode middleMode targetMode : modeCategory.ModeCarrier}
    (firstModality : modeCategory.Modality sourceMode middleMode)
    (secondModality : modeCategory.Modality middleMode targetMode) :
    Bool :=
  match modeCategory.isComposableDecidable firstModality secondModality with
  | isTrue _ => true
  | isFalse _ => false

/-- Boolean `true` from the checker exposes an admissibility proof. -/
theorem composable_of_checkComposable_true (modeCategory : ComposableTwoCellCat)
    {sourceMode middleMode targetMode : modeCategory.ModeCarrier}
    (firstModality : modeCategory.Modality sourceMode middleMode)
    (secondModality : modeCategory.Modality middleMode targetMode)
    (checkWasTrue :
      modeCategory.checkComposable firstModality secondModality = true) :
    modeCategory.Composable firstModality secondModality := by
  unfold checkComposable at checkWasTrue
  generalize decisionEq :
    modeCategory.isComposableDecidable firstModality secondModality = decision
      at checkWasTrue
  cases decision with
  | isTrue composableProof => exact composableProof
  | isFalse notComposable =>
      cases checkWasTrue

/-- Boolean `false` from the checker exposes inadmissibility. -/
theorem not_composable_of_checkComposable_false
    (modeCategory : ComposableTwoCellCat)
    {sourceMode middleMode targetMode : modeCategory.ModeCarrier}
    (firstModality : modeCategory.Modality sourceMode middleMode)
    (secondModality : modeCategory.Modality middleMode targetMode)
    (checkWasFalse :
      modeCategory.checkComposable firstModality secondModality = false) :
    ¬ modeCategory.Composable firstModality secondModality := by
  unfold checkComposable at checkWasFalse
  generalize decisionEq :
    modeCategory.isComposableDecidable firstModality secondModality = decision
      at checkWasFalse
  cases decision with
  | isTrue composableProof =>
      cases checkWasFalse
  | isFalse notComposable => exact notComposable

end ComposableTwoCellCat

namespace SmokeTestComposableTwoCellCat

/-- Tiny finite category used to test positive and forbidden
compositions without committing to the real FX modality list.

`true` behaves like identity, `false` behaves like a special effectful
edge, and composing two `false` edges is forbidden.
-/
def boolComposableTwoCellCat : ComposableTwoCellCat where
  ModeCarrier := Unit
  Modality := fun _ _ => Bool
  idMod := fun _ => true
  compMod := fun firstModality secondModality =>
    firstModality && secondModality
  idLeft := by
    intro sourceMode targetMode modality
    cases modality <;> rfl
  idRight := by
    intro sourceMode targetMode modality
    cases modality <;> rfl
  compAssoc := by
    intro firstMode secondMode thirdMode fourthMode
    intro firstModality secondModality thirdModality
    cases firstModality <;> cases secondModality <;> cases thirdModality <;> rfl
  TwoCell := fun firstModality secondModality =>
    firstModality = secondModality
  twoCellRefl := fun _ => rfl
  twoCellTrans := fun firstEquality secondEquality =>
    firstEquality.trans secondEquality
  twoCellWhisker := by
    intro sourceMode middleMode targetMode
    intro firstLeftModality firstRightModality
    intro secondLeftModality secondRightModality
    intro firstEquality secondEquality
    cases firstEquality
    cases secondEquality
    rfl
  Composable := fun firstModality secondModality =>
    ¬ (firstModality = false ∧ secondModality = false)
  isComposableDecidable := fun firstModality secondModality =>
    inferInstanceAs
      (Decidable
        (¬ (firstModality = false ∧ secondModality = false)))

/-- Positive composition can be formed with a proof. -/
example :
    boolComposableTwoCellCat.Modality () () :=
  boolComposableTwoCellCat.composeIfComposable
    (sourceMode := ()) (middleMode := ()) (targetMode := ())
    true false
    (by
      intro bothFalse
      cases bothFalse.left)

/-- The checker accepts an allowed composition. -/
example :
    boolComposableTwoCellCat.checkComposable
      (sourceMode := ()) (middleMode := ()) (targetMode := ())
      true false = true :=
  rfl

/-- The checker rejects the forbidden composition. -/
example :
    boolComposableTwoCellCat.checkComposable
      (sourceMode := ()) (middleMode := ()) (targetMode := ())
      false false = false :=
  rfl

/-- The forbidden composition has no admissibility proof. -/
example :
    ¬ boolComposableTwoCellCat.Composable
      (sourceMode := ()) (middleMode := ()) (targetMode := ())
      false false := by
  intro composableProof
  exact composableProof ⟨rfl, rfl⟩

end SmokeTestComposableTwoCellCat

end LeanFX.Mode
