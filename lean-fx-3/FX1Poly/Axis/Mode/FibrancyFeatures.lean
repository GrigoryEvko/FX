import FX1Poly.Axis.Mode.AdjointModeSignature

/-! # FibrancyFeatures — the φ-column of the grade↔mode spectrum, read at higher resolution

The **φ (Geometric) coordinate** of the `GradedSpectrum` (see `Axis/Mode/GradedSpectrum.lean`).
This file gives the finer READING of the ONE shipped fibrancy mode property (`Axis/Mode/FibrancyMode`,
`FibrancyKind` / the MATT predicate classes) demanded by `grade-mode-spectrum.md` §7.2: fibrancy stays a
single mode property; the spectrum reads it at higher resolution, it does NOT replace it.

## What φ classifies (grade-mode-spectrum.md §5, the R4 fibrancy column)

φ at rung R4 is the universal higher-cell question — "what structure do the ≥1-cells of an ω-category
carry?" — with FOUR answers running identically down all four axes (term / type / context / mode):

| φ-value        | character                                    | cube point ⟨inv, dir, rel⟩ |
|----------------|----------------------------------------------|-----------------------------|
| **strict**     | syntactic / UIP / exotype / strict 2-cat     | ⟨F, F, F⟩ (bottom)          |
| **groupoidal** | Conv / Path (univalence) / modal equivalence | ⟨T, F, F⟩                   |
| **directed**   | Step / Hom (directed) / adjoint string       | ⟨F, T, F⟩                   |
| **relational** | reducibility / Bridge (param.) / profunctor  | ⟨F, F, T⟩                   |
| **omega**      | all three characters at once (the ω-mode)    | ⟨T, T, T⟩ (top)             |

The cube's three bits — `hasInvertibility` (groupoidal character), `hasDirection` (directed character),
`hasRelationality` (relational character) — are three independent Booleans, so the FOUR named poles are
NOT a chain: `groupoidal` and `directed` are INCOMPARABLE atoms above `strict`.  That incomparability is
the whole point — the discrete `FibrancyKind` / `AdjointClass` classifiers are the CORNERS; the cube
INTERIOR (e.g. `directedRelational = ⟨F,T,T⟩`) is strictly richer, naming modalities no single shipped
tag can (`featuresOfAdjointClass_ne_directedRelational`).

## What ships (each piece zero-axiom, ASCII-only, propext-free)

  * **`FibrancyFeatures`** — the 3-Bool cube, the finer reading of `FibrancyMode`.
  * the pointwise Bool-implication order `le` (a genuine partial order: `le_refl` / `le_trans` /
    `le_antisymm`) with `join` (`||`) / `meet` (`&&`).
  * the five named poles + the interior point `directedRelational`.
  * **`featuresOfFibrancyKind`** (2LTT f/e ↦ groupoidal/strict — the §5 "strict-vs-groupoidal shadow")
    and **`featuresOfAdjointClass`** (the §5 MODE row: tangible/sharp/sinister/transparent ↦
    strict/groupoidal/directed/relational), the TOTAL maps FROM the shipped classifiers INTO the cube —
    nothing replaced, the poles definitionally recovered by `rfl`.
  * **`featuresOfAdjointClass_ne_directedRelational`** — the falsifiable payoff: no shipped `AdjointClass`
    tag names the cube interior, so the finer reading is genuinely finer.

This file imports only its `Axis/Mode` siblings (`AdjointModeSignature`, transitively `FibrancyMode`);
the mode carrier (`Polygraph/Computad`) is untouched.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Axis

/-! ## The φ cube -/

/-- The **fibrancy features cube** — the φ (Geometric) coordinate of the grade↔mode spectrum
(`grade-mode-spectrum.md` §5), the finer reading of the ONE shipped fibrancy mode property
(`FibrancyMode`).  Three independent Boolean characters an ω-category's higher cells may carry:
`hasInvertibility` (groupoidal — Conv / Path / univalence), `hasDirection` (directed — Step / Hom /
adjoint string), `hasRelationality` (relational — reducibility / Bridge / profunctor).  A FLAT record
(not `Character → Bool`) so the antisymmetry of its order needs no `funext` — zero-axiom by construction. -/
structure FibrancyFeatures where
  /-- Groupoidal character — the higher cells are invertible (Conv / Path / univalence). -/
  hasInvertibility : Bool
  /-- Directed character — the higher cells carry a direction (Step / Hom / adjoint string). -/
  hasDirection : Bool
  /-- Relational character — the higher cells are relations (reducibility / Bridge / profunctor). -/
  hasRelationality : Bool
  deriving DecidableEq

/-! ## The named poles and the interior point -/

/-- **Strict** — ⟨F,F,F⟩, the bottom corner: syntactic / UIP / exotype / strict 2-category. -/
def FibrancyFeatures.strict : FibrancyFeatures := ⟨false, false, false⟩

/-- **Groupoidal** — ⟨T,F,F⟩: Conv / Path (univalence) / modal equivalence. -/
def FibrancyFeatures.groupoidal : FibrancyFeatures := ⟨true, false, false⟩

/-- **Directed** — ⟨F,T,F⟩: Step / Hom (directed) / adjoint string. -/
def FibrancyFeatures.directed : FibrancyFeatures := ⟨false, true, false⟩

/-- **Relational** — ⟨F,F,T⟩: reducibility / Bridge (parametricity) / profunctor. -/
def FibrancyFeatures.relational : FibrancyFeatures := ⟨false, false, true⟩

/-- **Omega** — ⟨T,T,T⟩, the top corner: all three characters at once (the ω-mode). -/
def FibrancyFeatures.omega : FibrancyFeatures := ⟨true, true, true⟩

/-- ★ **DirectedRelational** — ⟨F,T,T⟩, a genuine cube INTERIOR point (`directed ⊔ relational`): a
modality that is a left adjoint AND admits a relational reading but is NOT invertible.  The witness that
the cube interior is strictly richer than the four discrete corners
(`featuresOfAdjointClass_ne_directedRelational`). -/
def FibrancyFeatures.directedRelational : FibrancyFeatures := ⟨false, true, true⟩

/-! ## The pointwise order -/

/-- The **φ order** — pointwise Bool-implication: `lower ≤ upper` iff every character `lower` carries is
also carried by `upper` (`strict` bottom, `omega` top).  The four pure poles are incomparable atoms
(neither `groupoidal ≤ directed` nor conversely). -/
def FibrancyFeatures.le (lower upper : FibrancyFeatures) : Bool :=
  (!lower.hasInvertibility || upper.hasInvertibility)
    && (!lower.hasDirection || upper.hasDirection)
    && (!lower.hasRelationality || upper.hasRelationality)

/-- The **φ join** — pointwise `||` (accumulate characters).  The least upper bound of the cube order. -/
def FibrancyFeatures.join (first second : FibrancyFeatures) : FibrancyFeatures :=
  ⟨first.hasInvertibility || second.hasInvertibility,
   first.hasDirection || second.hasDirection,
   first.hasRelationality || second.hasRelationality⟩

/-- The **φ meet** — pointwise `&&` (common characters).  The greatest lower bound of the cube order. -/
def FibrancyFeatures.meet (first second : FibrancyFeatures) : FibrancyFeatures :=
  ⟨first.hasInvertibility && second.hasInvertibility,
   first.hasDirection && second.hasDirection,
   first.hasRelationality && second.hasRelationality⟩

/-- `directedRelational` is exactly `directed ⊔ relational` — the interior point IS the accumulation of
two pure characters (`rfl`). -/
theorem FibrancyFeatures.directedRelational_eq_join :
    FibrancyFeatures.directed.join FibrancyFeatures.relational = FibrancyFeatures.directedRelational := rfl

/-- Reflexivity — `!x || x` is a Boolean tautology on each character. -/
theorem FibrancyFeatures.le_refl (features : FibrancyFeatures) : features.le features = true := by
  obtain ⟨hasInv, hasDir, hasRel⟩ := features
  cases hasInv <;> cases hasDir <;> cases hasRel <;> rfl

/-- Transitivity — pointwise Boolean-implication chains.  Impossible cases have a `false = true`
premise, refuted by `Bool.noConfusion`. -/
theorem FibrancyFeatures.le_trans {lower middle upper : FibrancyFeatures}
    (lowerToMiddle : lower.le middle = true) (middleToUpper : middle.le upper = true) :
    lower.le upper = true := by
  obtain ⟨lowInv, lowDir, lowRel⟩ := lower
  obtain ⟨midInv, midDir, midRel⟩ := middle
  obtain ⟨upInv, upDir, upRel⟩ := upper
  cases lowInv <;> cases lowDir <;> cases lowRel <;>
    cases midInv <;> cases midDir <;> cases midRel <;>
    cases upInv <;> cases upDir <;> cases upRel <;>
    first
      | rfl
      | exact Bool.noConfusion lowerToMiddle
      | exact Bool.noConfusion middleToUpper

/-- Antisymmetry — a genuine PARTIAL order on the cube.  Impossible cases refuted by `Bool.noConfusion`. -/
theorem FibrancyFeatures.le_antisymm {first second : FibrancyFeatures}
    (forward : first.le second = true) (backward : second.le first = true) : first = second := by
  obtain ⟨firstInv, firstDir, firstRel⟩ := first
  obtain ⟨secondInv, secondDir, secondRel⟩ := second
  cases firstInv <;> cases firstDir <;> cases firstRel <;>
    cases secondInv <;> cases secondDir <;> cases secondRel <;>
    first
      | rfl
      | exact Bool.noConfusion forward
      | exact Bool.noConfusion backward

/-- `strict` is the bottom of the cube order. -/
theorem FibrancyFeatures.strict_le (features : FibrancyFeatures) :
    FibrancyFeatures.strict.le features = true := by
  obtain ⟨hasInv, hasDir, hasRel⟩ := features
  cases hasInv <;> cases hasDir <;> cases hasRel <;> rfl

/-- `omega` is the top of the cube order. -/
theorem FibrancyFeatures.le_omega (features : FibrancyFeatures) :
    features.le FibrancyFeatures.omega = true := by
  obtain ⟨hasInv, hasDir, hasRel⟩ := features
  cases hasInv <;> cases hasDir <;> cases hasRel <;> rfl

/-! ## Total maps FROM the shipped classifiers (the finer reading, nothing replaced) -/

/-- ★ The **2LTT f/e reading** (`grade-mode-spectrum.md` §5 "2LTT's f/e is the type-axis,
strict-vs-groupoidal shadow"): the fibrant mode reads as `groupoidal` (univalent — invertible higher
cells), the exotype mode as `strict` (UIP — no higher structure).  A total map FROM the shipped
`FibrancyKind` INTO the cube; the poles are recovered by `rfl`. -/
def featuresOfFibrancyKind : FibrancyKind → FibrancyFeatures
  | .fibrant => FibrancyFeatures.groupoidal
  | .exotype => FibrancyFeatures.strict

/-- The fibrant mode reads as groupoidal (`rfl`). -/
theorem featuresOfFibrancyKind_fibrant :
    featuresOfFibrancyKind FibrancyKind.fibrant = FibrancyFeatures.groupoidal := rfl

/-- The exotype mode reads as strict (`rfl`). -/
theorem featuresOfFibrancyKind_exotype :
    featuresOfFibrancyKind FibrancyKind.exotype = FibrancyFeatures.strict := rfl

/-- ★ The **MATT MODE-row reading** (`grade-mode-spectrum.md` §5): the four MATT `AdjointClass` tags read
as the four pure cube corners — `tangible ↦ strict` (the ambient, no distinguishing character),
`sharp ↦ groupoidal`, `sinister ↦ directed` (the left-adjoint / directed character), `transparent ↦
relational` (the modal-function-type / relational character).  A total map FROM the shipped
`AdjointClass` INTO the cube; the poles are recovered by `rfl`.  Documents §5's claim that the φ MODE-row
IS the four AdjointClasses — one map, NO double order. -/
def featuresOfAdjointClass : AdjointClass → FibrancyFeatures
  | .tangible => FibrancyFeatures.strict
  | .sharp => FibrancyFeatures.groupoidal
  | .sinister => FibrancyFeatures.directed
  | .transparent => FibrancyFeatures.relational

/-- `tangible` reads as strict (`rfl`). -/
theorem featuresOfAdjointClass_tangible :
    featuresOfAdjointClass AdjointClass.tangible = FibrancyFeatures.strict := rfl

/-- `sharp` reads as groupoidal (`rfl`). -/
theorem featuresOfAdjointClass_sharp :
    featuresOfAdjointClass AdjointClass.sharp = FibrancyFeatures.groupoidal := rfl

/-- `sinister` reads as directed (`rfl`). -/
theorem featuresOfAdjointClass_sinister :
    featuresOfAdjointClass AdjointClass.sinister = FibrancyFeatures.directed := rfl

/-- `transparent` reads as relational (`rfl`). -/
theorem featuresOfAdjointClass_transparent :
    featuresOfAdjointClass AdjointClass.transparent = FibrancyFeatures.relational := rfl

/-- ★★★ **The interior is strictly richer than the discrete classifier.**  No shipped `AdjointClass` tag
reads as `directedRelational` — the cube INTERIOR names a modality (left-adjoint AND relational, NOT
invertible) that the four discrete MATT tags cannot.  The falsifiable content of "fibrancy read at
higher resolution" (`grade-mode-spectrum.md` §5): the finer reading is genuinely finer. -/
theorem featuresOfAdjointClass_ne_directedRelational (adjointClass : AdjointClass) :
    featuresOfAdjointClass adjointClass ≠ FibrancyFeatures.directedRelational := by
  cases adjointClass <;> decide

/-- The four MATT-class images are exactly the four pure poles — `featuresOfAdjointClass` surjects onto
`{strict, groupoidal, directed, relational}` (documented pole-by-pole above), and its image AVOIDS the
interior `directedRelational` (previous theorem) and the top `omega`. -/
theorem featuresOfAdjointClass_ne_omega (adjointClass : AdjointClass) :
    featuresOfAdjointClass adjointClass ≠ FibrancyFeatures.omega := by
  cases adjointClass <;> decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the φ cube ships.**  The 3-Bool `FibrancyFeatures` cube with its pointwise
partial order (`le_refl` / `le_trans` / `le_antisymm`), `join` / `meet`, the five named poles, and the
interior point `directedRelational`.  `= true`. -/
def fxFibrancyFeatures_hasCube : Bool := true

/-- ★ **Honesty marker — the shipped classifiers embed as the finer reading.**  `featuresOfFibrancyKind`
(2LTT f/e ↦ groupoidal/strict) and `featuresOfAdjointClass` (the MATT MODE row ↦ the four pure corners),
total maps FROM `FibrancyMode`'s `FibrancyKind` / `AdjointModeSignature`'s `AdjointClass` INTO the cube —
nothing replaced, the poles recovered by `rfl`.  `= true`. -/
def fxFibrancyFeatures_hasClassifierReading : Bool := true

/-- ★ **Honesty marker — the interior is strictly richer than the discrete classifier.**  The cube
interior `directedRelational` is named by NO shipped `AdjointClass` tag
(`featuresOfAdjointClass_ne_directedRelational`) — the falsifiable payoff of reading fibrancy at higher
resolution.  `= true`. -/
def fxFibrancyFeatures_hasRicherInterior : Bool := true

end FX1Poly.Axis
