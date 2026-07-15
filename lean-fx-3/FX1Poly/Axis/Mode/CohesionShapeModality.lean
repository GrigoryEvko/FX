import FX1Poly.Axis.Mode.CohesionAdjointString
import FX1Poly.Axis.Mode.ModalFracture

/-! # mode-13 (cohesion shape modality `ʃ`) — the reflective / positive shape modality

The cohesion adjoint string `ʃ ⊣ ♭ ⊣ ♯` (`CohesionAdjointString`) ships the shape modality `ʃ = Disc ∘ Π₀` as an
endofunctor with its unit `η^ʃ : X → ʃX` (the transpose of the identity on `Π₀ X`).  `ʃ` is the REFLECTIVE
(POSITIVE) cohesion modality: it is the MONAD of the locally-connected adjunction `Π₀ ⊣ Disc` (a `Disc∘Π₀ = R∘L`
composite, with `Π₀` the pieces / connected-components functor INTERNALIZED as a positive modality) and the
LEFTMOST modality of the string — the left adjoint of `♭`.  Being LEFT adjoint, `ʃ` is POSITIVE: it has a
mapping-OUT universal property (every type maps into its shape, and maps out of `ʃX` are determined by maps out
of `X` into `♭`-types).  This file reads that structure off the shipped adjunctions, CAST-FREE, with the genuine
universal property (β/η + the reflective row `ʃ ⊣ ♭`) shipped GENERALLY and the full reflective monad
(multiplication + idempotency) shipped CONCRETELY at the trivial witness, the general multiplication walled.

## What this file ships (each piece zero-axiom)

  * **`shapeUnit_eq` / `shapeUnit_untranspose`** — the unit is the transpose of the identity on `Π₀ X`
    (definitional), and its β/η universal-property law `untranspose (η^ʃ) = id` holds CAST-FREE via the
    `Π₀ ⊣ Disc` round-trip.  GENERAL over any quadruple.
  * **`shapeRecursion`** — the POSITIVE / reflective mapping-OUT principle `Hom(X, ♭A) → Hom(ʃX, A)` (the
    `ʃ ⊣ ♭` untranspose): a map out of `X` into a `♭`-type extends to a map out of the shape `ʃX`.  Its β/η
    (`shapeRecursion_transpose`) and UNIQUENESS (`shapeMap_unique`, the transposition is faithful) are proved
    cast-free.  GENERAL — this is `Π₀` internalized as a positive modality.
  * **`trivialCohesionShapeModality`** — the trivial cohesion's `ʃ` as a genuine `Modality` (idempotent reflective
    monad, the `mode-20` interface) with the unit the shipped `shapeUnit`; the unit tie (`_unit`) and the
    idempotency smoke (`ʃʃ = ʃ`) by `rfl`.

## What is DEFERRED (markers)

  * the GENERAL shape MONAD's multiplication `μ^ʃ : ʃʃX → ʃX` (= `Disc(ε^{Π₀⊣Disc})`) needs a functorial `map` on
    `Disc`/`Π₀`, and natural REFLECTIVE IDEMPOTENCY `ʃʃ ≅ ʃ` additionally needs `Disc` FULLY FAITHFUL — bare
    hom-set transposition carries neither, so the full reflective monad ships for the concrete (trivial) witness
    only (`fxMode_hasCohesionShapeMonadGeneral`; the shape instance of the string's
    `fxMode_hasCohesionModalityIdempotent` wall).
  * the COMPUTATION of `ʃ`-composites is gated on the keystone's decidable mode 2-cell equality
    (`fxMode_hasModeRelativeConvDecision`, currently `false`); the string's
    `fxMode_hasCohesionModalityComputation` already records this — not re-derived here.

Zero external dependencies beyond the cohesion adjoint string + the `mode-20` modality interface.  Raw Lean 4 +
Init.
-/

namespace FX1Poly.Axis

/-! ## The shape monad unit + its β/η -/

/-- The shape unit is the transpose of the identity on `Π₀ X` (the unit of `Π₀ ⊣ Disc` — definitional restatement
of `shapeUnit`). -/
theorem CohesionAdjointQuadruple.shapeUnit_eq (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    quadruple.shapeUnit typeX
      = quadruple.piecesDiscrete.transpose (fun piece => piece) := rfl

/-- ★ The shape monad's β/η law: untransposing the unit recovers the identity on `Π₀ X` (`untranspose (η^ʃ) = id`).
The genuine universal-property content of the reflector unit, CAST-FREE via the `Π₀ ⊣ Disc` round-trip
(`untranspose_transpose`).  GENERAL over any quadruple. -/
theorem CohesionAdjointQuadruple.shapeUnit_untranspose (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    quadruple.piecesDiscrete.untranspose (quadruple.shapeUnit typeX)
      = (fun piece => piece) :=
  quadruple.piecesDiscrete.untranspose_transpose (fun piece => piece)

/-! ## The reflective row `ʃ ⊣ ♭`: `Π₀` as a positive modality -/

/-- **Shape recursion** — the POSITIVE / reflective mapping-OUT principle `Hom(X, ♭A) → Hom(ʃX, A)` (the
`ʃ ⊣ ♭` untranspose): a map out of `X` into a `♭`-type `♭A` extends to a map out of the shape `ʃX` into `A`.
This is `Π₀` internalized as a positive modality — the reflector's recursion principle. -/
def CohesionAdjointQuadruple.shapeRecursion (quadruple : CohesionAdjointQuadruple) {typeX typeA : Type}
    (flatMap : typeX → quadruple.flatModality typeA) : quadruple.shapeModality typeX → typeA :=
  quadruple.shapeFlatAdjunction.untranspose flatMap

/-- ★ Shape recursion's β/η: it is INVERSE to transposing along the reflective row, so the extension `ʃX → A` is
recovered from its transpose `X → ♭A`.  CAST-FREE via the `ʃ ⊣ ♭` round-trip. -/
theorem CohesionAdjointQuadruple.shapeRecursion_transpose (quadruple : CohesionAdjointQuadruple)
    {typeX typeA : Type} (flatMap : typeX → quadruple.flatModality typeA) :
    quadruple.shapeFlatAdjunction.transpose (quadruple.shapeRecursion flatMap) = flatMap :=
  quadruple.shapeFlatAdjunction.transpose_untranspose flatMap

/-- ★ Uniqueness of the map out of `ʃX`: two maps with equal transposes are equal (the `ʃ ⊣ ♭` transposition is
faithful — the reflective universal property). -/
theorem CohesionAdjointQuadruple.shapeMap_unique (quadruple : CohesionAdjointQuadruple)
    {typeX typeA : Type} {firstMap secondMap : quadruple.shapeModality typeX → typeA}
    (transposesEqual :
      quadruple.shapeFlatAdjunction.transpose firstMap = quadruple.shapeFlatAdjunction.transpose secondMap) :
    firstMap = secondMap :=
  quadruple.shapeFlatAdjunction.transpose_injective transposesEqual

/-! ## The concrete shape monad (the trivial witness) -/

/-- ★ The trivial cohesion's shape modality as a genuine **modality** (idempotent reflective monad) — the
established `Modality` interface (`mode-20` `ModalFracture`), with the unit the shipped `shapeUnit`.  The full
reflective monad (multiplication + idempotency) is concrete here (all functors `Id`); the GENERAL monad needs a
functorial `map` on `Disc`/`Π₀` + `Disc` fully faithful (walled below). -/
def trivialCohesionShapeModality : Modality where
  Apply := trivialCohesionQuadruple.shapeModality
  map := fun morphism applied => morphism applied
  unit := fun {typeA} point => trivialCohesionQuadruple.shapeUnit typeA point
  mult := fun nested => nested
  map_id := fun _localized => rfl
  unit_natural := fun _morphism _point => rfl
  mult_unit := fun _localized => rfl
  mult_map_unit := fun _localized => rfl
  idempotent := fun _nested => rfl

/-- The concrete shape modality's unit IS the shipped shape unit (the tie to the adjoint-string presentation, by
`rfl`). -/
theorem trivialCohesionShapeModality_unit (typeX : Type) (point : typeX) :
    trivialCohesionShapeModality.unit point = trivialCohesionQuadruple.shapeUnit typeX point := rfl

/-- Smoke: the concrete shape modality is idempotent `ʃʃ = ʃ` (here both `= Id`). -/
theorem trivialCohesionShapeModality_idempotent (typeX : Type) :
    trivialCohesionShapeModality.Apply (trivialCohesionShapeModality.Apply typeX)
      = trivialCohesionShapeModality.Apply typeX := rfl

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the cohesion SHAPE modality `ʃ = Disc ∘ Π₀` ships.**  The reflective positive modality as
an endofunctor with its unit `η^ʃ` (`shapeUnit`) and the β/η universal-property law `untranspose (η^ʃ) = id`
(`shapeUnit_untranspose`), `Π₀` internalized as a positive modality via the reflective mapping-OUT principle
`ʃ ⊣ ♭` with shape recursion + its β/η + faithfulness (`shapeRecursion` / `_transpose` / `shapeMap_unique`), and
the concrete idempotent reflective-monad witness tying the unit to the `mode-20` `Modality` interface — all
CAST-FREE from the shipped `Π₀ ⊣ Disc` / `ʃ ⊣ ♭` transpositions.  `= true`. -/
def fxMode_hasCohesionShapeModality : Bool := true

/-- **Honesty marker.**  The GENERAL shape MONAD beyond the pointed core — the multiplication `μ^ʃ : ʃʃX → ʃX`
(= `Disc(ε^{Π₀⊣Disc})`, needs a functorial `map` on `Disc`/`Π₀`) and natural REFLECTIVE IDEMPOTENCY `ʃʃ ≅ ʃ`
(additionally needs `Disc` FULLY FAITHFUL) — is shipped for the concrete (trivial) witness only
(`trivialCohesionShapeModality`); bare hom-set transposition carries neither.  This is the shape instance of the
string's `fxMode_hasCohesionModalityIdempotent` wall.  `= false`. -/
def fxMode_hasCohesionShapeMonadGeneral : Bool := false

end FX1Poly.Axis
