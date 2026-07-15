import FX1Poly.Axis.Mode.CohesionAdjointString
import FX1Poly.Axis.Mode.ModalFracture

/-! # mode-13 (cohesion flat modality `♭`) — the comonadic / crisp discrete modality

The cohesion adjoint string `ʃ ⊣ ♭ ⊣ ♯` (`CohesionAdjointString`) ships the flat modality `♭ = Disc ∘ Γ` as an
endofunctor with its counit `ε^♭ : ♭X → X` (the untranspose of the identity on `Γ X`).  `♭` is the COMONADIC
(coreflective / crisp) cohesion modality: it is the COMONAD of the geometric-morphism edge `Disc ⊣ Γ` (a
`Disc∘Γ = L∘R` composite) and the CENTRAL modality of the string — right adjoint to `ʃ`, left adjoint to `♯`.
This file reads the comonadic structure off the shipped adjunctions, CAST-FREE, with the genuine universal
property (β/η + the crisp/Fitch-style row `♭ ⊣ ♯`) shipped GENERALLY and the full comonad (comultiplication +
idempotency) shipped CONCRETELY at the trivial witness, the general multiplication honestly walled.

## What this file ships (each piece zero-axiom)

  * **`flatCounit_eq` / `flatCounit_transpose`** — the counit is the untranspose of the identity on `Γ X`
    (definitional), and its β/η universal-property law `transpose (ε^♭) = id` holds CAST-FREE via the `Disc ⊣ Γ`
    round-trip.  GENERAL over any quadruple.
  * **`flatCrispRow`** — the crisp / Fitch-style adjoint row `Hom(♭X, A) ≃ Hom(X, ♯A)` (the `♭ ⊣ ♯`
    adjunction, shipped), re-exported as the flat modality's defining row: a crisp map out of a flat type into
    `A` is the same datum as an ordinary map into `♯A`.  **`flatCrispCorecursion`** untransposes along it, with
    its β/η (`flatCrispCorecursion_transpose`) and UNIQUENESS (`flatCrispMap_unique`, the transposition is
    faithful) proved cast-free.  GENERAL.
  * **`trivialCohesionFlatComodality`** — the trivial cohesion's `♭` as a genuine `CoreflectiveSubuniverse`
    (idempotent comonad, the `mode-20` interface) with the counit the shipped `flatCounit`; the counit tie
    (`_counit`) and the idempotency smoke (`♭♭ = ♭`) by `rfl`.

## What is DEFERRED (markers)

  * the GENERAL flat COMONAD's comultiplication `δ : ♭X → ♭♭X` (= `Disc(η^{Disc⊣Γ})`) needs a functorial `map` on
    `Disc`/`Γ`, and natural IDEMPOTENCY `♭♭ ≅ ♭` additionally needs `Disc` FULLY FAITHFUL — bare hom-set
    transposition carries neither, so the full comonad ships for the concrete (trivial) witness only
    (`fxMode_hasCohesionFlatComonadGeneral`; this is the flat instance of the string's
    `fxMode_hasCohesionModalityIdempotent` wall).
  * the COMPUTATION of `♭`-composites (deciding the adjoint-string normal form) is gated on the keystone's
    decidable mode 2-cell equality (`fxMode_hasModeRelativeConvDecision`, currently `false`); the string's
    `fxMode_hasCohesionModalityComputation` already records this — not re-derived here.

Zero external dependencies beyond the cohesion adjoint string + the `mode-20` modality interface.  Raw Lean 4 +
Init.
-/

namespace FX1Poly.Axis

/-! ## The flat comonad counit + its β/η -/

/-- The flat counit is the untranspose of the identity on `Γ X` (the counit of `Disc ⊣ Γ` — definitional
restatement of `flatCounit`). -/
theorem CohesionAdjointQuadruple.flatCounit_eq (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    quadruple.flatCounit typeX
      = quadruple.discreteSections.untranspose (fun globalSection => globalSection) := rfl

/-- ★ The flat comonad's β/η law: transposing the counit recovers the identity on `Γ X` (`transpose (ε^♭) = id`).
The genuine universal-property content of the comonad counit, CAST-FREE via the `Disc ⊣ Γ` round-trip
(`transpose_untranspose`).  GENERAL over any quadruple. -/
theorem CohesionAdjointQuadruple.flatCounit_transpose (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    quadruple.discreteSections.transpose (quadruple.flatCounit typeX)
      = (fun globalSection => globalSection) :=
  quadruple.discreteSections.transpose_untranspose (fun globalSection => globalSection)

/-! ## The crisp / Fitch-style row `♭ ⊣ ♯` + crisp corecursion -/

/-- The flat modality's **crisp (Fitch-style) row** `Hom(♭X, A) ≃ Hom(X, ♯A)` — the `♭ ⊣ ♯` adjunction (shipped
as `flatSharpAdjunction`), re-exported as the flat modality's defining adjoint row.  This is the semantic content
that justifies Fitch-style crisp assumptions: a crisp map OUT of a flat type into `A` is the same datum as an
ordinary map INTO `♯A`. -/
def CohesionAdjointQuadruple.flatCrispRow (quadruple : CohesionAdjointQuadruple) :
    HomAdjunctionBetween quadruple.flatModality quadruple.sharpModality :=
  quadruple.flatSharpAdjunction

/-- **Crisp corecursion** — a map `X → ♯A` extends to a (crisp) map `♭X → A` by untransposing the crisp row. -/
def CohesionAdjointQuadruple.flatCrispCorecursion (quadruple : CohesionAdjointQuadruple) {typeX typeA : Type}
    (sharpMap : typeX → quadruple.sharpModality typeA) : quadruple.flatModality typeX → typeA :=
  quadruple.flatCrispRow.untranspose sharpMap

/-- ★ Crisp corecursion's β/η: it is INVERSE to transposing along the crisp row, so the crisp map `♭X → A` is
recovered (uniquely) from its transpose `X → ♯A`.  CAST-FREE via the `♭ ⊣ ♯` round-trip. -/
theorem CohesionAdjointQuadruple.flatCrispCorecursion_transpose (quadruple : CohesionAdjointQuadruple)
    {typeX typeA : Type} (sharpMap : typeX → quadruple.sharpModality typeA) :
    quadruple.flatCrispRow.transpose (quadruple.flatCrispCorecursion sharpMap) = sharpMap :=
  quadruple.flatCrispRow.transpose_untranspose sharpMap

/-- ★ Uniqueness of the crisp map out of `♭X`: two crisp maps with equal transposes are equal (the `♭ ⊣ ♯`
transposition is faithful). -/
theorem CohesionAdjointQuadruple.flatCrispMap_unique (quadruple : CohesionAdjointQuadruple)
    {typeX typeA : Type} {firstMap secondMap : quadruple.flatModality typeX → typeA}
    (transposesEqual :
      quadruple.flatCrispRow.transpose firstMap = quadruple.flatCrispRow.transpose secondMap) :
    firstMap = secondMap :=
  quadruple.flatCrispRow.transpose_injective transposesEqual

/-! ## The concrete flat comonad (the trivial witness) -/

/-- ★ The trivial cohesion's flat modality as a genuine **coreflective subuniverse** (idempotent comonad) — the
established `CoreflectiveSubuniverse` interface (`mode-20` `ModalFracture`), with the counit the shipped
`flatCounit`.  The full comonad (comultiplication + idempotency) is concrete here (all functors `Id`); the
GENERAL comonad needs a functorial `map` on `Disc`/`Γ` + `Disc` fully faithful (walled below). -/
def trivialCohesionFlatComodality : CoreflectiveSubuniverse where
  Colocalize := trivialCohesionQuadruple.flatModality
  comap := fun morphism colocalized => morphism colocalized
  counit := fun {typeA} colocalized => trivialCohesionQuadruple.flatCounit typeA colocalized
  counit_natural := fun _morphism _colocalized => rfl

/-- The concrete flat comodality's counit IS the shipped flat counit (the tie to the adjoint-string presentation,
by `rfl`). -/
theorem trivialCohesionFlatComodality_counit (typeX : Type)
    (element : trivialCohesionQuadruple.flatModality typeX) :
    trivialCohesionFlatComodality.counit element = trivialCohesionQuadruple.flatCounit typeX element := rfl

/-- Smoke: the concrete flat comodality is idempotent `♭♭ = ♭` (here both `= Id`). -/
theorem trivialCohesionFlatComodality_idempotent (typeX : Type) :
    trivialCohesionFlatComodality.Colocalize (trivialCohesionFlatComodality.Colocalize typeX)
      = trivialCohesionFlatComodality.Colocalize typeX := rfl

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the cohesion FLAT modality `♭ = Disc ∘ Γ` ships.**  The comonadic discrete modality as
an endofunctor with its counit `ε^♭` (`flatCounit`) and the β/η universal-property law `transpose (ε^♭) = id`
(`flatCounit_transpose`), the crisp / Fitch-style row `♭ ⊣ ♯` (`flatCrispRow`) with crisp corecursion + its β/η +
faithfulness (`flatCrispCorecursion` / `_transpose` / `flatCrispMap_unique`), and the concrete idempotent comonad
witness tying the counit to the `mode-20` `CoreflectiveSubuniverse` interface — all CAST-FREE from the shipped
`Disc ⊣ Γ` / `♭ ⊣ ♯` transpositions.  `= true`. -/
def fxMode_hasCohesionFlatModality : Bool := true

/-- **Honesty marker.**  The GENERAL flat COMONAD beyond the copointed core — the comultiplication
`δ : ♭X → ♭♭X` (= `Disc(η^{Disc⊣Γ})`, needs a functorial `map` on `Disc`/`Γ`) and natural IDEMPOTENCY `♭♭ ≅ ♭`
(additionally needs `Disc` FULLY FAITHFUL) — is shipped for the concrete (trivial) witness only
(`trivialCohesionFlatComodality`); bare hom-set transposition carries neither `map` nor full-faithfulness.  This
is the flat instance of the string's `fxMode_hasCohesionModalityIdempotent` wall.  `= false`. -/
def fxMode_hasCohesionFlatComonadGeneral : Bool := false

end FX1Poly.Axis
