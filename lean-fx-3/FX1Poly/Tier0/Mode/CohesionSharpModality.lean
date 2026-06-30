import FX1Poly.Tier0.Mode.CohesionAdjointString
import FX1Poly.Tier0.Mode.ModalFracture

/-! # mode-13 (cohesion sharp modality `♯`) — the monadic / codiscrete modality

The cohesion adjoint string `ʃ ⊣ ♭ ⊣ ♯` (`CohesionAdjointString`) ships the sharp modality `♯ = coDisc ∘ Γ` as
an endofunctor with its unit `η^♯ : X → ♯X` (the transpose of the identity on `Γ X`).  `♯` is the MONADIC
(reflective / codiscrete) cohesion modality: it is the MONAD of the local adjunction `Γ ⊣ coDisc` (a
`coDisc∘Γ = R∘L` composite) and the RIGHTMOST modality of the string — the right adjoint of `♭`.  This file
reads the monadic structure off the shipped adjunctions, CAST-FREE, with the genuine universal property (β/η +
the crisp row `♭ ⊣ ♯`) shipped GENERALLY and the full monad (multiplication + idempotency) shipped CONCRETELY at
the trivial witness, the general multiplication honestly walled.

## What this file ships (each piece zero-axiom)

  * **`sharpUnit_eq` / `sharpUnit_untranspose`** — the unit is the transpose of the identity on `Γ X`
    (definitional), and its β/η universal-property law `untranspose (η^♯) = id` holds CAST-FREE via the
    `Γ ⊣ coDisc` round-trip.  GENERAL over any quadruple.
  * **`sharpModalize`** — the row direction `Hom(♭X, A) → Hom(X, ♯A)` (the `♭ ⊣ ♯` transpose): a crisp map out of
    `♭X` into `A` becomes a sharp map `X → ♯A`.  Its β/η (`sharpModalize_untranspose`) and UNIQUENESS
    (`sharpModalize_unique`, the transposition is faithful) are proved cast-free.  GENERAL.
  * **`trivialCohesionSharpModality`** — the trivial cohesion's `♯` as a genuine `Modality` (idempotent reflective
    monad, the `mode-20` interface) with the unit the shipped `sharpUnit`; the unit tie (`_unit`) and the
    idempotency smoke (`♯♯ = ♯`) by `rfl`.

## What is DEFERRED (markers)

  * the GENERAL sharp MONAD's multiplication `μ^♯ : ♯♯X → ♯X` (= `coDisc(ε^{Γ⊣coDisc})`) needs a functorial `map`
    on `coDisc`/`Γ`, and natural IDEMPOTENCY `♯♯ ≅ ♯` additionally needs `coDisc` FULLY FAITHFUL — bare hom-set
    transposition carries neither, so the full monad ships for the concrete (trivial) witness only
    (`fxMode_hasCohesionSharpMonadGeneral`; the sharp instance of the string's
    `fxMode_hasCohesionModalityIdempotent` wall).
  * the COMPUTATION of `♯`-composites is gated on the keystone's decidable mode 2-cell equality
    (`fxMode_hasModeRelativeConvDecision`, currently `false`); the string's
    `fxMode_hasCohesionModalityComputation` already records this — not re-derived here.

Zero external dependencies beyond the cohesion adjoint string + the `mode-20` modality interface.  Raw Lean 4 +
Init.
-/

namespace FX1Poly.Tier0

/-! ## The sharp monad unit + its β/η -/

/-- The sharp unit is the transpose of the identity on `Γ X` (the unit of `Γ ⊣ coDisc` — definitional restatement
of `sharpUnit`). -/
theorem CohesionAdjointQuadruple.sharpUnit_eq (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    quadruple.sharpUnit typeX
      = quadruple.sectionsCodiscrete.transpose (fun globalSection => globalSection) := rfl

/-- ★ The sharp monad's β/η law: untransposing the unit recovers the identity on `Γ X` (`untranspose (η^♯) = id`).
The genuine universal-property content of the monad unit, CAST-FREE via the `Γ ⊣ coDisc` round-trip
(`untranspose_transpose`).  GENERAL over any quadruple. -/
theorem CohesionAdjointQuadruple.sharpUnit_untranspose (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    quadruple.sectionsCodiscrete.untranspose (quadruple.sharpUnit typeX)
      = (fun globalSection => globalSection) :=
  quadruple.sectionsCodiscrete.untranspose_transpose (fun globalSection => globalSection)

/-! ## The crisp row `♭ ⊣ ♯` direction into `♯` -/

/-- **Sharp modalization** — the `♭ ⊣ ♯` row direction `Hom(♭X, A) → Hom(X, ♯A)`: a crisp map out of `♭X` into
`A` transposes to a sharp map `X → ♯A`.  This is the universal property exhibiting `♯` as the right adjoint of
`♭` (the codiscrete modality reached from a crisp map). -/
def CohesionAdjointQuadruple.sharpModalize (quadruple : CohesionAdjointQuadruple) {typeX typeA : Type}
    (crispMap : quadruple.flatModality typeX → typeA) : typeX → quadruple.sharpModality typeA :=
  quadruple.flatSharpAdjunction.transpose crispMap

/-- ★ Sharp modalization's β/η: it is INVERSE to untransposing along the row, so the sharp map `X → ♯A` is
recovered from its untranspose `♭X → A`.  CAST-FREE via the `♭ ⊣ ♯` round-trip. -/
theorem CohesionAdjointQuadruple.sharpModalize_untranspose (quadruple : CohesionAdjointQuadruple)
    {typeX typeA : Type} (crispMap : quadruple.flatModality typeX → typeA) :
    quadruple.flatSharpAdjunction.untranspose (quadruple.sharpModalize crispMap) = crispMap :=
  quadruple.flatSharpAdjunction.untranspose_transpose crispMap

/-- ★ Uniqueness of the crisp source of a sharp map: two crisp maps with equal modalizations are equal (the
`♭ ⊣ ♯` transposition is faithful). -/
theorem CohesionAdjointQuadruple.sharpModalize_unique (quadruple : CohesionAdjointQuadruple)
    {typeX typeA : Type} {firstMap secondMap : quadruple.flatModality typeX → typeA}
    (modalizesEqual : quadruple.sharpModalize firstMap = quadruple.sharpModalize secondMap) :
    firstMap = secondMap :=
  quadruple.flatSharpAdjunction.transpose_injective modalizesEqual

/-! ## The concrete sharp monad (the trivial witness) -/

/-- ★ The trivial cohesion's sharp modality as a genuine **modality** (idempotent reflective monad) — the
established `Modality` interface (`mode-20` `ModalFracture`), with the unit the shipped `sharpUnit`.  The full
monad (multiplication + idempotency) is concrete here (all functors `Id`); the GENERAL monad needs a functorial
`map` on `coDisc`/`Γ` + `coDisc` fully faithful (walled below). -/
def trivialCohesionSharpModality : Modality where
  Apply := trivialCohesionQuadruple.sharpModality
  map := fun morphism applied => morphism applied
  unit := fun {typeA} point => trivialCohesionQuadruple.sharpUnit typeA point
  mult := fun nested => nested
  map_id := fun _localized => rfl
  unit_natural := fun _morphism _point => rfl
  mult_unit := fun _localized => rfl
  mult_map_unit := fun _localized => rfl
  idempotent := fun _nested => rfl

/-- The concrete sharp modality's unit IS the shipped sharp unit (the tie to the adjoint-string presentation, by
`rfl`). -/
theorem trivialCohesionSharpModality_unit (typeX : Type) (point : typeX) :
    trivialCohesionSharpModality.unit point = trivialCohesionQuadruple.sharpUnit typeX point := rfl

/-- Smoke: the concrete sharp modality is idempotent `♯♯ = ♯` (here both `= Id`). -/
theorem trivialCohesionSharpModality_idempotent (typeX : Type) :
    trivialCohesionSharpModality.Apply (trivialCohesionSharpModality.Apply typeX)
      = trivialCohesionSharpModality.Apply typeX := rfl

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the cohesion SHARP modality `♯ = coDisc ∘ Γ` ships.**  The monadic codiscrete modality as
an endofunctor with its unit `η^♯` (`sharpUnit`) and the β/η universal-property law `untranspose (η^♯) = id`
(`sharpUnit_untranspose`), the `♭ ⊣ ♯` row direction into `♯` with sharp modalization + its β/η + faithfulness
(`sharpModalize` / `_untranspose` / `sharpModalize_unique`), and the concrete idempotent reflective-monad witness
tying the unit to the `mode-20` `Modality` interface — all CAST-FREE from the shipped `Γ ⊣ coDisc` / `♭ ⊣ ♯`
transpositions.  `= true`. -/
def fxMode_hasCohesionSharpModality : Bool := true

/-- **Honesty marker.**  The GENERAL sharp MONAD beyond the pointed core — the multiplication `μ^♯ : ♯♯X → ♯X`
(= `coDisc(ε^{Γ⊣coDisc})`, needs a functorial `map` on `coDisc`/`Γ`) and natural IDEMPOTENCY `♯♯ ≅ ♯`
(additionally needs `coDisc` FULLY FAITHFUL) — is shipped for the concrete (trivial) witness only
(`trivialCohesionSharpModality`); bare hom-set transposition carries neither.  This is the sharp instance of the
string's `fxMode_hasCohesionModalityIdempotent` wall.  `= false`. -/
def fxMode_hasCohesionSharpMonadGeneral : Bool := false

end FX1Poly.Tier0
