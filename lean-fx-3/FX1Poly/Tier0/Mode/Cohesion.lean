import FX1Poly.Tier0.Mode.Mode

/-! # mode-13 — Lawvere cohesion: the adjoint quadruple + modal fracture + differential cohesion

A **cohesive** structure (Lawvere, axiomatic cohesion; Schreiber–Shulman cohesive HoTT) is an ADJOINT QUADRUPLE
`Π₀ ⊣ Disc ⊣ Γ ⊣ Codisc` between a category of cohesive types and a base of discrete types, from which three
idempotent **cohesive modalities** are derived — shape `ʃ = Disc ∘ Π₀`, flat `♭ = Disc ∘ Γ`, sharp
`♯ = Codisc ∘ Γ` — forming the adjoint string `ʃ ⊣ ♭ ⊣ ♯`.  **Differential** cohesion adds a further infinitesimal
adjoint triple (reduction `ℜ` ⊣ infinitesimal-shape `ℑ` ⊣ coreduction).  `mode-13` ships the quadruple, the
derived modalities, and the differential extension, with the deep theorems (the modal fracture, a non-degenerate
cohesive topos) deferred.

## What this file ships (each piece zero-axiom)

  * **`HomAdjunction`** — a hom-set adjunction `L ⊣ R` (`transpose`/`untranspose` mutually inverse) with the
    derived faithfulness AND surjectivity (so the transposition is a full BIJECTION).
  * **`CohesiveQuadruple`** — the adjoint quadruple as three `HomAdjunction`s (`Π₀⊣Disc`, `Disc⊣Γ`, `Γ⊣Codisc`)
    sharing their middle functors (the genuine adjoint STRING, not three unrelated adjunctions).  Derived: the
    four functors and the three modalities `shapeModality` / `flatModality` / `sharpModality`.
  * **`trivialCohesion`** — the concrete (degenerate) witness (every functor `Id`), with the modality smokes
    (`ʃ = ♭ = ♯ = Id`).
  * **`DifferentialCohesion`** — cohesion + the infinitesimal reduction adjunction `ℜ ⊣ ℑ`, with its two derived
    modalities and the trivial witness.

## What is DEFERRED (markers)

  * the adjoint-modality string `ʃ ⊣ ♭ ⊣ ♯` is shipped FOR THE TRIVIAL cohesion
    (`trivialCohesion_adjointString`); deriving it for a GENERAL quadruple stays deferred
    (`hasCohesiveModalityAdjointString`);
  * the MODAL FRACTURE square / hexagon (reconstructing a type from `ʃ` / `♭` / `♯`) (`hasModalFracture`);
  * a genuine NON-DEGENERATE cohesive topos (the trivial cohesion is degenerate; real cohesion needs e.g.
    simplicial / smooth sets) (`hasCohesiveToposModel`);
  * the connection to the kernel's `gen_shapeModality` / `gen_flatModality` / `gen_sharpModality` /
    `gen_cohesiveAdjunctionUnit` (cross-axis, `fib`) (`hasKernelCohesionConnection`).

The cohesive modalities are the `mode-4` adjoint-string content specialized to Lawvere cohesion.
Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## Hom-set adjunctions -/

/-- A **hom-set adjunction** `L ⊣ R` on `Type` endofunctors — the natural bijection
`(L X → A) ≃ (X → R A)`. -/
structure HomAdjunction where
  /-- The left adjoint. -/
  leftFunctor : Type → Type
  /-- The right adjoint. -/
  rightFunctor : Type → Type
  /-- The forward transposition. -/
  transpose : {X A : Type} → (leftFunctor X → A) → (X → rightFunctor A)
  /-- The backward transposition. -/
  untranspose : {X A : Type} → (X → rightFunctor A) → (leftFunctor X → A)
  /-- The bijection, one direction. -/
  transpose_untranspose : {X A : Type} → (rightMorphism : X → rightFunctor A) →
    transpose (untranspose rightMorphism) = rightMorphism
  /-- The bijection, the other direction. -/
  untranspose_transpose : {X A : Type} → (leftMorphism : leftFunctor X → A) →
    untranspose (transpose leftMorphism) = leftMorphism

/-- The identity hom-adjunction `Id ⊣ Id`. -/
def identityHomAdjunction : HomAdjunction where
  leftFunctor := fun carrier => carrier
  rightFunctor := fun carrier => carrier
  transpose := fun morphism => morphism
  untranspose := fun morphism => morphism
  transpose_untranspose := fun _rightMorphism => rfl
  untranspose_transpose := fun _leftMorphism => rfl

/-- ★ The forward transposition is FAITHFUL — derived from the adjunction iso. -/
theorem HomAdjunction.transpose_injective (adjunction : HomAdjunction) {X A : Type}
    {firstMorphism secondMorphism : adjunction.leftFunctor X → A}
    (transposesEqual : adjunction.transpose firstMorphism = adjunction.transpose secondMorphism) :
    firstMorphism = secondMorphism := by
  rw [← adjunction.untranspose_transpose firstMorphism,
      ← adjunction.untranspose_transpose secondMorphism, transposesEqual]

/-- ★ The forward transposition is SURJECTIVE — every `X → R A` is a transpose.  With injectivity, a full
BIJECTION. -/
theorem HomAdjunction.transpose_surjective (adjunction : HomAdjunction) {X A : Type}
    (rightMorphism : X → adjunction.rightFunctor A) :
    ∃ leftMorphism : adjunction.leftFunctor X → A, adjunction.transpose leftMorphism = rightMorphism :=
  ⟨adjunction.untranspose rightMorphism, adjunction.transpose_untranspose rightMorphism⟩

/-! ## The cohesive adjoint quadruple -/

/-- A **cohesive adjoint quadruple** `Π₀ ⊣ Disc ⊣ Γ ⊣ Codisc` — three hom-adjunctions whose MIDDLE functors
agree (`Disc` is the right adjoint of the first and the left adjoint of the second; `Γ` likewise), making it a
genuine adjoint STRING.  This is the datum of Lawvere cohesion. -/
structure CohesiveQuadruple where
  /-- `Π₀ ⊣ Disc` (the shape/components functor is left adjoint to the discrete inclusion). -/
  shapeDiscAdjunction : HomAdjunction
  /-- `Disc ⊣ Γ` (the discrete inclusion is left adjoint to the global-sections functor). -/
  discPointsAdjunction : HomAdjunction
  /-- `Γ ⊣ Codisc` (global sections is left adjoint to the codiscrete inclusion). -/
  pointsCodiscAdjunction : HomAdjunction
  /-- The `Disc` functor is shared between the first two adjunctions. -/
  discShared : shapeDiscAdjunction.rightFunctor = discPointsAdjunction.leftFunctor
  /-- The `Γ` functor is shared between the last two adjunctions. -/
  pointsShared : discPointsAdjunction.rightFunctor = pointsCodiscAdjunction.leftFunctor

/-- The shape / components functor `Π₀`. -/
def CohesiveQuadruple.shapeFunctor (quadruple : CohesiveQuadruple) : Type → Type :=
  quadruple.shapeDiscAdjunction.leftFunctor

/-- The discrete-inclusion functor `Disc`. -/
def CohesiveQuadruple.discFunctor (quadruple : CohesiveQuadruple) : Type → Type :=
  quadruple.shapeDiscAdjunction.rightFunctor

/-- The global-sections functor `Γ`. -/
def CohesiveQuadruple.pointsFunctor (quadruple : CohesiveQuadruple) : Type → Type :=
  quadruple.discPointsAdjunction.rightFunctor

/-- The codiscrete-inclusion functor `Codisc`. -/
def CohesiveQuadruple.codiscFunctor (quadruple : CohesiveQuadruple) : Type → Type :=
  quadruple.pointsCodiscAdjunction.rightFunctor

/-- The **shape modality** `ʃ = Disc ∘ Π₀`. -/
def CohesiveQuadruple.shapeModality (quadruple : CohesiveQuadruple) : Type → Type :=
  fun typeX => quadruple.discFunctor (quadruple.shapeFunctor typeX)

/-- The **flat modality** `♭ = Disc ∘ Γ`. -/
def CohesiveQuadruple.flatModality (quadruple : CohesiveQuadruple) : Type → Type :=
  fun typeX => quadruple.discFunctor (quadruple.pointsFunctor typeX)

/-- The **sharp modality** `♯ = Codisc ∘ Γ`. -/
def CohesiveQuadruple.sharpModality (quadruple : CohesiveQuadruple) : Type → Type :=
  fun typeX => quadruple.codiscFunctor (quadruple.pointsFunctor typeX)

/-- The **trivial (degenerate) cohesion** — every functor is the identity. -/
def trivialCohesion : CohesiveQuadruple where
  shapeDiscAdjunction := identityHomAdjunction
  discPointsAdjunction := identityHomAdjunction
  pointsCodiscAdjunction := identityHomAdjunction
  discShared := rfl
  pointsShared := rfl

/-- Smoke: the trivial cohesion's shape modality is the identity. -/
theorem trivialCohesion_shapeModality (typeX : Type) :
    trivialCohesion.shapeModality typeX = typeX := rfl

/-- Smoke: the trivial cohesion's flat modality is the identity. -/
theorem trivialCohesion_flatModality (typeX : Type) :
    trivialCohesion.flatModality typeX = typeX := rfl

/-- Smoke: the trivial cohesion's sharp modality is the identity. -/
theorem trivialCohesion_sharpModality (typeX : Type) :
    trivialCohesion.sharpModality typeX = typeX := rfl

/-! ## Differential cohesion -/

/-- **Differential cohesion** — a cohesive quadruple plus the infinitesimal REDUCTION adjunction `ℜ ⊣ ℑ`
(reduction is left adjoint to the infinitesimal shape / de Rham functor).  The infinitesimal counterpart of the
cohesive structure (Schreiber). -/
structure DifferentialCohesion where
  /-- The underlying cohesion. -/
  cohesion : CohesiveQuadruple
  /-- The infinitesimal reduction adjunction `ℜ ⊣ ℑ`. -/
  reductionAdjunction : HomAdjunction

/-- The **reduction modality** `ℜ` (the left adjoint of the infinitesimal adjunction). -/
def DifferentialCohesion.reductionModality (differential : DifferentialCohesion) : Type → Type :=
  differential.reductionAdjunction.leftFunctor

/-- The **infinitesimal-shape modality** `ℑ` (the de Rham / infinitesimal-shape functor). -/
def DifferentialCohesion.infinitesimalShapeModality (differential : DifferentialCohesion) : Type → Type :=
  differential.reductionAdjunction.rightFunctor

/-- The **trivial differential cohesion** — trivial cohesion + the identity infinitesimal adjunction. -/
def trivialDifferentialCohesion : DifferentialCohesion where
  cohesion := trivialCohesion
  reductionAdjunction := identityHomAdjunction

/-- Smoke: the trivial differential cohesion's reduction modality is the identity. -/
theorem trivialDifferentialCohesion_reductionModality (typeX : Type) :
    trivialDifferentialCohesion.reductionModality typeX = typeX := rfl

/-! ## The derived adjoint-modality string `ʃ ⊣ ♭ ⊣ ♯` (for the trivial cohesion)

From the quadruple, the cohesive modalities form an adjoint STRING `ʃ ⊣ ♭ ⊣ ♯`.  Deriving it for a GENERAL
quadruple is the fiddly cross-world derivation (deferred); for the TRIVIAL cohesion (all functors `Id`, so all
three modalities `Id`) the string is concrete: the two adjunctions `ʃ ⊣ ♭` and `♭ ⊣ ♯`, each a genuine
`HomAdjunction` whose functors ARE the modalities, composing at the shared `♭`. -/

/-- The `ʃ ⊣ ♭` adjunction for the trivial cohesion — `leftFunctor` is the shape modality, `rightFunctor` the
flat modality (both `Id` here), the transposition the identity bijection. -/
def trivialCohesion_shapeFlatAdjunction : HomAdjunction where
  leftFunctor := trivialCohesion.shapeModality
  rightFunctor := trivialCohesion.flatModality
  transpose := fun morphism => morphism
  untranspose := fun morphism => morphism
  transpose_untranspose := fun _rightMorphism => rfl
  untranspose_transpose := fun _leftMorphism => rfl

/-- The `♭ ⊣ ♯` adjunction for the trivial cohesion — `leftFunctor` is the flat modality, `rightFunctor` the
sharp modality. -/
def trivialCohesion_flatSharpAdjunction : HomAdjunction where
  leftFunctor := trivialCohesion.flatModality
  rightFunctor := trivialCohesion.sharpModality
  transpose := fun morphism => morphism
  untranspose := fun morphism => morphism
  transpose_untranspose := fun _rightMorphism => rfl
  untranspose_transpose := fun _leftMorphism => rfl

/-- The `ʃ ⊣ ♭` adjunction's functors ARE the shape and flat modalities. -/
theorem trivialCohesion_shapeFlatAdjunction_functors :
    trivialCohesion_shapeFlatAdjunction.leftFunctor = trivialCohesion.shapeModality
      ∧ trivialCohesion_shapeFlatAdjunction.rightFunctor = trivialCohesion.flatModality :=
  ⟨rfl, rfl⟩

/-- The `♭ ⊣ ♯` adjunction's functors ARE the flat and sharp modalities. -/
theorem trivialCohesion_flatSharpAdjunction_functors :
    trivialCohesion_flatSharpAdjunction.leftFunctor = trivialCohesion.flatModality
      ∧ trivialCohesion_flatSharpAdjunction.rightFunctor = trivialCohesion.sharpModality :=
  ⟨rfl, rfl⟩

/-- ★ The string COMPOSES: the right adjoint of `ʃ ⊣ ♭` IS the left adjoint of `♭ ⊣ ♯` (the shared `♭`), so the
two adjunctions form the genuine adjoint string `ʃ ⊣ ♭ ⊣ ♯`. -/
theorem trivialCohesion_adjointString :
    trivialCohesion_shapeFlatAdjunction.rightFunctor = trivialCohesion_flatSharpAdjunction.leftFunctor :=
  rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The adjoint-modality STRING `ʃ ⊣ ♭ ⊣ ♯` IS shipped for the trivial cohesion
(`trivialCohesion_shapeFlatAdjunction` / `trivialCohesion_flatSharpAdjunction` tied to the modalities +
`trivialCohesion_adjointString` composing them).  What remains deferred is deriving it for a GENERAL quadruple
(the fiddly cross-world adjunction derivation).  `= false`. -/
def fxMode_hasCohesiveModalityAdjointString : Bool := false

/-- **Honesty marker.**  The MODAL FRACTURE square / hexagon (reconstructing a type from its `ʃ` / `♭` / `♯`
pieces, the cohesive fracture theorem) is deferred.  `= false`. -/
def fxMode_hasModalFracture : Bool := false

/-- **Honesty marker.**  A genuine NON-DEGENERATE cohesive topos (simplicial / smooth sets …) — the trivial
cohesion here is degenerate (all functors `Id`) — is deferred.  `= false`. -/
def fxMode_hasCohesiveToposModel : Bool := false

/-- **Honesty marker.**  The connection to the kernel's cohesive formers (`gen_shapeModality` /
`gen_flatModality` / `gen_sharpModality` / `gen_cohesiveAdjunctionUnit`) is cross-axis (`fib`), deferred.
`= false`. -/
def fxMode_hasKernelCohesionConnection : Bool := false

end FX1Poly.Tier0
