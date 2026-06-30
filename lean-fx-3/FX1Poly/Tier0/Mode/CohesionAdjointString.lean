import FX1Poly.Tier0.Mode.CohesionGlobalSectionsEdge

/-! # mode-13 (cohesion string) — the `ʃ ⊣ ♭ ⊣ ♯` adjoint string + the cohesion axioms

The cohesion EDGE file shipped the adjoint quadruple `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` with the four functors EXPLICIT,
so the central `Disc` / `Γ` are shared between consecutive adjunctions DEFINITIONALLY.  This file cashes that in:
the derived cohesive modalities `ʃ = Disc∘Π₀`, `♭ = Disc∘Γ`, `♯ = coDisc∘Γ` form the adjoint string
`ʃ ⊣ ♭ ⊣ ♯` — and now, because the shared functors are definitional, the string is built for a GENERAL
quadruple CAST-FREE (composing the two hom-set transpositions; the round-trip laws collapse by the component
adjunctions' laws under `congrArg`).  This is exactly the derivation `mode-13` deferred
(`fxMode_hasCohesiveModalityAdjointString = false`, "the fiddly cross-world adjunction derivation").

It also ships the cohesion AXIOMS as the structural (co)pointed data extractable from the adjunctions without
any functorial `map`: the shape unit `η^ʃ : X → ʃX`, the flat counit `ε^♭ : ♭X → X`, the sharp unit
`η^♯ : X → ♯X` (each a transpose of an identity), and the canonical points comparison `♭X → ʃX` (the modal
shadow of "pieces have points").

## What this file ships (each piece zero-axiom, each GENERAL over any quadruple)

  * **`CohesionAdjointQuadruple.shapeFlatAdjunction`** / **`flatSharpAdjunction`** — the two modal adjunctions
    `ʃ ⊣ ♭` and `♭ ⊣ ♯`, built CAST-FREE by composing the quadruple's hom-set transpositions, with the
    round-trip laws proved in term mode (`congrArg` + the component laws).  GENERAL.
  * **`CohesionModalityAdjointString`** + **`cohesionAdjointString`** — the two adjunctions packaged as the
    string `ʃ ⊣ ♭ ⊣ ♯`, with the shared central `♭` witnessed by `rfl` (`cohesionAdjointString_middle`).
  * **`shapeUnit` / `flatCounit` / `sharpUnit`** — the (co)pointed structure of the three modalities, each a
    transpose / untranspose of an identity (no functorial `map` needed).  GENERAL.
  * **`piecesHavePoints`** — the canonical comparison `♭X → ʃX` (`shapeUnit ∘ flatCounit`), the modal shadow of
    punctual local connectedness.  GENERAL.
  * the trivial-witness smokes (`trivialCohesionQuadruple_*`) confirming every modality / unit / string
    component collapses to the identity in the degenerate case.

## What is DEFERRED (markers)

  * GENERAL natural IDEMPOTENCY of the modalities (`ʃʃ ≅ ʃ` etc.) needs `Disc` / `coDisc` FULLY FAITHFUL plus a
    functorial `map` on the four functors — bare hom-set adjunction omits both; idempotency ships for the
    concrete (trivial) witness only (`fxMode_hasCohesionModalityIdempotent`).
  * the "pieces have points" AXIOM proper (the comparison is EPI / points dense in pieces), beyond the canonical
    map shipped here, needs an image factorization (`fxMode_hasPiecesHavePointsEpi`).
  * the real-cohesive `ℝ`-locality (C2: `ʃ` computes the topological shape) is `mode-14`
    (`RealCohesion` / `fxMode_hasShulmanRealCohesiveAxioms`), not re-derived here.
  * the cohesion modalities' COMPUTATION (deciding the adjoint-string normal form) needs the keystone's
    decidable mode 2-cell equality (`fxMode_hasModeRelativeConvDecision`, currently `false`)
    (`fxMode_hasCohesionModalityComputation`).

Zero external dependencies beyond the cohesion edge.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The modal adjunctions `ʃ ⊣ ♭` and `♭ ⊣ ♯`, built cast-free -/

/-- ★ The **shape-flat adjunction** `ʃ ⊣ ♭` — `Hom(ʃ X, A) ≃ Hom(X, ♭ A)` — built by composing the quadruple's
hom-set transpositions: `(Disc(Π₀ X) → A) --discreteSections--> (Π₀ X → Γ A) --piecesDiscrete--> (X → Disc(Γ A))`.
Because the central `Disc` is the SAME field of the quadruple on both sides, the composite is CAST-FREE; the
round-trip laws collapse by the two component adjunctions' laws under `congrArg`.  GENERAL — this is the
derivation `mode-13` deferred. -/
def CohesionAdjointQuadruple.shapeFlatAdjunction (quadruple : CohesionAdjointQuadruple) :
    HomAdjunctionBetween quadruple.shapeModality quadruple.flatModality where
  transpose := fun shapeMorphism =>
    quadruple.piecesDiscrete.transpose (quadruple.discreteSections.transpose shapeMorphism)
  untranspose := fun flatMorphism =>
    quadruple.discreteSections.untranspose (quadruple.piecesDiscrete.untranspose flatMorphism)
  transpose_untranspose := fun flatMorphism =>
    Eq.trans
      (congrArg quadruple.piecesDiscrete.transpose
        (quadruple.discreteSections.transpose_untranspose (quadruple.piecesDiscrete.untranspose flatMorphism)))
      (quadruple.piecesDiscrete.transpose_untranspose flatMorphism)
  untranspose_transpose := fun shapeMorphism =>
    Eq.trans
      (congrArg quadruple.discreteSections.untranspose
        (quadruple.piecesDiscrete.untranspose_transpose (quadruple.discreteSections.transpose shapeMorphism)))
      (quadruple.discreteSections.untranspose_transpose shapeMorphism)

/-- ★ The **flat-sharp adjunction** `♭ ⊣ ♯` — `Hom(♭ X, A) ≃ Hom(X, ♯ A)` — built by composing
`(Disc(Γ X) → A) --discreteSections--> (Γ X → Γ A) --sectionsCodiscrete--> (X → coDisc(Γ A))`.  CAST-FREE for
the same reason (the central `Γ` is the SAME field on both sides).  GENERAL. -/
def CohesionAdjointQuadruple.flatSharpAdjunction (quadruple : CohesionAdjointQuadruple) :
    HomAdjunctionBetween quadruple.flatModality quadruple.sharpModality where
  transpose := fun flatMorphism =>
    quadruple.sectionsCodiscrete.transpose (quadruple.discreteSections.transpose flatMorphism)
  untranspose := fun sharpMorphism =>
    quadruple.discreteSections.untranspose (quadruple.sectionsCodiscrete.untranspose sharpMorphism)
  transpose_untranspose := fun sharpMorphism =>
    Eq.trans
      (congrArg quadruple.sectionsCodiscrete.transpose
        (quadruple.discreteSections.transpose_untranspose
          (quadruple.sectionsCodiscrete.untranspose sharpMorphism)))
      (quadruple.sectionsCodiscrete.transpose_untranspose sharpMorphism)
  untranspose_transpose := fun flatMorphism =>
    Eq.trans
      (congrArg quadruple.discreteSections.untranspose
        (quadruple.sectionsCodiscrete.untranspose_transpose
          (quadruple.discreteSections.transpose flatMorphism)))
      (quadruple.discreteSections.untranspose_transpose flatMorphism)

/-! ## The adjoint string `ʃ ⊣ ♭ ⊣ ♯` -/

/-- The **cohesion adjoint string** `ʃ ⊣ ♭ ⊣ ♯` — the two modal adjunctions sharing the central flat modality
`♭` (manifest in the field types: `shapeFlat`'s right functor and `flatSharp`'s left functor are BOTH
`quadruple.flatModality`). -/
structure CohesionModalityAdjointString (quadruple : CohesionAdjointQuadruple) where
  /-- `ʃ ⊣ ♭`. -/
  shapeFlat : HomAdjunctionBetween quadruple.shapeModality quadruple.flatModality
  /-- `♭ ⊣ ♯` (so `♭` is central — right adjoint below, left adjoint above). -/
  flatSharp : HomAdjunctionBetween quadruple.flatModality quadruple.sharpModality

/-- ★ The cohesion adjoint string of a quadruple — `ʃ ⊣ ♭ ⊣ ♯` assembled from the two cast-free modal
adjunctions.  GENERAL over any quadruple. -/
def CohesionAdjointQuadruple.cohesionAdjointString (quadruple : CohesionAdjointQuadruple) :
    CohesionModalityAdjointString quadruple where
  shapeFlat := quadruple.shapeFlatAdjunction
  flatSharp := quadruple.flatSharpAdjunction

/-- ★ The string COMPOSES: the right adjoint of `ʃ ⊣ ♭` IS the left adjoint of `♭ ⊣ ♯` (the shared central
`♭`), so the two adjunctions form the genuine adjoint string `ʃ ⊣ ♭ ⊣ ♯`.  The GENERAL analogue of
`mode-13`'s `trivialCohesion_adjointString` (which held only for the trivial cohesion). -/
theorem CohesionAdjointQuadruple.cohesionAdjointString_middle (quadruple : CohesionAdjointQuadruple) :
    quadruple.shapeFlatAdjunction.toHomAdjunction.rightFunctor
      = quadruple.flatSharpAdjunction.toHomAdjunction.leftFunctor := rfl

/-! ## The (co)pointed structure — units and counit from identities -/

/-- ★ The **shape unit** `η^ʃ : X → ʃX` — the unit of `Π₀ ⊣ Disc`, the transpose of the identity on `Π₀ X`.
Every type maps to its shape.  GENERAL, no functorial `map` needed. -/
def CohesionAdjointQuadruple.shapeUnit (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    typeX → quadruple.shapeModality typeX :=
  quadruple.piecesDiscrete.transpose (fun piece => piece)

/-- ★ The **flat counit** `ε^♭ : ♭X → X` — the counit of `Disc ⊣ Γ`, the untranspose of the identity on `Γ X`.
Flat is copointed (a comonad counit).  GENERAL. -/
def CohesionAdjointQuadruple.flatCounit (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    quadruple.flatModality typeX → typeX :=
  quadruple.discreteSections.untranspose (fun globalSection => globalSection)

/-- ★ The **sharp unit** `η^♯ : X → ♯X` — the unit of `Γ ⊣ coDisc`, the transpose of the identity on `Γ X`.
Sharp is pointed (a monad unit).  GENERAL. -/
def CohesionAdjointQuadruple.sharpUnit (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    typeX → quadruple.sharpModality typeX :=
  quadruple.sectionsCodiscrete.transpose (fun globalSection => globalSection)

/-- ★ The canonical **points comparison** `♭X → ʃX` — flat counit then shape unit (`ε^♭` then `η^ʃ`), the modal
shadow of "pieces have points" (every flat point lies over a shape component).  GENERAL; the AXIOM proper (this
is epi / points dense in pieces) is deferred. -/
def CohesionAdjointQuadruple.piecesHavePoints (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    quadruple.flatModality typeX → quadruple.shapeModality typeX :=
  fun flatPoint => quadruple.shapeUnit typeX (quadruple.flatCounit typeX flatPoint)

/-- The points comparison is exactly `shapeUnit ∘ flatCounit` (the construction, definitionally). -/
theorem CohesionAdjointQuadruple.piecesHavePoints_eq (quadruple : CohesionAdjointQuadruple) (typeX : Type)
    (flatPoint : quadruple.flatModality typeX) :
    quadruple.piecesHavePoints typeX flatPoint
      = quadruple.shapeUnit typeX (quadruple.flatCounit typeX flatPoint) := rfl

/-! ## Idempotency of the modalities — the concrete witness -/

/-- Smoke: the trivial quadruple's shape modality is idempotent (`ʃʃ = ʃ`).  General natural idempotency needs
`Disc` fully faithful + a functorial `map` (deferred); the trivial witness has it by `rfl`. -/
theorem trivialCohesionQuadruple_shapeModality_idempotent (typeX : Type) :
    trivialCohesionQuadruple.shapeModality (trivialCohesionQuadruple.shapeModality typeX)
      = trivialCohesionQuadruple.shapeModality typeX := rfl

/-- Smoke: the trivial quadruple's flat modality is idempotent (`♭♭ = ♭`). -/
theorem trivialCohesionQuadruple_flatModality_idempotent (typeX : Type) :
    trivialCohesionQuadruple.flatModality (trivialCohesionQuadruple.flatModality typeX)
      = trivialCohesionQuadruple.flatModality typeX := rfl

/-- Smoke: the trivial quadruple's sharp modality is idempotent (`♯♯ = ♯`). -/
theorem trivialCohesionQuadruple_sharpModality_idempotent (typeX : Type) :
    trivialCohesionQuadruple.sharpModality (trivialCohesionQuadruple.sharpModality typeX)
      = trivialCohesionQuadruple.sharpModality typeX := rfl

/-! ## Trivial-witness smokes for the string + units -/

/-- Smoke: the trivial quadruple's `ʃ ⊣ ♭` transpose is the identity (both modalities are `Id`). -/
theorem trivialCohesionQuadruple_shapeFlat_transpose (typeX typeA : Type)
    (shapeMorphism : trivialCohesionQuadruple.shapeModality typeX → typeA) :
    trivialCohesionQuadruple.shapeFlatAdjunction.transpose shapeMorphism = shapeMorphism := rfl

/-- Smoke: the trivial quadruple's `♭ ⊣ ♯` transpose is the identity. -/
theorem trivialCohesionQuadruple_flatSharp_transpose (typeX typeA : Type)
    (flatMorphism : trivialCohesionQuadruple.flatModality typeX → typeA) :
    trivialCohesionQuadruple.flatSharpAdjunction.transpose flatMorphism = flatMorphism := rfl

/-- Smoke: the trivial quadruple's shape unit is the identity. -/
theorem trivialCohesionQuadruple_shapeUnit (typeX : Type) (element : typeX) :
    trivialCohesionQuadruple.shapeUnit typeX element = element := rfl

/-- Smoke: the trivial quadruple's flat counit is the identity. -/
theorem trivialCohesionQuadruple_flatCounit (typeX : Type) (element : typeX) :
    trivialCohesionQuadruple.flatCounit typeX element = element := rfl

/-- Smoke: the trivial quadruple's points comparison is the identity. -/
theorem trivialCohesionQuadruple_piecesHavePoints (typeX : Type) (element : typeX) :
    trivialCohesionQuadruple.piecesHavePoints typeX element = element := rfl

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the `ʃ ⊣ ♭ ⊣ ♯` adjoint string ships GENERALLY.**  Both modal adjunctions
(`shapeFlatAdjunction` / `flatSharpAdjunction`) are built CAST-FREE for ANY `CohesionAdjointQuadruple` by
composing the quadruple's hom-set transpositions, packaged as `cohesionAdjointString` with the shared central
`♭` (`cohesionAdjointString_middle`).  This discharges the derivation `mode-13` deferred as
`fxMode_hasCohesiveModalityAdjointString` (general, not trivial-only).  `= true`. -/
def fxMode_hasCohesionAdjointString : Bool := true

/-- ★ **Honesty marker — the cohesion AXIOMS ship as general structural facts.**  The (co)pointed structure of
the three modalities — the shape unit `η^ʃ` (`shapeUnit`), the flat counit `ε^♭` (`flatCounit`), the sharp unit
`η^♯` (`sharpUnit`) — and the canonical points comparison `♭ ⟹ ʃ` (`piecesHavePoints`), all GENERAL over any
quadruple and cast-free (each a transpose / untranspose of an identity).  Together with the adjoint string these
are the structural core (C0–C1) of the cohesion axioms; the deeper conditions (C1-epi, C2 `ℝ`-locality) stay
deferred (see below + `mode-14`).  `= true`. -/
def fxMode_hasCohesionAxioms : Bool := true

/-- **Honesty marker.**  GENERAL natural IDEMPOTENCY of the cohesive modalities (`ʃʃ ≅ ʃ`, `♭♭ ≅ ♭`, `♯♯ ≅ ♯`)
needs `Disc` / `coDisc` FULLY FAITHFUL plus a functorial `map` on the four functors (to lift the resulting iso
through `Disc` / `coDisc`); bare hom-set transposition carries neither, so idempotency ships for the concrete
(trivial) witness only.  `= false`. -/
def fxMode_hasCohesionModalityIdempotent : Bool := false

/-- **Honesty marker.**  The "pieces have points" AXIOM proper — that the canonical comparison `♭X → ʃX`
(`piecesHavePoints`) is EPI / points are dense in pieces (punctual local connectedness) — needs an image
factorization beyond the comparison map shipped here.  `= false`. -/
def fxMode_hasPiecesHavePointsEpi : Bool := false

/-- **Honesty marker.**  The cohesion modalities' COMPUTATION — deciding the adjoint-string normal form, i.e.
when two composites of `ʃ` / `♭` / `♯` are equal as mode 2-cells — needs the keystone's decidable mode 2-cell
equality (`fxMode_hasModeRelativeConvDecision`, currently `false`, blocked by the `mode-3` 3-polygraph
convergence).  Gated on that keystone.  `= false`. -/
def fxMode_hasCohesionModalityComputation : Bool := false

end FX1Poly.Tier0
