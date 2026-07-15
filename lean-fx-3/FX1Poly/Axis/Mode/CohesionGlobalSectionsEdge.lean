import FX1Poly.Axis.Mode.Cohesion

/-! # mode-13 (cohesion edge) — the global-sections geometric morphism + the explicit-functor adjoint quadruple

`mode-13` (`Cohesion.lean`) shipped the cohesive adjoint quadruple `Π₀ ⊣ Disc ⊣ Γ ⊣ Codisc` as three
`HomAdjunction`s sharing their middle functors via PROPOSITIONAL equalities (`discShared` / `pointsShared`).
That packaging is exactly why the GENERAL adjoint-modality string `ʃ ⊣ ♭ ⊣ ♯` was deferred there
(`fxMode_hasCohesiveModalityAdjointString = false`): composing two `HomAdjunction`s across a propositional
shared-functor equality threads `Eq.rec` casts through every round-trip law.

This file ships the CLEANER presentation that removes the obstruction — the cohesion **EDGE**.  A cohesive base
is, before anything else, the GLOBAL-SECTIONS GEOMETRIC MORPHISM `Γ : Psh(W) → Set` — the vertical edge of the
mode 2-category connecting the presheaf mode to the point mode `Set` — given by an adjoint pair
`Disc ⊣ Γ` (inverse image ⊣ direct image).  Lawvere cohesion EXTENDS that edge with a further LEFT adjoint
`Π₀ ⊣ Disc` (locally connected) and a further RIGHT adjoint `Γ ⊣ coDisc` (local), giving the quadruple.

## What this file ships (each piece zero-axiom)

  * **`HomAdjunctionBetween L R`** — a hom-set adjunction `L ⊣ R` with the two functors as STRUCTURE PARAMETERS
    (not fields), so adjacent adjunctions in a string share a functor DEFINITIONALLY.  Derived faithfulness +
    surjectivity (the transposition is a full bijection); `toHomAdjunction` / `HomAdjunction.toBetween` bridges
    to `mode-13`'s packaged form.
  * **`GeometricMorphism`** — the vertical edge: an inverse-image / direct-image adjoint pair `f^* ⊣ f_*`, with
    `identityGeometricMorphism` and the transposition's derived faithfulness.
  * **`CohesionAdjointQuadruple`** — the adjoint quadruple `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` with the four functors
    EXPLICIT and the three `HomAdjunctionBetween` adjunction WITNESSES sharing functors definitionally.  Its
    **`globalSectionsEdge`** extracts the middle `Disc ⊣ Γ` geometric morphism (the edge), with the shared
    functors witnessed by `rfl`; the locally-connected / local extensions are the outer two adjunctions.
  * **`trivialCohesionQuadruple`** — the concrete (degenerate, all-`Id`) witness with the edge / modality smokes.
  * **`CohesionAdjointQuadruple.toCohesiveQuadruple`** — the bridge to `mode-13`'s `CohesiveQuadruple`, with the
    shared-functor equalities discharged by `rfl` and the three modalities shown to AGREE (so this is a genuine
    refinement of the `mode-13` packaging, not a parallel duplicate).

## What is DEFERRED (markers)

  * the genuine NON-DEGENERATE cohesive geometric morphism (presheaf / smooth sets) — the trivial witness is
    degenerate (`fxMode_hasCohesiveToposModelEdge`); this matches `mode-13`'s `hasCohesiveToposModel`.
  * the inverse image being LEFT EXACT (a genuine geometric morphism preserves finite limits) — bare hom-set
    transposition cannot express finite-limit preservation (`fxMode_hasGeometricMorphismLeftExact`).
  * the GENERAL `ʃ ⊣ ♭ ⊣ ♯` adjoint string + the cohesion axioms are the SEQUEL file (`CohesionAdjointString`).

Zero external dependencies beyond `mode-13`.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Axis

/-! ## Hom-set adjunctions with the functors as parameters -/

/-- A **hom-set adjunction with explicit functors** `leftFunctor ⊣ rightFunctor` — the natural bijection
`(leftFunctor X → A) ≃ (X → rightFunctor A)`, but with the two functors as STRUCTURE PARAMETERS rather than
fields.  This is the only difference from `mode-13`'s `HomAdjunction`, and it is the load-bearing one: when two
such adjunctions are composed in an adjoint STRING the shared functor is referenced by the SAME parameter on
both sides, so the composite's round-trip laws need no `Eq.rec` cast across a propositional shared-functor
equality. -/
structure HomAdjunctionBetween (leftFunctor rightFunctor : Type → Type) where
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

/-- ★ The forward transposition is FAITHFUL — derived from the adjunction iso. -/
theorem HomAdjunctionBetween.transpose_injective {leftFunctor rightFunctor : Type → Type}
    (adjunction : HomAdjunctionBetween leftFunctor rightFunctor) {X A : Type}
    {firstMorphism secondMorphism : leftFunctor X → A}
    (transposesEqual : adjunction.transpose firstMorphism = adjunction.transpose secondMorphism) :
    firstMorphism = secondMorphism := by
  rw [← adjunction.untranspose_transpose firstMorphism,
      ← adjunction.untranspose_transpose secondMorphism, transposesEqual]

/-- ★ The forward transposition is SURJECTIVE — with injectivity, a full BIJECTION. -/
theorem HomAdjunctionBetween.transpose_surjective {leftFunctor rightFunctor : Type → Type}
    (adjunction : HomAdjunctionBetween leftFunctor rightFunctor) {X A : Type}
    (rightMorphism : X → rightFunctor A) :
    ∃ leftMorphism : leftFunctor X → A, adjunction.transpose leftMorphism = rightMorphism :=
  ⟨adjunction.untranspose rightMorphism, adjunction.transpose_untranspose rightMorphism⟩

/-- The identity hom-adjunction `Id ⊣ Id` with explicit functors. -/
def identityHomAdjunctionBetween : HomAdjunctionBetween (fun carrier => carrier) (fun carrier => carrier) where
  transpose := fun morphism => morphism
  untranspose := fun morphism => morphism
  transpose_untranspose := fun _rightMorphism => rfl
  untranspose_transpose := fun _leftMorphism => rfl

/-- Forget the explicit functors back into a `mode-13` `HomAdjunction`. -/
def HomAdjunctionBetween.toHomAdjunction {leftFunctor rightFunctor : Type → Type}
    (adjunction : HomAdjunctionBetween leftFunctor rightFunctor) : HomAdjunction where
  leftFunctor := leftFunctor
  rightFunctor := rightFunctor
  transpose := adjunction.transpose
  untranspose := adjunction.untranspose
  transpose_untranspose := adjunction.transpose_untranspose
  untranspose_transpose := adjunction.untranspose_transpose

/-- Read a packaged `HomAdjunction` as an explicit-functor adjunction between its own functors. -/
def HomAdjunction.toBetween (adjunction : HomAdjunction) :
    HomAdjunctionBetween adjunction.leftFunctor adjunction.rightFunctor where
  transpose := adjunction.transpose
  untranspose := adjunction.untranspose
  transpose_untranspose := adjunction.transpose_untranspose
  untranspose_transpose := adjunction.untranspose_transpose

/-- The two bridges round-trip on the functors (the explicit functors ARE the packaged ones). -/
theorem HomAdjunctionBetween.toHomAdjunction_functors {leftFunctor rightFunctor : Type → Type}
    (adjunction : HomAdjunctionBetween leftFunctor rightFunctor) :
    adjunction.toHomAdjunction.leftFunctor = leftFunctor
      ∧ adjunction.toHomAdjunction.rightFunctor = rightFunctor :=
  ⟨rfl, rfl⟩

/-! ## The geometric morphism — the vertical edge -/

/-- A **geometric morphism** `f : E → S` — the vertical edge of the mode 2-category: an adjoint pair
`inverseImage ⊣ directImage` (`f^* ⊣ f_*`), the inverse image the left adjoint.  The global-sections
geometric morphism `Γ : Psh(W) → Set` is the canonical one (`inverseImage = Disc`, `directImage = Γ`).
(A genuine geometric morphism additionally requires `f^*` LEFT EXACT — see the markers; bare hom-set
transposition cannot express finite-limit preservation.) -/
structure GeometricMorphism where
  /-- The inverse-image functor `f^*` (left adjoint). -/
  inverseImage : Type → Type
  /-- The direct-image functor `f_*` (right adjoint). -/
  directImage : Type → Type
  /-- The adjunction `f^* ⊣ f_*`. -/
  adjunction : HomAdjunctionBetween inverseImage directImage

/-- The identity geometric morphism `Id ⊣ Id` (the edge of the point mode onto itself). -/
def identityGeometricMorphism : GeometricMorphism where
  inverseImage := fun carrier => carrier
  directImage := fun carrier => carrier
  adjunction := identityHomAdjunctionBetween

/-- ★ The inverse image is FAITHFUL through the edge transposition — a geometric morphism's adjunction is a
genuine hom-set bijection. -/
theorem GeometricMorphism.transpose_injective (edge : GeometricMorphism) {X A : Type}
    {firstMorphism secondMorphism : edge.inverseImage X → A}
    (transposesEqual : edge.adjunction.transpose firstMorphism = edge.adjunction.transpose secondMorphism) :
    firstMorphism = secondMorphism :=
  edge.adjunction.transpose_injective transposesEqual

/-! ## The cohesion adjoint quadruple, with explicit functors -/

/-- A **cohesion adjoint quadruple** `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` — the datum of Lawvere cohesion with the four
functors EXPLICIT and the three adjunctions as `HomAdjunctionBetween` witnesses.  Because the functors are
fields referenced by the adjunctions, the middle `Disc` and `Γ` are shared DEFINITIONALLY between consecutive
adjunctions (no propositional shared-functor equality).  This is the genuine adjoint STRING shape; its
`globalSectionsEdge` is the geometric morphism, the outer two adjunctions its locally-connected / local
extensions. -/
structure CohesionAdjointQuadruple where
  /-- The shape / pieces / connected-components functor `Π₀`. -/
  pieces : Type → Type
  /-- The discrete-inclusion functor `Disc`. -/
  discrete : Type → Type
  /-- The global-sections / points functor `Γ`. -/
  globalSections : Type → Type
  /-- The codiscrete-inclusion functor `coDisc`. -/
  codiscrete : Type → Type
  /-- `Π₀ ⊣ Disc` — the pieces functor is left adjoint to the discrete inclusion. -/
  piecesDiscrete : HomAdjunctionBetween pieces discrete
  /-- `Disc ⊣ Γ` — the discrete inclusion is left adjoint to global sections (the geometric morphism). -/
  discreteSections : HomAdjunctionBetween discrete globalSections
  /-- `Γ ⊣ coDisc` — global sections is left adjoint to the codiscrete inclusion. -/
  sectionsCodiscrete : HomAdjunctionBetween globalSections codiscrete

/-- ★ The **global-sections geometric morphism** — the vertical edge `Disc ⊣ Γ` extracted from the quadruple
(`inverseImage = Disc`, `directImage = Γ`).  This is THE cohesion edge; cohesion is this edge plus the outer
two adjoints. -/
def CohesionAdjointQuadruple.globalSectionsEdge (quadruple : CohesionAdjointQuadruple) : GeometricMorphism where
  inverseImage := quadruple.discrete
  directImage := quadruple.globalSections
  adjunction := quadruple.discreteSections

/-- The edge's inverse image is the discrete functor (definitionally). -/
theorem CohesionAdjointQuadruple.globalSectionsEdge_inverseImage (quadruple : CohesionAdjointQuadruple) :
    quadruple.globalSectionsEdge.inverseImage = quadruple.discrete := rfl

/-- The edge's direct image is the global-sections functor (definitionally). -/
theorem CohesionAdjointQuadruple.globalSectionsEdge_directImage (quadruple : CohesionAdjointQuadruple) :
    quadruple.globalSectionsEdge.directImage = quadruple.globalSections := rfl

/-- ★ The `Disc` functor is SHARED — it is the right adjoint of `Π₀ ⊣ Disc` AND the inverse image of the edge,
the same field on both sides (the lower half of the adjoint string sharing the central inverse image). -/
theorem CohesionAdjointQuadruple.discrete_shared (quadruple : CohesionAdjointQuadruple) :
    quadruple.globalSectionsEdge.inverseImage = quadruple.discrete := rfl

/-- ★ The `Γ` functor is SHARED — it is the direct image of the edge AND the left adjoint of `Γ ⊣ coDisc`, the
same field on both sides (the upper half of the string sharing the central direct image). -/
theorem CohesionAdjointQuadruple.globalSections_shared (quadruple : CohesionAdjointQuadruple) :
    quadruple.globalSectionsEdge.directImage = quadruple.globalSections := rfl

/-- ★ The quadruple is **locally connected**: the edge's inverse image `Disc` has a FURTHER LEFT adjoint `Π₀`
(`Π₀ ⊣ Disc`), witnessed by `piecesDiscrete` against the edge's inverse image directly (no cast). -/
def CohesionAdjointQuadruple.isLocallyConnectedWitness (quadruple : CohesionAdjointQuadruple) :
    HomAdjunctionBetween quadruple.pieces quadruple.globalSectionsEdge.inverseImage :=
  quadruple.piecesDiscrete

/-- ★ The quadruple is **local**: the edge's direct image `Γ` has a FURTHER RIGHT adjoint `coDisc`
(`Γ ⊣ coDisc`), witnessed by `sectionsCodiscrete` against the edge's direct image directly (no cast). -/
def CohesionAdjointQuadruple.isLocalWitness (quadruple : CohesionAdjointQuadruple) :
    HomAdjunctionBetween quadruple.globalSectionsEdge.directImage quadruple.codiscrete :=
  quadruple.sectionsCodiscrete

/-! ## The derived cohesive modalities (composites) -/

/-- The **shape modality** `ʃ = Disc ∘ Π₀`. -/
def CohesionAdjointQuadruple.shapeModality (quadruple : CohesionAdjointQuadruple) : Type → Type :=
  fun typeX => quadruple.discrete (quadruple.pieces typeX)

/-- The **flat modality** `♭ = Disc ∘ Γ`. -/
def CohesionAdjointQuadruple.flatModality (quadruple : CohesionAdjointQuadruple) : Type → Type :=
  fun typeX => quadruple.discrete (quadruple.globalSections typeX)

/-- The **sharp modality** `♯ = coDisc ∘ Γ`. -/
def CohesionAdjointQuadruple.sharpModality (quadruple : CohesionAdjointQuadruple) : Type → Type :=
  fun typeX => quadruple.codiscrete (quadruple.globalSections typeX)

/-! ## The concrete (trivial) witness -/

/-- The **trivial (degenerate) cohesion quadruple** — every functor is the identity, every adjunction the
identity hom-adjunction.  The concrete witness (degenerate: the genuine non-degenerate edge needs a real
presheaf base). -/
def trivialCohesionQuadruple : CohesionAdjointQuadruple where
  pieces := fun carrier => carrier
  discrete := fun carrier => carrier
  globalSections := fun carrier => carrier
  codiscrete := fun carrier => carrier
  piecesDiscrete := identityHomAdjunctionBetween
  discreteSections := identityHomAdjunctionBetween
  sectionsCodiscrete := identityHomAdjunctionBetween

/-- Smoke: the trivial quadruple's edge IS the identity geometric morphism. -/
theorem trivialCohesionQuadruple_edge :
    trivialCohesionQuadruple.globalSectionsEdge = identityGeometricMorphism := rfl

/-- Smoke: the trivial quadruple's shape modality is the identity. -/
theorem trivialCohesionQuadruple_shapeModality (typeX : Type) :
    trivialCohesionQuadruple.shapeModality typeX = typeX := rfl

/-- Smoke: the trivial quadruple's flat modality is the identity. -/
theorem trivialCohesionQuadruple_flatModality (typeX : Type) :
    trivialCohesionQuadruple.flatModality typeX = typeX := rfl

/-- Smoke: the trivial quadruple's sharp modality is the identity. -/
theorem trivialCohesionQuadruple_sharpModality (typeX : Type) :
    trivialCohesionQuadruple.sharpModality typeX = typeX := rfl

/-! ## Bridge to the `mode-13` packaged `CohesiveQuadruple` -/

/-- Forget the explicit-functor quadruple into `mode-13`'s `CohesiveQuadruple`.  The shared-functor equalities
`discShared` / `pointsShared` — propositional THERE — are `rfl` HERE, because the explicit functors make the
sharing definitional.  This exhibits `CohesionAdjointQuadruple` as a genuine refinement of the `mode-13`
packaging, not a parallel duplicate. -/
def CohesionAdjointQuadruple.toCohesiveQuadruple (quadruple : CohesionAdjointQuadruple) : CohesiveQuadruple where
  shapeDiscAdjunction := quadruple.piecesDiscrete.toHomAdjunction
  discPointsAdjunction := quadruple.discreteSections.toHomAdjunction
  pointsCodiscAdjunction := quadruple.sectionsCodiscrete.toHomAdjunction
  discShared := rfl
  pointsShared := rfl

/-- The bridge preserves the shape modality (`ʃ` agrees on both presentations). -/
theorem CohesionAdjointQuadruple.toCohesiveQuadruple_shapeModality (quadruple : CohesionAdjointQuadruple)
    (typeX : Type) : quadruple.toCohesiveQuadruple.shapeModality typeX = quadruple.shapeModality typeX := rfl

/-- The bridge preserves the flat modality. -/
theorem CohesionAdjointQuadruple.toCohesiveQuadruple_flatModality (quadruple : CohesionAdjointQuadruple)
    (typeX : Type) : quadruple.toCohesiveQuadruple.flatModality typeX = quadruple.flatModality typeX := rfl

/-- The bridge preserves the sharp modality. -/
theorem CohesionAdjointQuadruple.toCohesiveQuadruple_sharpModality (quadruple : CohesionAdjointQuadruple)
    (typeX : Type) : quadruple.toCohesiveQuadruple.sharpModality typeX = quadruple.sharpModality typeX := rfl

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the cohesion adjoint QUADRUPLE ships.**  The adjoint quadruple `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc`
with the four explicit functors and the three `HomAdjunctionBetween` adjunction witnesses
(`CohesionAdjointQuadruple`), the bridge to `mode-13`'s packaging with the shared-functor equalities discharged
by `rfl`, and the modality agreement.  `= true`. -/
def fxMode_hasCohesionAdjointQuadruple : Bool := true

/-- ★ **Honesty marker — the global-sections geometric-morphism EDGE ships.**  The vertical edge `Disc ⊣ Γ`
(`GeometricMorphism` + `CohesionAdjointQuadruple.globalSectionsEdge`), with the central `Disc` / `Γ` shared by
`rfl` between the edge and the outer adjoints (`discrete_shared` / `globalSections_shared`) and the
locally-connected / local extensions exhibited cast-free (`isLocallyConnectedWitness` / `isLocalWitness`).
`= true`. -/
def fxMode_hasGlobalSectionsEdge : Bool := true

/-- **Honesty marker.**  A genuine NON-DEGENERATE cohesive geometric morphism (presheaf / smooth sets) — the
`trivialCohesionQuadruple` here is degenerate (all functors `Id`, the edge the identity) — is deferred, matching
`mode-13`'s `fxMode_hasCohesiveToposModel`.  `= false`. -/
def fxMode_hasCohesiveToposModelEdge : Bool := false

/-- **Honesty marker.**  A genuine geometric morphism requires the inverse image `f^*` to be LEFT EXACT (preserve
finite limits); bare hom-set transposition cannot express finite-limit preservation, so the edge here is the
adjoint-pair skeleton only.  `= false`. -/
def fxMode_hasGeometricMorphismLeftExact : Bool := false

end FX1Poly.Axis
