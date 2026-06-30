import FX1Poly.Tier0.Mode.CohesionFlatModality
import FX1Poly.Tier0.Mode.CohesionSharpModality
import FX1Poly.Tier0.Mode.CohesionShapeModality

/-! # mode-13 (cohesion family metatheory) — recovery-classification + structure-class facts (structural part)

The three cohesion modalities `ʃ` (shape), `♭` (flat), `♯` (sharp) close type-11 (cohesive type-level
modalities).  Their individual rows shipped in `CohesionShapeModality` / `CohesionFlatModality` /
`CohesionSharpModality`; this file ships the STRUCTURAL part of the cohesion-FAMILY metatheory — the parts that
classify the family and record its structure-class facts, all CAST-FREE off the shipped adjoint string.  The
COMPUTATION leg (deciding when two `ʃ`/`♭`/`♯` composites are equal) is HONESTLY WALLED on the keystone's
decidable mode 2-cell equality.

## What this file ships (each piece zero-axiom)

  * **`CohesionModality` / `CohesionModalityKind` / `cohesionModalityKind`** — the RECOVERY-CLASSIFICATION: each
    of the three cohesion modalities is recovered as a zoo class — `ʃ` and `♯` are REFLECTIVE subuniverses
    (idempotent monads), `♭` is the COREFLECTIVE subuniverse (idempotent comonad).  Plus the adjoint-string
    POSITION (`cohesionModalityPosition`: shape leftmost, flat central, sharp rightmost) and the
    non-degeneracy fact (`cohesionModalityKind_flat_ne_shape`: `♭` genuinely differs in kind from `ʃ`).
  * **`CohesionModalityFamily` / `trivialCohesionModalityFamily`** — the family as a BUNDLE of the three
    concrete (co)reflective witnesses (`mode-20` `Modality` / `CoreflectiveSubuniverse`), tying the bundle's
    (co)units to the shipped `shapeUnit` / `flatCounit` / `sharpUnit` by `rfl`.
  * **`cohesionFamily_flatCentral`** — the structure-class admissibility fact: `♭` is CENTRAL (the right adjoint
    of `ʃ ⊣ ♭` IS the left adjoint of `♭ ⊣ ♯`), GENERAL, re-read off `cohesionAdjointString_middle`.
  * **`cohesionFamily_triangleBetaEta`** — the family's three triangle β/η laws (`transpose ε^♭ = id`,
    `untranspose η^♯ = id`, `untranspose η^ʃ = id`) assembled into one structure-class fact, GENERAL.
  * **`cohesionFamily_piecesHavePoints`** — the cross-modality comparison `♭ ⟹ ʃ` (the modal shadow of "pieces
    have points") factors as `η^ʃ ∘ ε^♭`, GENERAL.

## What is DEFERRED (markers)

  * the COMPUTATION leg — `fxMode_hasCohesionModalityComputation` (in `CohesionAdjointString`) — deciding the
    adjoint-string normal form (when two composites of `ʃ` / `♭` / `♯` are equal as mode 2-cells) is gated on the
    keystone `fxMode_hasModeRelativeConvDecision` (currently `false`, blocked by the `mode-3` 3-polygraph
    convergence).  This file does NOT claim SR / SN / canonicity-by-computation for the modalities; only the
    structural adjoint-derived facts above.
  * the GENERAL (co)monad multiplication / natural idempotency of each modality stays the per-modality wall
    (`fxMode_hasCohesion{Shape,Flat,Sharp}…General`); the family bundle here is the concrete (trivial) witness.

Zero external dependencies beyond the three cohesion modality files.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The recovery-classification -/

/-- A tag for the three cohesion modalities of the string `ʃ ⊣ ♭ ⊣ ♯`. -/
inductive CohesionModality where
  /-- The shape modality `ʃ = Disc ∘ Π₀`. -/
  | shape
  /-- The flat modality `♭ = Disc ∘ Γ`. -/
  | flat
  /-- The sharp modality `♯ = coDisc ∘ Γ`. -/
  | sharp

/-- The (co)reflective ZOO class of a cohesion modality — the recovery-classification target. -/
inductive CohesionModalityKind where
  /-- A reflective subuniverse (idempotent MONAD) — `ʃ` and `♯`. -/
  | reflective
  /-- A coreflective subuniverse (idempotent COMONAD) — `♭`. -/
  | coreflective

/-- ★ The **recovery-classification** — which (co)reflective zoo class each cohesion modality is: `ʃ` and `♯` are
REFLECTIVE (idempotent monads, the shape reflector and the codiscrete reflector), `♭` is COREFLECTIVE (the
idempotent comonad, the discrete coreflector). -/
def cohesionModalityKind : CohesionModality → CohesionModalityKind
  | .shape => .reflective
  | .flat => .coreflective
  | .sharp => .reflective

/-- The adjoint-string POSITION of a cohesion modality — shape leftmost, flat central, sharp rightmost. -/
inductive CohesionStringPosition where
  /-- The leftmost modality `ʃ` (left adjoint of `♭`). -/
  | leftmost
  /-- The central modality `♭` (right adjoint of `ʃ`, left adjoint of `♯`). -/
  | central
  /-- The rightmost modality `♯` (right adjoint of `♭`). -/
  | rightmost

/-- ★ The adjoint-string POSITION of each cohesion modality. -/
def cohesionModalityPosition : CohesionModality → CohesionStringPosition
  | .shape => .leftmost
  | .flat => .central
  | .sharp => .rightmost

/-- `ʃ` and `♯` share the reflective kind (both idempotent monads). -/
theorem cohesionModalityKind_shape_eq_sharp :
    cohesionModalityKind .shape = cohesionModalityKind .sharp := rfl

/-- ★ The classification is NON-DEGENERATE: `♭` (coreflective) genuinely differs in kind from `ʃ` (reflective). -/
theorem cohesionModalityKind_flat_ne_shape :
    cohesionModalityKind .flat ≠ cohesionModalityKind .shape :=
  fun kindsEqual => CohesionModalityKind.noConfusion kindsEqual

/-! ## The family as a bundle of concrete (co)reflective witnesses -/

/-- The **cohesion modality family** — the three modalities as their recovered (co)reflective witnesses: `ʃ` and
`♯` as `Modality` (reflective monad) instances, `♭` as a `CoreflectiveSubuniverse` (coreflective comonad)
instance. -/
structure CohesionModalityFamily where
  /-- The shape modality as a reflective subuniverse. -/
  shapeReflective : Modality
  /-- The flat modality as a coreflective subuniverse. -/
  flatCoreflective : CoreflectiveSubuniverse
  /-- The sharp modality as a reflective subuniverse. -/
  sharpReflective : Modality

/-- ★ The trivial cohesion's modality family — the three concrete witnesses from the per-modality files. -/
def trivialCohesionModalityFamily : CohesionModalityFamily where
  shapeReflective := trivialCohesionShapeModality
  flatCoreflective := trivialCohesionFlatComodality
  sharpReflective := trivialCohesionSharpModality

/-- The family's shape unit IS the shipped shape unit. -/
theorem trivialCohesionModalityFamily_shapeUnit (typeX : Type) (point : typeX) :
    trivialCohesionModalityFamily.shapeReflective.unit point
      = trivialCohesionQuadruple.shapeUnit typeX point := rfl

/-- The family's flat counit IS the shipped flat counit. -/
theorem trivialCohesionModalityFamily_flatCounit (typeX : Type)
    (element : trivialCohesionQuadruple.flatModality typeX) :
    trivialCohesionModalityFamily.flatCoreflective.counit element
      = trivialCohesionQuadruple.flatCounit typeX element := rfl

/-- The family's sharp unit IS the shipped sharp unit. -/
theorem trivialCohesionModalityFamily_sharpUnit (typeX : Type) (point : typeX) :
    trivialCohesionModalityFamily.sharpReflective.unit point
      = trivialCohesionQuadruple.sharpUnit typeX point := rfl

/-! ## Structure-class facts (general, cast-free) -/

/-- ★ The structure-class admissibility fact: `♭` is CENTRAL — the right adjoint of `ʃ ⊣ ♭` IS the left adjoint of
`♭ ⊣ ♯`, so the family genuinely forms the adjoint string `ʃ ⊣ ♭ ⊣ ♯`.  GENERAL, re-read off the shipped string. -/
theorem cohesionFamily_flatCentral (quadruple : CohesionAdjointQuadruple) :
    quadruple.shapeFlatAdjunction.toHomAdjunction.rightFunctor
      = quadruple.flatSharpAdjunction.toHomAdjunction.leftFunctor :=
  quadruple.cohesionAdjointString_middle

/-- ★ The family's three triangle β/η laws assembled — `transpose (ε^♭) = id`, `untranspose (η^♯) = id`,
`untranspose (η^ʃ) = id` — the structure-class fact that all three (co)units are (un)transposes of identities.
GENERAL over any quadruple, cast-free. -/
theorem cohesionFamily_triangleBetaEta (quadruple : CohesionAdjointQuadruple) (typeX : Type) :
    quadruple.discreteSections.transpose (quadruple.flatCounit typeX) = (fun globalSection => globalSection)
      ∧ quadruple.sectionsCodiscrete.untranspose (quadruple.sharpUnit typeX)
          = (fun globalSection => globalSection)
      ∧ quadruple.piecesDiscrete.untranspose (quadruple.shapeUnit typeX) = (fun piece => piece) :=
  ⟨quadruple.flatCounit_transpose typeX, quadruple.sharpUnit_untranspose typeX,
    quadruple.shapeUnit_untranspose typeX⟩

/-- ★ The cross-modality comparison `♭ ⟹ ʃ` (the modal shadow of "pieces have points") factors as the shape unit
after the flat counit (`η^ʃ ∘ ε^♭`).  GENERAL — the structural bridge between the coreflective `♭` and the
reflective `ʃ`. -/
theorem cohesionFamily_piecesHavePoints (quadruple : CohesionAdjointQuadruple) (typeX : Type)
    (flatPoint : quadruple.flatModality typeX) :
    quadruple.piecesHavePoints typeX flatPoint
      = quadruple.shapeUnit typeX (quadruple.flatCounit typeX flatPoint) :=
  quadruple.piecesHavePoints_eq typeX flatPoint

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the cohesion-family STRUCTURAL metatheory ships.**  The recovery-classification
(`cohesionModalityKind`: `ʃ`/`♯` reflective, `♭` coreflective + the non-degeneracy
`cohesionModalityKind_flat_ne_shape` + the string position `cohesionModalityPosition`), the family bundle of
concrete (co)reflective witnesses tying the (co)units to the shipped string (`CohesionModalityFamily` /
`trivialCohesionModalityFamily` + the unit/counit ties), and the structure-class facts (`cohesionFamily_flatCentral`,
`cohesionFamily_triangleBetaEta`, `cohesionFamily_piecesHavePoints`) — all CAST-FREE off the shipped adjoint
string.  This is the STRUCTURAL part of type-11's closure.  `= true`. -/
def fxMode_hasCohesionFamilyStructuralMetatheory : Bool := true

/-- **Honesty marker.**  The cohesion-family COMPUTATION metatheory — SR / SN / canonicity by deciding the
adjoint-string normal form (when two `ʃ` / `♭` / `♯` composites are equal as mode 2-cells) — is NOT claimed here.
It is gated on the keystone `fxMode_hasModeRelativeConvDecision` (currently `false`, blocked by the `mode-3`
3-polygraph convergence), exactly as the string's `fxMode_hasCohesionModalityComputation` already records.  The
structural facts above are adjoint-derived only; no computation/canonicity is asserted for the modalities.
`= false`. -/
def fxMode_hasCohesionFamilyComputationMetatheory : Bool := false

end FX1Poly.Tier0
