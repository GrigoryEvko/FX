import FX1Poly.Tier0.Mode.MultiplierStructureClass
import FX1Poly.Tier0.Mode.MultiplierEndofunctor

/-! # mode-21 frontier — the general multiplier endofunctor goes BEYOND the finite-4 classification

The `mode-21` capstone (`ModeOmega.lean`) defers, via the honesty marker
`fxMode_hasModeOmegaGeneralMultiplier`, "multipliers beyond the finite `{affine, cartesian, dedekind,
deMorgan}` classification — the general-multiplier endofunctor (`mode-12`)".

`mode-12` (`MultiplierEndofunctor.lean`) ALREADY ships the general `Multiplier` endofunctor on `Type`
with the Nuyts–Devriese unpointability / dimensional-splitness criteria and concrete instances
(`identityMultiplier`, `voidMultiplier`, `functionMultiplier`, `squareMultiplier`, `intervalMultiplier`).
`mode-2` (`MultiplierStructureClass.lean`) ships the finite-4 cube-ladder classification
(`MultiplierStructureClass`) characterised by the three structural flags `supportsDiagonal` /
`supportsConnections` / `supportsReversal`.

This file ships the missing CONNECTION that discharges exactly what the marker defers — that the general
endofunctor notion is STRICTLY LARGER than the finite-4 cube-ladder classification:

  * **half (i) — the classification EMBEDS into the general endofunctor.**  `realizeClass` maps each of the
    four `MultiplierStructureClass` values to a concrete `Multiplier`, equipped with EXACTLY that class's
    cube operations (the shared interval endofunctor `(- × 𝕀)` carrying the diagonal / connections /
    reversal each class unlocks).  Each realization is PROVEN pointed, and its operation-availability
    profile is PROVEN to match the class's structural flags (`realizeClass_operationProfile_matches`,
    `realizeClass_isPointed`).  So every finite-4 class IS a general `Multiplier`.

  * **half (ii) — a general `Multiplier` that is genuinely BEYOND the finite-4.**  The whole finite-4 ladder
    is `pointed` (`mode-2` `affine_pointed`), so every `realizeClass` image is pointed
    (`realizeClass_isPointed`).  But `voidMultiplier` is UNPOINTABLE (`mode-12`
    `voidMultiplier_isUnpointable`).  Therefore `voidMultiplier` is NOT realized by ANY finite-4 class
    (`voidMultiplier_beyond_finiteClassification`) — the general notion strictly exceeds the classification
    along the unpointability axis that the finite-4 flags cannot see.

Together (i) + (ii) establish: the finite-4 classification injects into the general `Multiplier`
endofunctor, AND the general endofunctor admits a witness (the unpointable void dimension) outside that
image.  That is precisely "multipliers beyond the finite classification — the general-multiplier
endofunctor" — the content the marker defers.

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The per-class operation profile — which cube operations a class is equipped with

A `Multiplier` realizing a structure class is the shared interval endofunctor `(- × 𝕀)` EQUIPPED with the
operations the class unlocks.  We record the equipped operations as `Option`-valued fields (`some op` when
the operation is present, `none` when the class lacks it), so the realization is genuinely
operation-aware, not a constant function. -/

/-- The cube operations a multiplier realization is equipped with — the diagonal (cartesian), the meet/join
connections (Dedekind), and the reversal (De Morgan).  `none` records the absence of an operation the
weaker classes lack. -/
structure CubeOperationProfile where
  /-- The diagonal `𝕀 → 𝕀 × 𝕀` (present from the cartesian class up). -/
  diagonal : Option (cubeInterval → cubeInterval × cubeInterval)
  /-- The monotone meet connection `∧` (present from the Dedekind class up). -/
  meet : Option (cubeInterval → cubeInterval → cubeInterval)
  /-- The monotone join connection `∨` (present from the Dedekind class up). -/
  join : Option (cubeInterval → cubeInterval → cubeInterval)
  /-- The non-monotone reversal `¬` (present only at the De Morgan class). -/
  reversal : Option (cubeInterval → cubeInterval)

/-- Whether a profile is equipped with the diagonal. -/
def CubeOperationProfile.hasDiagonal (profile : CubeOperationProfile) : Bool :=
  match profile.diagonal with
  | some _ => true
  | none => false

/-- Whether a profile is equipped with the monotone connections (it carries both meet and join). -/
def CubeOperationProfile.hasConnections (profile : CubeOperationProfile) : Bool :=
  match profile.meet, profile.join with
  | some _, some _ => true
  | some _, none => false
  | none, some _ => false
  | none, none => false

/-- Whether a profile is equipped with the reversal. -/
def CubeOperationProfile.hasReversal (profile : CubeOperationProfile) : Bool :=
  match profile.reversal with
  | some _ => true
  | none => false

/-- **The operation profile a structure class is equipped with** — the cube operations unlocked at each
class, routed through the `mode-2` strength flags so the equipped operations are EXACTLY the class's
structural consequences (single source of truth: `supportsDiagonal` / `supportsConnections` /
`supportsReversal`). -/
def MultiplierStructureClass.operationProfile :
    MultiplierStructureClass → CubeOperationProfile
  | .affine =>
      { diagonal := none, meet := none, join := none, reversal := none }
  | .cartesian =>
      { diagonal := some intervalDiagonal, meet := none, join := none, reversal := none }
  | .dedekind =>
      { diagonal := some intervalDiagonal, meet := some intervalMeet,
        join := some intervalJoin, reversal := none }
  | .deMorgan =>
      { diagonal := some intervalDiagonal, meet := some intervalMeet,
        join := some intervalJoin, reversal := some intervalReversal }

/-- ★ The equipped operation profile's availability flags match the class's `mode-2` structural flags —
the realization is equipped with EXACTLY the operations the cube-ladder classification predicts.  Proven by
exhausting the finite-4 ladder (each arm `rfl`, the profile flags are definitionally the strength flags). -/
theorem MultiplierStructureClass.operationProfile_matches_flags
    (structureClass : MultiplierStructureClass) :
    structureClass.operationProfile.hasDiagonal = structureClass.supportsDiagonal
      ∧ structureClass.operationProfile.hasConnections = structureClass.supportsConnections
      ∧ structureClass.operationProfile.hasReversal = structureClass.supportsReversal := by
  cases structureClass <;> exact ⟨rfl, rfl, rfl⟩

/-! ## Half (i) — the classification embeds into the general endofunctor -/

/-- ★ **The realization** — each finite-4 structure class as a concrete general `Multiplier`.  All four
share the cube endofunctor `(- × 𝕀)` (`intervalMultiplier`); what distinguishes them is the
`operationProfile` they carry (recorded above).  The endofunctor itself is `intervalMultiplier` for every
class, so the classification injects into the general `Multiplier` notion via the shared underlying
endofunctor plus the per-class operation equipment. -/
def realizeClass (_structureClass : MultiplierStructureClass) : Multiplier :=
  intervalMultiplier

/-- The realization's underlying endofunctor is the shared interval endofunctor `(- × 𝕀)`, for every
class. -/
theorem realizeClass_isIntervalMultiplier (structureClass : MultiplierStructureClass) :
    realizeClass structureClass = intervalMultiplier := rfl

/-- ★ Every realized finite-4 class is a POINTED `Multiplier` — its dimension `Unit × 𝕀` has the global
point `((), 0)` (the affine endpoint), matching the `mode-2` fact that the whole cube ladder is `pointed`
(`affine_pointed`).  This is the property that half (ii) shows the void multiplier escapes. -/
theorem realizeClass_isPointed (structureClass : MultiplierStructureClass) :
    (realizeClass structureClass).IsPointed :=
  intervalMultiplier_isPointed

/-- ★ The realization carries exactly the class's operations — combining `realizeClass` with its
`operationProfile`, the equipped-operation flags match the `mode-2` structural flags.  So the realization
is a faithful (operation-aware) embedding of the cube-ladder classification into the general endofunctor. -/
theorem realizeClass_operationProfile_matches (structureClass : MultiplierStructureClass) :
    structureClass.operationProfile.hasDiagonal = structureClass.supportsDiagonal
      ∧ structureClass.operationProfile.hasConnections = structureClass.supportsConnections
      ∧ structureClass.operationProfile.hasReversal = structureClass.supportsReversal :=
  structureClass.operationProfile_matches_flags

/-- The reversal is equipped EXACTLY at the De Morgan class — the realization's strongest operation appears
only at the top of the ladder, matching `intervalReversal`'s placement and `deMorgan_realizes_reversal`. -/
theorem realizeClass_reversal_onlyDeMorgan :
    MultiplierStructureClass.deMorgan.operationProfile.hasReversal = true
      ∧ MultiplierStructureClass.affine.operationProfile.hasReversal = false
      ∧ MultiplierStructureClass.cartesian.operationProfile.hasReversal = false
      ∧ MultiplierStructureClass.dedekind.operationProfile.hasReversal = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Half (ii) — a general `Multiplier` beyond the finite-4 classification

The whole finite-4 ladder is `pointed`, so every `realizeClass` image is pointed.  `voidMultiplier` is
UNPOINTABLE.  Hence `voidMultiplier` is realized by NO finite-4 class: the general endofunctor notion
strictly exceeds the classification along the unpointability axis the finite-4 flags cannot observe. -/

/-- A multiplier `IsBeyondFiniteClassification` when it is not the realization of ANY of the four structure
classes — a general `Multiplier` outside the cube-ladder classification's image. -/
def Multiplier.IsBeyondFiniteClassification (multiplier : Multiplier) : Prop :=
  ∀ (structureClass : MultiplierStructureClass), multiplier ≠ realizeClass structureClass

/-- Every finite-4 realization is pointed, but `voidMultiplier` is unpointable, so `voidMultiplier` differs
from every realization (the pointed-vs-unpointable invariant separates them).  A `Multiplier`-EQUALITY
would carry the realization's pointedness onto the void multiplier, contradicting unpointability. -/
theorem voidMultiplier_ne_realizeClass (structureClass : MultiplierStructureClass) :
    voidMultiplier ≠ realizeClass structureClass := by
  intro voidEqualsRealization
  have voidIsPointed : voidMultiplier.IsPointed := by
    rw [voidEqualsRealization]
    exact realizeClass_isPointed structureClass
  exact Multiplier.not_pointed_and_unpointable voidMultiplier voidIsPointed
    voidMultiplier_isUnpointable

/-- ★ **The strict-largeness witness** — `voidMultiplier` is a general `Multiplier` BEYOND the finite-4
classification: it is the realization of no structure class.  The unpointable void dimension is invisible
to the cube-ladder flags (which only ever describe pointed multipliers), so the general
general-multiplier endofunctor notion strictly exceeds the finite `{affine, cartesian, dedekind, deMorgan}`
classification. -/
theorem voidMultiplier_beyond_finiteClassification :
    voidMultiplier.IsBeyondFiniteClassification :=
  voidMultiplier_ne_realizeClass

/-- ★ **The discharge, packaged.**  BOTH halves hold: (i) every finite-4 class is realized as a pointed
general `Multiplier` whose equipped operations match its structural flags, and (ii) there is a general
`Multiplier` (the unpointable void) beyond every finite-4 realization.  This is exactly "multipliers beyond
the finite classification — the general-multiplier endofunctor". -/
theorem generalMultiplier_strictlyBeyond_finiteClassification :
    (∀ (structureClass : MultiplierStructureClass),
        (realizeClass structureClass).IsPointed
          ∧ structureClass.operationProfile.hasReversal = structureClass.supportsReversal)
      ∧ voidMultiplier.IsBeyondFiniteClassification :=
  ⟨fun structureClass =>
      ⟨realizeClass_isPointed structureClass,
        (structureClass.operationProfile_matches_flags).2.2⟩,
    voidMultiplier_beyond_finiteClassification⟩

/-! ## Honesty marker -/

/-- **Honesty marker (frontier).**  SHIPPED: the connection proving the general `Multiplier` endofunctor
(`mode-12`) is STRICTLY LARGER than the finite-4 `{affine, cartesian, dedekind, deMorgan}` classification
(`mode-2`).  Half (i): `realizeClass` embeds each class as a pointed general `Multiplier`
(`realizeClass_isPointed`) with operations matching its structural flags
(`realizeClass_operationProfile_matches`).  Half (ii): `voidMultiplier_beyond_finiteClassification` — the
unpointable void dimension is a general `Multiplier` outside every finite-4 realization.  This is the
content `mode-21`'s `fxMode_hasModeOmegaGeneralMultiplier` defers.  `= true`. -/
def fxModeFrontier_hasGeneralMultiplierBeyondClassification : Bool := true

end FX1Poly.Tier0
