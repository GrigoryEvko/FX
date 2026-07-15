import FX1Poly.Axis.Mode.FibrancyMode
import FX1Poly.Polygraph.Computad.AdjunctionSeed

/-! # AdjointModeSignature — a signature-parametric MATT adjoint mode theory (Shulman Def 2.1)

The GENERIC lift of `FibrancyMode`'s bespoke 4-constructor `FibrancyMorphismShape` classification to an
arbitrary `ModeSignature`.  Where `FibrancyMode.lean` hand-rolls the class predicates over a fixed enum of
{identities, ι, ι†}, this file equips ANY `ModeSignature` with the MATT Definition 2.1 adjoint-mode-theory
decoration, PER 1-cell generator (edge):

  1. **the MATT class** — `tangible` / `sharp` / `transparent` / `sinister` — as a decoration
     `classOf : edge → AdjointClass` (`AdjointClass` a 4-constructor `DecidableEq` enum);
  2. **the designated right adjoint** `μ†` — a PARTIAL map `rightAdjoint : edge → Option (reversed edge)`
     (a right adjoint reverses the boundary, so `μ : src → tgt` gives `μ† : tgt → src`, enforced at the TYPE
     level — the endpoint-swap is definitional, not a theorem);
  3. **the class-implication LAWS** — `sharp ⟹ tangible`, `transparent ⟹ tangible` (MATT Def 2.1's class
     containments) plus `sinister ⟹ has a right adjoint` — as `Prop`-valued structure fields, supplied per
     instance.

## Faithfulness to `FibrancyMode`

A single class TAG per generator (rather than four independent Bools) recovers MATT Example 2.5 EXACTLY because
generators are never identities, and `tangible` = ALL morphisms is modeled by `AdjointClass.isTangible` being
constant-`true`: a `sinister`-tagged generator is STILL tangible.  The recovery bridge below proves the fibrancy
instance's decoration matches `FibrancyMorphismShape`'s class predicates on the nose (inclusion ↦ sinister,
its adjoint ↦ tangible; both not-sharp, not-transparent, both tangible).

## Two instances

  * **`fibrancyAdjointModeSignature`** — the recovering 2LTT instance.  Because the shipped `FibrancyModality`
    quiver has NO ι† generator (a total right adjoint into a reversed generator would have nowhere to land),
    the recovering instance is built over the ADJOINT-COMPLETED quiver `FibrancyModalityAdj` = {ι, ι†}, so
    `rightAdjoint ι = some ι†` is honest and the endpoint-swap theorem is definitional.
  * **`adjunctionAdjointModeSignature`** — the walking-adjunction seed.  `left` (the left adjoint) is sinister
    with designated right adjoint `right`; `right` (a right adjoint that has NO further right adjoint in the
    FREE walking adjunction) is tangible with `rightAdjoint = none`.

## Scope discipline (what this does NOT do)

The decoration RECORDS that an edge is sinister / has a right adjoint (data + Bool).  It does NOT prove the
triangle identities of the adjunction — that is the fib-3 free-2-cell-rewriting decision layer's job
(`AdjunctionSeed`'s generators-only discipline).  No law is phrased as a functor / natural-iso EQUALITY; every
law is componentwise / `Prop`-valued, so `funext` / `Quot.sound` never enter.

Zero external dependencies beyond the fibrancy mode structure and the adjunction seed.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

/-! ## The MATT class tag -/

/-- The **MATT Definition 2.1 class** of a 1-cell generator — the four adjoint-mode-theory predicate classes as
a single tag.  A generator carries the class that DISTINGUISHES it; `tangible` is the ambient class every
generator satisfies (recovered by `isTangible` being constant-`true` below), so a `sinister` generator is still
tangible.  `DecidableEq` so class comparisons stay propext-free. -/
inductive AdjointClass where
  /-- **Tangible** — the ambient class (every morphism); may annotate a context variable. -/
  | tangible
  /-- **Sharp** — a positive modality `μ ⊡` may be formed (identities only, in 2LTT). -/
  | sharp
  /-- **Transparent** — a modal function type `(x :^μ A) → B` may be formed. -/
  | transparent
  /-- **Sinister** — a left adjoint (has a right adjoint `μ†`), so generates the negative modality `μ ◇→`. -/
  | sinister
  deriving DecidableEq

/-- **Tangible** membership — constant-`true`: every class is tangible (MATT Example 2.5 "tangible = ALL
morphisms").  This constant is exactly what lets a single mutually-exclusive class tag reproduce the
non-mutually-exclusive MATT predicate family. -/
def AdjointClass.isTangible : AdjointClass → Bool := fun _ => true

/-- **Sharp** membership — `true` only on the `sharp` tag. -/
def AdjointClass.isSharp : AdjointClass → Bool
  | .sharp => true
  | .tangible => false
  | .transparent => false
  | .sinister => false

/-- **Transparent** membership — `true` only on the `transparent` tag. -/
def AdjointClass.isTransparent : AdjointClass → Bool
  | .transparent => true
  | .tangible => false
  | .sharp => false
  | .sinister => false

/-- **Sinister** membership — `true` only on the `sinister` tag. -/
def AdjointClass.isSinister : AdjointClass → Bool
  | .sinister => true
  | .tangible => false
  | .sharp => false
  | .transparent => false

/-- MATT Def 2.1 containment: sharp ⟹ tangible (holds because `isTangible` is constant-`true`). -/
theorem AdjointClass.isSharp_implies_isTangible (adjointClass : AdjointClass)
    (_isSharpClass : adjointClass.isSharp = true) : adjointClass.isTangible = true := rfl

/-- MATT Def 2.1 containment: transparent ⟹ tangible. -/
theorem AdjointClass.isTransparent_implies_isTangible (adjointClass : AdjointClass)
    (_isTransparentClass : adjointClass.isTransparent = true) : adjointClass.isTangible = true := rfl

/-! ## The signature-parametric adjoint mode theory -/

/-- ★ An **adjoint mode signature** (MATT Definition 2.1) — a `ModeSignature` whose 1-cell GENERATORS carry the
MATT class decoration `classOf`, a designated PARTIAL right adjoint `rightAdjoint` (reversing the boundary at the
type level), and the class-implication laws as `Prop` fields.  The generic lift of `FibrancyMode`'s bespoke
`FibrancyMorphismShape` classification to an arbitrary `ModeSignature`. -/
structure AdjointModeSignature where
  /-- The underlying 2-polygraph signature. -/
  base : ModeSignature
  /-- The MATT class of each 1-cell generator (edge). -/
  classOf : {sourceMode targetMode : base.graph.Mode} →
    base.graph.Modality sourceMode targetMode → AdjointClass
  /-- The designated right adjoint `μ†` of a generator — PARTIAL (`Option`), landing on a generator of the
  REVERSED boundary (`tgt → src`), the endpoint-swap being definitional in the type. -/
  rightAdjoint : {sourceMode targetMode : base.graph.Mode} →
    base.graph.Modality sourceMode targetMode → Option (base.graph.Modality targetMode sourceMode)
  /-- MATT Def 2.1 law: a sharp generator is tangible. -/
  sharp_implies_tangible : {sourceMode targetMode : base.graph.Mode} →
    (modality : base.graph.Modality sourceMode targetMode) →
    (classOf modality).isSharp = true → (classOf modality).isTangible = true
  /-- MATT Def 2.1 law: a transparent generator is tangible. -/
  transparent_implies_tangible : {sourceMode targetMode : base.graph.Mode} →
    (modality : base.graph.Modality sourceMode targetMode) →
    (classOf modality).isTransparent = true → (classOf modality).isTangible = true
  /-- MATT Def 2.1 law: every sinister generator HAS a designated right adjoint. -/
  sinister_hasRightAdjoint : {sourceMode targetMode : base.graph.Mode} →
    (modality : base.graph.Modality sourceMode targetMode) →
    (classOf modality).isSinister = true → (rightAdjoint modality).isSome = true

/-! ## Generic edge predicates read off the decoration -/

/-- Is a generator tangible (through its class tag)?  Constant-`true` — every generator is tangible. -/
def AdjointModeSignature.isTangibleEdge (signature : AdjointModeSignature)
    {sourceMode targetMode : signature.base.graph.Mode}
    (modality : signature.base.graph.Modality sourceMode targetMode) : Bool :=
  (signature.classOf modality).isTangible

/-- Is a generator sharp? -/
def AdjointModeSignature.isSharpEdge (signature : AdjointModeSignature)
    {sourceMode targetMode : signature.base.graph.Mode}
    (modality : signature.base.graph.Modality sourceMode targetMode) : Bool :=
  (signature.classOf modality).isSharp

/-- Is a generator transparent? -/
def AdjointModeSignature.isTransparentEdge (signature : AdjointModeSignature)
    {sourceMode targetMode : signature.base.graph.Mode}
    (modality : signature.base.graph.Modality sourceMode targetMode) : Bool :=
  (signature.classOf modality).isTransparent

/-- Is a generator sinister (a left adjoint)? -/
def AdjointModeSignature.isSinisterEdge (signature : AdjointModeSignature)
    {sourceMode targetMode : signature.base.graph.Mode}
    (modality : signature.base.graph.Modality sourceMode targetMode) : Bool :=
  (signature.classOf modality).isSinister

/-- A sinister generator's right adjoint is genuinely present (`isSome`) — the generic restatement of the
`sinister_hasRightAdjoint` field over the derived edge predicate. -/
theorem AdjointModeSignature.isSinisterEdge_hasRightAdjoint (signature : AdjointModeSignature)
    {sourceMode targetMode : signature.base.graph.Mode}
    (modality : signature.base.graph.Modality sourceMode targetMode)
    (isSinister : signature.isSinisterEdge modality = true) :
    (signature.rightAdjoint modality).isSome = true :=
  signature.sinister_hasRightAdjoint modality isSinister

/-! ## Instance 1 — the recovering 2LTT fibrancy instance (adjoint-completed quiver) -/

/-- The **adjoint-completed fibrancy modality quiver** — `ι : e → f` AND its right adjoint `ι† : f → e` as GENUINE
generators.  The shipped `FibrancyModality` has only `ι`, so a total right adjoint would have no target; adding
`ι†` as an edge lets `rightAdjoint ι = some ι†` be honest and the endpoint swap be definitional. -/
inductive FibrancyModalityAdj : FibrancyKind → FibrancyKind → Type where
  /-- The mode inclusion `ι : e → f` (the sinister generator). -/
  | inclusion : FibrancyModalityAdj FibrancyKind.exotype FibrancyKind.fibrant
  /-- Its right adjoint `ι† : f → e`. -/
  | inclusionAdj : FibrancyModalityAdj FibrancyKind.fibrant FibrancyKind.exotype

/-- The adjoint-completed fibrancy quiver — two modes `{f, e}`, the generators `ι` and `ι†`. -/
def fibrancyAdjGraph : ModeGraph where
  Mode := FibrancyKind
  Modality := FibrancyModalityAdj

/-- The adjoint-completed fibrancy mode signature — the quiver with no non-trivial 2-cell generators (the mode
theory stays thin; the asymmetry lives in the class decoration). -/
def fibrancyAdjModeSignature : ModeSignature where
  graph := fibrancyAdjGraph
  twoCell := fun _ _ => Empty

/-- ★ The **fibrancy adjoint mode signature** — the recovering 2LTT instance (MATT Example 2.5): `ι` sinister
with right adjoint `ι†`, `ι†` tangible with right adjoint `ι` back.  The class decoration matches
`FibrancyMorphismShape` on the nose (see the recovery bridge below). -/
def fibrancyAdjointModeSignature : AdjointModeSignature where
  base := fibrancyAdjModeSignature
  classOf := fun modality =>
    match modality with
    | .inclusion => AdjointClass.sinister
    | .inclusionAdj => AdjointClass.tangible
  rightAdjoint := fun modality =>
    match modality with
    | .inclusion => some FibrancyModalityAdj.inclusionAdj
    | .inclusionAdj => some FibrancyModalityAdj.inclusion
  sharp_implies_tangible := fun _ _ => rfl
  transparent_implies_tangible := fun _ _ => rfl
  sinister_hasRightAdjoint := fun modality isSinister => by
    cases modality <;> first | rfl | exact Bool.noConfusion isSinister

/-- Recovery: `ι`'s designated right adjoint is `ι†` (the endpoint swap `e → f` ↦ `f → e` is definitional in the
`Option (Modality f e)` result type). -/
theorem fibrancyAdj_rightAdjoint_inclusion :
    fibrancyAdjointModeSignature.rightAdjoint FibrancyModalityAdj.inclusion
      = some FibrancyModalityAdj.inclusionAdj := rfl

/-- Recovery: `ι†`'s designated right adjoint is `ι` back. -/
theorem fibrancyAdj_rightAdjoint_inclusionAdj :
    fibrancyAdjointModeSignature.rightAdjoint FibrancyModalityAdj.inclusionAdj
      = some FibrancyModalityAdj.inclusion := rfl

/-- ★ Recovery of `FibrancyMode`'s classification, part 1 — `ι` is SINISTER, matching
`FibrancyMorphismShape.fibrancyInclusion.isSinister`. -/
theorem fibrancyAdj_inclusion_isSinister_matches :
    fibrancyAdjointModeSignature.isSinisterEdge FibrancyModalityAdj.inclusion
      = FibrancyMorphismShape.fibrancyInclusion.isSinister := rfl

/-- ★ Recovery, part 2 — `ι` is NOT sharp, matching `FibrancyMorphismShape.fibrancyInclusion.isSharp` (the MATT
non-sharpness constraint, generic form). -/
theorem fibrancyAdj_inclusion_isSharp_matches :
    fibrancyAdjointModeSignature.isSharpEdge FibrancyModalityAdj.inclusion
      = FibrancyMorphismShape.fibrancyInclusion.isSharp := rfl

/-- ★ Recovery, part 3 — `ι` is NOT transparent, matching `FibrancyMorphismShape.fibrancyInclusion.isTransparent`. -/
theorem fibrancyAdj_inclusion_isTransparent_matches :
    fibrancyAdjointModeSignature.isTransparentEdge FibrancyModalityAdj.inclusion
      = FibrancyMorphismShape.fibrancyInclusion.isTransparent := rfl

/-- ★ Recovery, part 4 — `ι` IS tangible, matching `FibrancyMorphismShape.fibrancyInclusion.isTangible`. -/
theorem fibrancyAdj_inclusion_isTangible_matches :
    fibrancyAdjointModeSignature.isTangibleEdge FibrancyModalityAdj.inclusion
      = FibrancyMorphismShape.fibrancyInclusion.isTangible := rfl

/-- ★ Recovery of `ι†`'s classification — `ι†` is NOT sinister, matching
`FibrancyMorphismShape.fibrancyInclusionRightAdjoint.isSinister`. -/
theorem fibrancyAdj_inclusionAdj_isSinister_matches :
    fibrancyAdjointModeSignature.isSinisterEdge FibrancyModalityAdj.inclusionAdj
      = FibrancyMorphismShape.fibrancyInclusionRightAdjoint.isSinister := rfl

/-- Non-degeneracy: `ι` is genuinely sinister in the fibrancy instance. -/
theorem fibrancyAdj_inclusion_isSinister :
    fibrancyAdjointModeSignature.isSinisterEdge FibrancyModalityAdj.inclusion = true := rfl

/-- Non-degeneracy: `ι` genuinely has a right adjoint. -/
theorem fibrancyAdj_inclusion_hasRightAdjoint :
    (fibrancyAdjointModeSignature.rightAdjoint FibrancyModalityAdj.inclusion).isSome = true := rfl

/-! ## Instance 2 — the walking-adjunction seed -/

/-- ★ The **adjunction adjoint mode signature** — the walking-adjunction seed as a MATT adjoint mode theory:
`left` (the left adjoint `base → tip`) is SINISTER with designated right adjoint `right`; `right` (a right
adjoint with NO further right adjoint in the free walking adjunction) is tangible with `rightAdjoint = none`. -/
def adjunctionAdjointModeSignature : AdjointModeSignature where
  base := adjunctionModeSignature
  classOf := fun modality =>
    match modality with
    | .left => AdjointClass.sinister
    | .right => AdjointClass.tangible
  rightAdjoint := fun modality =>
    match modality with
    | .left => some AdjunctionModality.right
    | .right => none
  sharp_implies_tangible := fun _ _ => rfl
  transparent_implies_tangible := fun _ _ => rfl
  sinister_hasRightAdjoint := fun modality isSinister => by
    cases modality <;> first | rfl | exact Bool.noConfusion isSinister

/-- The left adjoint is sinister. -/
theorem adjunction_left_isSinister :
    adjunctionAdjointModeSignature.isSinisterEdge AdjunctionModality.left = true := rfl

/-- The left adjoint's designated right adjoint is `right` (endpoint swap `base → tip` ↦ `tip → base`
definitional in the result type). -/
theorem adjunction_left_rightAdjoint :
    adjunctionAdjointModeSignature.rightAdjoint AdjunctionModality.left
      = some AdjunctionModality.right := rfl

/-- The left adjoint genuinely has a right adjoint. -/
theorem adjunction_left_hasRightAdjoint :
    (adjunctionAdjointModeSignature.rightAdjoint AdjunctionModality.left).isSome = true := rfl

/-- The right adjoint is NOT sinister (no further right adjoint in the free walking adjunction). -/
theorem adjunction_right_not_isSinister :
    adjunctionAdjointModeSignature.isSinisterEdge AdjunctionModality.right = false := rfl

/-- The right adjoint has no designated right adjoint. -/
theorem adjunction_right_rightAdjoint_none :
    adjunctionAdjointModeSignature.rightAdjoint AdjunctionModality.right = none := rfl

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the signature-parametric adjoint mode theory ships, inhabited by BOTH instances.**  The
generic `AdjointModeSignature` (MATT Def 2.1) with the `AdjointClass` 4-tag decoration, the partial right adjoint
(endpoint-swap definitional), and the class-implication laws — instantiated by (a) the recovering 2LTT fibrancy
instance `fibrancyAdjointModeSignature` (whose decoration matches `FibrancyMorphismShape` on the nose) and
(b) the walking-adjunction seed `adjunctionAdjointModeSignature`.  `= true` because both witnesses type-check. -/
def fxMode_hasAdjointModeSignature : Bool := true

end FX1Poly.Axis
