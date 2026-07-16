import FX1Poly.Axis.Mode.Mode
import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility

/-! # FX1Poly/Typed/Fib/ModeLockPath — fib-3b: the bespoke ObligationModality as a mode-axis ModalityPath

fib-3a/3c presented the affine dimension lock in the mode axis's MULTIPLIER form (mode-12 `voidMultiplier`:
unpointable + split, with the kernel's fibrant-inaccessibility DERIVED from unpointedness).  This file presents
the SAME affine modality in the mode axis's POLYGRAPH form (`ModeGraph` / `ModalityPath`, mode-0) and maps the
kernel's bespoke `ObligationModality {fibrant, dimensional}` onto it — the translation that retires the enum
onto the real free-modality 1-cells (the `fib-3d` retirement consumes it).

The affine dimension modality has a minimal POLYGRAPH presentation: ONE mode (the dimension mode) with ONE
generating modality (the affine lock generator — semantically the mode-12 void multiplier of fib-3a).  The
bespoke `ObligationModality` is then two specific 1-cells over this graph:

  * `fibrant`     ↦ the IDENTITY path (no modality — the unlocked / fibrant access);
  * `dimensional` ↦ the affine generator path (one application of the lock generator — the locked / dimensional
    access).

The translation is INJECTIVE (distinct modalities map to distinct-LENGTH paths: `0` vs `1`), so the bespoke
enum embeds FAITHFULLY into the mode-axis `ModalityPath` over the affine dimension graph — the genuine
retirement target for the bespoke `ObligationModality`.

## Zero-axiom

A `ModeGraph` over `Unit`, two `ModalityPath` constructors, `rfl` lengths, and a `cases` + `decide`-length
injectivity.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Axis FX1Poly.Typed FX1Poly.Core
open FX1Poly.Polygraph

/-- The minimal POLYGRAPH presentation of the affine dimension modality: ONE mode (the dimension mode) with ONE
generating modality (the affine lock generator, semantically the mode-12 void multiplier of fib-3a). -/
def dimensionUsePositionModeGraph : ModeGraph where
  Mode := Unit
  Modality := fun _ _ => Unit

/-- The single dimension mode of the affine graph. -/
def dimensionUsePositionMode : dimensionUsePositionModeGraph.Mode := ()

/-- The affine lock generator — the single 1-cell generator of the dimension mode graph (the polygraph face of
the mode-12 void multiplier). -/
def affineLockGenerator : dimensionUsePositionModeGraph.Modality dimensionUsePositionMode dimensionUsePositionMode := ()

/-- ★ **fib-3b: the bespoke `ObligationModality` as a mode-axis `ModalityPath`.**  `fibrant` is the IDENTITY
1-cell (no modality — unlocked / fibrant access); `dimensional` is the affine generator path (one lock
application — dimensional access).  Embeds the kernel's bespoke 2-element enum into the mode axis's
free-modality 1-cells over the affine dimension graph. -/
def obligationModalityToPath :
    ObligationModality → ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode
  | .fibrant => identityPath dimensionUsePositionMode
  | .dimensional => ModalityPath.cons affineLockGenerator (identityPath dimensionUsePositionMode)

/-- The fibrant access mode maps to the IDENTITY path (length `0`). -/
theorem obligationModalityToPath_fibrant_length :
    (obligationModalityToPath .fibrant).length = 0 := rfl

/-- The dimensional access mode maps to the affine generator path (length `1`). -/
theorem obligationModalityToPath_dimensional_length :
    (obligationModalityToPath .dimensional).length = 1 := rfl

/-- ★ The translation is INJECTIVE: distinct `ObligationModality`s map to distinct `ModalityPath`s, refuted by
their distinct path lengths (`0` vs `1`).  So the bespoke enum embeds FAITHFULLY into the mode-axis
`ModalityPath` — the genuine retirement target. -/
theorem obligationModalityToPath_injective {firstModality secondModality : ObligationModality}
    (pathsEqual : obligationModalityToPath firstModality = obligationModalityToPath secondModality) :
    firstModality = secondModality := by
  cases firstModality <;> cases secondModality <;>
    first
      | rfl
      | exact absurd (congrArg ModalityPath.length pathsEqual) (by decide)

/-! ## fib-3d: the decidable DIMENSION-1 word problem for the kernel's affine mode (1-cell equality)

★★ HONESTY (do NOT conflate the two dimensions).  Gratzer's "Conv-dec = mode-dec" keystone is at DIMENSION 2:
modal-type conversion is decidable iff mode **2-cell** equality is decidable (`fxMode_hasDecidableTwoCellEquality`
/ `fxMode_hasModeRelativeConvDecision`, a convergent 3-polygraph deciding `TwoCellConv` modulo the modality's
adjunction triangle identities — still DEFERRED, even for the affine mode).  What THIS file decides is at
DIMENSION 1: equality of 1-cells (modality PATHS) over the affine graph.  Dimension-1 decidability is NECESSARY
for, but NOT SUFFICIENT for, the keystone — and it is moreover ALREADY available generally as the mode axis's
`decidableOneCellEq` (`TwoCategoryCore`); what is below is the affine-graph instance of that dimension-1 fact,
used by the fib-3 fibration capstone, NOT the dimension-2 mode-dec.

The affine dimension polygraph (`dimensionUsePositionModeGraph`): ONE mode, ONE generator, NO 2-cell relations — the
FREE category on a single generator; its 1-cells (`ModalityPath`s) are determined by length, so the
DIMENSION-1 word problem is `DecidableEq Nat` in disguise.  The dimension-2 word problem (deciding the affine
mode's 2-cells) is the genuine remaining keystone work. -/

/-- Length injectivity for the affine mode's 1-cells, over ARBITRARY (mode-)endpoints — the form whose source
and target are variables, so `induction` on the path is legal.  Both endpoints are `Unit` so they are forced to
`()`, but quantifying keeps them free for the recursor.  The hard direction (`length equal → path equal`): the
cross `nil`/`cons` cases are refuted by their `0`-vs-`n+1` lengths (`Nat`-level, propext-free), and the
`cons`/`cons` case strips one generator (both `()` by `Unit` eta, so generators and middle modes coincide
definitionally) and recurses on the tails. -/
theorem affineModalityPath_length_injective_overEndpoints :
    ∀ {sourceMode targetMode : dimensionUsePositionModeGraph.Mode}
      (firstPath secondPath : ModalityPath dimensionUsePositionModeGraph sourceMode targetMode),
      firstPath.length = secondPath.length → firstPath = secondPath := by
  intro sourceMode targetMode firstPath
  induction firstPath with
  | nil _ =>
      intro secondPath lengthsEqual
      cases secondPath with
      | nil _ => rfl
      | cons _ restSecond =>
          exact Nat.noConfusion (show (0 : Nat) = restSecond.length + 1 from lengthsEqual)
  | cons firstGenerator restFirst inductiveHypothesis =>
      intro secondPath lengthsEqual
      cases secondPath with
      | nil _ =>
          exact Nat.noConfusion (show restFirst.length + 1 = (0 : Nat) from lengthsEqual)
      | cons secondGenerator restSecond =>
          have restsEqual : restFirst = restSecond :=
            inductiveHypothesis restSecond (Nat.succ.inj lengthsEqual)
          cases restsEqual
          rfl

/-- ★ **Length injectivity for the affine mode's 1-cells** (the kernel's mode endpoints).  Two `ModalityPath`s
over the affine dimension graph are equal iff they have the same length — the free-category-on-one-generator
word problem.  Specializes `affineModalityPath_length_injective_overEndpoints` to the kernel's single mode. -/
theorem affineModalityPath_length_injective
    (firstPath secondPath :
        ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode)
    (lengthsEqual : firstPath.length = secondPath.length) : firstPath = secondPath :=
  affineModalityPath_length_injective_overEndpoints firstPath secondPath lengthsEqual

/-- ★ **fib-3d: the kernel's affine mode theory has DECIDABLE DIMENSION-1 (1-cell / modality) equality** — the
decidable dimension-1 word problem.  Decided by comparing path lengths (`Nat.decEq`) and transporting along
`affineModalityPath_length_injective`.  Propext-free: `Nat.decEq` plus the length-injectivity recursion.
HONESTY: this is DIMENSION 1, NOT Gratzer's dimension-2 "mode-dec" (`fxMode_hasDecidableTwoCellEquality`, the
decidable 2-CELL equality), which stays deferred; dimension-1 is also generally available as the mode axis's
`decidableOneCellEq`, and this is the affine-graph instance. -/
instance affineModalityPathDecidableEq :
    DecidableEq (ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode) :=
  fun firstPath secondPath =>
    match Nat.decEq firstPath.length secondPath.length with
    | isTrue lengthsEqual =>
        isTrue (affineModalityPath_length_injective firstPath secondPath lengthsEqual)
    | isFalse lengthsDistinct =>
        isFalse (fun pathsEqual => lengthsDistinct (congrArg ModalityPath.length pathsEqual))

/-! ## A1-MODE-SEAL: the engine's accessibility IS the mode-axis free-category 2-cell existence

The kernel's structural accessibility check (`TypingContext.isAccessibleAtModality`, the engine's
`DimensionLockAccessibility`) decides — for the single affine lock — exactly the DIMENSION-1 word problem over
the affine mode graph: a variable is usable at `modality` iff its USE-modality PATH (`obligationModalityToPath
modality`) equals its BINDING-modality PATH (`bindingModalityPath context index`).  Over the FREE category on one
generator the only 2-cells are identities, so 2-cell existence collapses to PATH EQUALITY
(`affineModalityPathDecidableEq`).  This is the genuine fib-3 seal — the kernel's decidable accessibility IS the
mode theory's check, the `locks(Delta) = id` specialization of MTT's use-modality variable rule
`alpha : nu ==> mu . locks(Delta)`.  HONESTY: dimension-1 (1-cell equality), NOT Gratzer's dimension-2 mode-dec
(`fxMode_hasDecidableTwoCellEquality`, still deferred). -/

/-- The BINDING modality of `index` as a mode-axis path: a plain `cons` binds at the IDENTITY 1-cell (an
ordinary fibrant value), a `lockCons` binds at the affine generator (the locked dimension).  Walks the context
telescope with EXACTLY the recursion shape of `isFibrantlyAccessibleAt` / `isDimensionallyAccessibleAt`. -/
def bindingModalityPath {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Fin scope →
      ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode
  | _, .empty, emptyIndex => absurd emptyIndex.isLt (Nat.not_lt_zero emptyIndex.val)
  | _, .cons _ _, ⟨0, _⟩ => identityPath dimensionUsePositionMode
  | _, .lockCons _ _, ⟨0, _⟩ => ModalityPath.cons affineLockGenerator (identityPath dimensionUsePositionMode)
  | _, .cons restContext _, ⟨position + 1, isLtSucc⟩ =>
      bindingModalityPath restContext ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩
  | _, .lockCons restContext _, ⟨position + 1, isLtSucc⟩ =>
      bindingModalityPath restContext ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-- Fibrant half of the seal: a variable is fibrantly accessible iff its binding-modality path is the IDENTITY
path (its binding is a `cons`), since `obligationModalityToPath .fibrant = identityPath`.  Structural recursion
matching the telescope walk; the two leaves compute the decidable path equality (lengths `0`=`0` vs `0`!=`1`). -/
theorem isFibrantlyAccessibleAt_eq_identityPathEq {profile : PolyProfile} :
    ∀ {scope : Nat} (context : TypingContext profile scope) (index : Fin scope),
      context.isFibrantlyAccessibleAt index
        = decide (obligationModalityToPath .fibrant = bindingModalityPath context index)
  | _, .empty, emptyIndex => absurd emptyIndex.isLt (Nat.not_lt_zero emptyIndex.val)
  | _, .cons _ _, ⟨0, _⟩ => rfl
  | _, .lockCons _ _, ⟨0, _⟩ => rfl
  | _, .cons restContext _, ⟨position + 1, isLtSucc⟩ =>
      isFibrantlyAccessibleAt_eq_identityPathEq restContext ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩
  | _, .lockCons restContext _, ⟨position + 1, isLtSucc⟩ =>
      isFibrantlyAccessibleAt_eq_identityPathEq restContext ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-- Dimensional half of the seal: a variable is dimensionally accessible iff its binding-modality path is the
affine GENERATOR path (its binding is a `lockCons`), since `obligationModalityToPath .dimensional =
ModalityPath.cons affineLockGenerator identityPath`.  The structural dual of the fibrant half. -/
theorem isDimensionallyAccessibleAt_eq_generatorPathEq {profile : PolyProfile} :
    ∀ {scope : Nat} (context : TypingContext profile scope) (index : Fin scope),
      context.isDimensionallyAccessibleAt index
        = decide (obligationModalityToPath .dimensional = bindingModalityPath context index)
  | _, .empty, emptyIndex => absurd emptyIndex.isLt (Nat.not_lt_zero emptyIndex.val)
  | _, .cons _ _, ⟨0, _⟩ => rfl
  | _, .lockCons _ _, ⟨0, _⟩ => rfl
  | _, .cons restContext _, ⟨position + 1, isLtSucc⟩ =>
      isDimensionallyAccessibleAt_eq_generatorPathEq restContext ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩
  | _, .lockCons restContext _, ⟨position + 1, isLtSucc⟩ =>
      isDimensionallyAccessibleAt_eq_generatorPathEq restContext ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-- ★ **A1-MODE-SEAL (the fib-3 seal).**  The kernel's decidable accessibility check IS the mode-axis
free-category 2-cell existence: `var k` is usable at `modality` iff its use-modality path equals its
binding-modality path over the affine dimension graph.  The `locks(Delta) = id` specialization of MTT's
use-modality variable rule, with 2-cell existence = path equality (free category on one generator).  Both halves
are context-derived, decided by `affineModalityPathDecidableEq` — the engine's `isAccessibleAtModality` is the
mode theory's dimension-1 check, on the nose. -/
theorem isAccessibleAtModality_eq_pathEq {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) (modality : ObligationModality) :
    context.isAccessibleAtModality index modality
      = decide (obligationModalityToPath modality = bindingModalityPath context index) := by
  cases modality with
  | fibrant => exact isFibrantlyAccessibleAt_eq_identityPathEq context index
  | dimensional => exact isDimensionallyAccessibleAt_eq_generatorPathEq context index

/-! ## A1-RETIRE: the retraction — the bespoke enum is RECOVERED from its mode-axis 1-cell

The embedding `obligationModalityToPath` is injective (`obligationModalityToPath_injective`), i.e. a
MONOMORPHISM.  This section upgrades that to a genuine RETRACT: a computable inverse `pathToObligationModality`
on the image, with `pathToObligationModality ∘ obligationModalityToPath = id`.  A split monomorphism loses NO
information in EITHER direction on the staged image, which is the precise sense in which the 2-element enum is
RETIRED onto the free-modality 1-cells: the discipline can be carried entirely on the mode axis (a `ModalityPath`)
and the enum re-derived on demand.  The retraction reads a path's HEAD — the identity path is `fibrant`, any
generator-headed path is `dimensional` (over the affine graph every non-identity 1-cell is one lock application,
so length ≥ 1 is exactly `dimensional`). -/

/-- ★ **The retraction (A1-RETIRE).**  Recover the bespoke `ObligationModality` from a mode-axis 1-cell over the
affine dimension graph: the IDENTITY path (`nil`, no lock) is `fibrant`; any generator-headed path (`cons`, a
lock application) is `dimensional`.  Total structural match on `ModalityPath` — propext-free. -/
def pathToObligationModality :
    ModalityPath dimensionUsePositionModeGraph dimensionUsePositionMode dimensionUsePositionMode → ObligationModality
  | .nil _ => .fibrant
  | .cons _ _ => .dimensional

/-- ★ **The embedding is a SPLIT MONO (faithful retract).**  `pathToObligationModality` is a left inverse of
`obligationModalityToPath`: recovering the enum from its staged path returns the original modality.  Together
with `obligationModalityToPath_injective` this makes the enum-to-path translation a genuine retract — the enum
carries no information beyond its image among the affine 1-cells, so it may be RETIRED onto the mode axis. -/
theorem pathToObligationModality_obligationModalityToPath (modality : ObligationModality) :
    pathToObligationModality (obligationModalityToPath modality) = modality := by
  cases modality <;> rfl

/-- The staged image is length-bounded: every `obligationModalityToPath` value is a 1-cell of length at most one
(the identity path or a single lock application).  So the bespoke enum populates exactly the affine graph's
1-cells of word length `≤ 1` — the retirement's image characterization. -/
theorem obligationModalityToPath_length_le_one (modality : ObligationModality) :
    (obligationModalityToPath modality).length ≤ 1 := by
  cases modality with
  | fibrant => exact Nat.zero_le 1
  | dimensional => exact Nat.le_refl 1

/-! ## A1-RETIRE: the RETIRED accessibility function — the discipline carried on the mode axis

`isAccessibleViaModeAxis` is the mode-axis-native replacement for the engine's bespoke
`TypingContext.isAccessibleAtModality`: it decides use-site accessibility purely by comparing 1-cells over the
affine dimension graph — the USE-modality path (`obligationModalityToPath modality`) against the BINDING-modality
path (`bindingModalityPath context index`), decided by `affineModalityPathDecidableEq`.  The A1-MODE-SEAL
(`isAccessibleAtModality_eq_pathEq`) proves the enum-based engine check EQUALS this mode-axis function ON THE
NOSE, so consumers may be routed through `isAccessibleViaModeAxis` and the enum retired to a mere finite index
into the two staged 1-cells.  This is the Route-B retirement: no consumer proof changes (the two functions are
provably equal), yet the discipline now lives on the real free-modality axis. -/

/-- ★ **The RETIRED accessibility check.**  Decide whether the variable `index` is usable at `modality` purely on
the mode axis: the use-modality 1-cell equals the binding-modality 1-cell over the affine dimension graph.
The mode-axis-native replacement for the bespoke `TypingContext.isAccessibleAtModality`. -/
def isAccessibleViaModeAxis {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) (modality : ObligationModality) : Bool :=
  decide (obligationModalityToPath modality = bindingModalityPath context index)

/-- ★ **The engine check IS the retired mode-axis check.**  `TypingContext.isAccessibleAtModality` equals
`isAccessibleViaModeAxis` on the nose (the A1-MODE-SEAL, repackaged as a function equation).  So every consumer
of the bespoke enum-based accessibility can be routed through the mode-axis 1-cell comparison with NO change to
its proof — the enum is retired to an index into the affine graph's length-`≤ 1` 1-cells. -/
theorem isAccessibleAtModality_eq_isAccessibleViaModeAxis {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) (modality : ObligationModality) :
    context.isAccessibleAtModality index modality = isAccessibleViaModeAxis context index modality :=
  isAccessibleAtModality_eq_pathEq context index modality

end FX1Poly.Core.Fib
