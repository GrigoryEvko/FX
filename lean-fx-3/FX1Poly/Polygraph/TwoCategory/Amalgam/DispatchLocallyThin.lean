import FX1Poly.Polygraph.TwoCategory.Amalgam.Witness
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjointStrings

/-! # Polygraph/TwoCategory/Amalgam/DispatchLocallyThin — the locally-thin component decider + the
doubly-thin dispatch (WP-AMALG-2, LEG A partial + LEG B fragment)

`Dispatch.lean` STATED the categorical Nelson-Oppen dispatch (`DispatchDecidability`) but left its four
fields — two component `DecidableTwoCellConvFor` deciders, the disjointness precondition, and the combined
decider — uninhabited (`fxAmalg_hasDispatchTheorem = false`).  This file ships the FIRST genuine inhabitants,
for the fragment where the arithmetic actually closes ZERO-AXIOM.

## The exact frontier (what closes, and the wall the rest hits)

The decider interface `DecidableTwoCellConvFor signature` decides the FREE 2-cell convertibility `TwoCellConv`
(`FreeTwoCell/Model.lean`): the reflexive-symmetric-transitive closure of the strict-2-category structural
laws (`vcompId`, `vcompAssoc`, `whiskerId`, `whiskerVcomp`, `interchange`) closed under congruence.  Crucially
`TwoCellConv` mentions the signature's generating 2-cells ONLY as opaque `gen` atoms — it carries NO
doctrine-specific relations.  Two consequences pin the frontier:

  * **Any signature with GENERATING 2-cells forces the FREE decision into the open convergence hurdle.**  The
    structural laws critical-pair against each other (interchange vs `whiskerVcomp`) regardless of which
    generators exist, so deciding `TwoCellConv` in general needs the confluence proof
    (`fxMode_hasConvergentThreeCellSystem = false`, mode-9 / Gratzer).  The shipped walking-doctrine decisions
    (idempotent thinness, KZ Delta-fold, involution parity) decide a strictly LARGER, doctrine-SATURATED
    relation — a different word problem the free `DecidableTwoCellConvFor` interface does not carry.  This is
    LEG A's honest wall: no shipped walker decision is typed as `DecidableTwoCellConvFor _.toModeSignature`.

  * **A signature with NO generating 2-cells is LOCALLY THIN: every parallel 2-cell pair is convertible.**
    With no `gen` atoms, every free 2-cell is a structural composite of identities and whiskerings; each such
    cell collapses to the identity on its (necessarily equal) boundary (`collapseToId`), so ALL parallel cells
    are mutually convertible (`allParallelConv_of_noGen`).  The relation is TOTAL, so `DecidableTwoCellConvFor`
    is `isTrue` with a genuine `TwoCellConv` proof — NO convergence needed.  This is the exact zero-axiom
    frontier: the relation is trivial precisely when there are no generators, which is precisely when the
    convergence hurdle vanishes.

## What ships here (each piece zero-axiom, structural, ASCII-only)

  * **`idTo`** — the identity 2-cell transported along a boundary equality (the `Eq.rec` cast the collapse needs).
  * **`boundaryEq_of_noGen`** — in a no-2-generator signature, a free 2-cell's boundary paths are EQUAL
    (structural induction: `gen` is absurd, `id` is `rfl`, composites chain the boundary equalities).
  * **`collapseToId`** — every no-generator free 2-cell converts to the transported identity on its boundary
    (structural induction, discharging each composite via the shipped `TwoCellConv` congruences + the
    `vcompId` / `whiskerId` collapse steps).
  * **`allParallelConv_of_noGen`** + **`locallyThinDecider`** — local thinness, and hence the FIRST genuine
    `DecidableTwoCellConvFor _.toModeSignature` (LEG A for no-2-gen components).
  * **`involutionThinDecider`** — the walking-involution component's decider (its `s.s = id` law is 1-cell
    level, so `twoCellGenerators = []`), the concrete LEG-A inhabitant.
  * **`locallyThinDispatch`** — `DispatchDecidability` INHABITED for two locally-thin components: both component
    deciders are locally thin, the pushout inherits no 2-generators so its combined decider is locally thin
    too, and the disjointness precondition holds vacuously.  This is the LEG-B dispatch fragment that closes.
  * **`mixedThinPair` + `mixedThinVerdict`** — a genuine MIXED 2-cell pair over the real thin pushout (boundary
    over both components' letters, two DISTINCT expressions), decided `isTrue` by the combined decider and
    `#eval`'d to a Bool (LEG C, the reachable direction).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

/-! ## The transported identity -/

/-- The identity 2-cell on `sourcePath`, transported along a boundary equality `sourcePath = targetPath` into a
2-cell of boundary `sourcePath ⇒ targetPath`.  Explicit-motive `Eq.rec` (propext-free); reduces to
`RawTwoCellExpr.id` on `rfl`. -/
def idTo {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (boundaryEqual : sourcePath = targetPath) : RawTwoCellExpr signature sourcePath targetPath :=
  Eq.rec (motive := fun candidatePath _ => RawTwoCellExpr signature sourcePath candidatePath)
    (RawTwoCellExpr.id sourcePath) boundaryEqual

/-- `idTo` on a reflexivity proof IS the plain identity — the reduction anchor. -/
theorem idTo_rfl {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {path : ModalityPath signature.graph sourceMode targetMode} :
    idTo (signature := signature) (Eq.refl path) = RawTwoCellExpr.id path := rfl

/-! ## Boundary collapse: a no-generator 2-cell has equal source and target paths -/

/-- **The no-generating-2-cell hypothesis** — the signature's generating-2-cell family is uniformly empty.  The
walking-involution's `toModeSignature` satisfies it (its `s.s = id` relation is 1-cell level, so
`twoCellGenerators = []`). -/
abbrev SignatureHasNoTwoGen (signature : ModeSignature) : Prop :=
  {sourceMode targetMode : signature.graph.Mode} →
  (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
  signature.twoCell sourcePath targetPath → False

/-- In a no-generating-2-cell signature, every free 2-cell has EQUAL source and target paths: with no `gen`
atoms, `id` fixes the boundary, `vcomp` chains it, and whiskerings preserve it under `composePath`.  Structural
induction. -/
theorem boundaryEq_of_noGen {signature : ModeSignature} (noGen : SignatureHasNoTwoGen signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : sourcePath = targetPath := by
  induction cell with
  | gen generator => exact (noGen _ _ generator).elim
  | id _ => rfl
  | vcomp _ _ ihLeft ihRight => exact ihLeft.trans ihRight
  | whiskerLeft oneCell _ ihBody => exact congrArg (composePath oneCell) ihBody
  | whiskerRight oneCell _ ihBody => exact congrArg (fun path => composePath path oneCell) ihBody

/-! ## The collapse steps: a transported identity absorbs its neighbours -/

/-- A vertical composite of two transported identities collapses to a single transported identity.  Both
boundary equalities substituted, the composite is `vcomp (id _) (id _)` and the `vcompIdLeft` 3-cell fires. -/
theorem vcompIdCollapse {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (leftEqual : oneCellF = oneCellG) (rightEqual : oneCellG = oneCellH) :
    TwoCellConv signature (RawTwoCellExpr.vcomp (idTo leftEqual) (idTo rightEqual))
      (idTo (leftEqual.trans rightEqual)) := by
  subst rightEqual
  subst leftEqual
  exact TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id oneCellF))

/-- A left whiskering of a transported identity collapses to a transported identity (`whiskerLeftId`). -/
theorem whiskerLeftIdCollapse {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    (bodyEqual : oneCellG = oneCellH) :
    TwoCellConv signature (RawTwoCellExpr.whiskerLeft oneCell (idTo bodyEqual))
      (idTo (congrArg (composePath oneCell) bodyEqual)) := by
  subst bodyEqual
  exact TwoCellConv.ofStep (TwoCellStep.whiskerLeftId oneCell oneCellG)

/-- A right whiskering of a transported identity collapses to a transported identity (`whiskerRightId`). -/
theorem whiskerRightIdCollapse {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (bodyEqual : oneCellF = oneCellG) :
    TwoCellConv signature (RawTwoCellExpr.whiskerRight oneCell (idTo bodyEqual))
      (idTo (congrArg (fun path => composePath path oneCell) bodyEqual)) := by
  subst bodyEqual
  exact TwoCellConv.ofStep (TwoCellStep.whiskerRightId oneCellF oneCell)

/-! ## Every no-generator 2-cell converts to the identity on its boundary -/

/-- **Collapse to identity** — in a no-generating-2-cell signature every free 2-cell is convertible to the
transported identity on its boundary.  Structural induction, each composite discharged by the shipped
`TwoCellConv` congruences (`vcompCongrLeft/Right`, `whisker{Left,Right}Congr`) followed by the matching
collapse step; the `id` case rewrites the boundary proof to `rfl` (proof irrelevance). -/
theorem collapseToId {signature : ModeSignature} (noGen : SignatureHasNoTwoGen signature) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (cell : RawTwoCellExpr signature sourcePath targetPath) →
    (boundaryEqual : sourcePath = targetPath) →
    TwoCellConv signature cell (idTo boundaryEqual) := by
  intro sourceMode targetMode sourcePath targetPath cell
  induction cell with
  | gen generator => intro _; exact (noGen _ _ generator).elim
  | id path =>
      intro boundaryEqual
      have proofIsRfl : boundaryEqual = Eq.refl path := rfl
      rw [proofIsRfl]
      exact TwoCellConv.refl _
  | vcomp cellLeft cellRight ihLeft ihRight =>
      intro _
      have leftEqual := boundaryEq_of_noGen noGen cellLeft
      have rightEqual := boundaryEq_of_noGen noGen cellRight
      exact TwoCellConv.trans
        (TwoCellConv.trans
          (TwoCellConv.vcompCongrLeft cellRight (ihLeft leftEqual))
          (TwoCellConv.vcompCongrRight (idTo leftEqual) (ihRight rightEqual)))
        (vcompIdCollapse leftEqual rightEqual)
  | whiskerLeft oneCell cellBody ihBody =>
      intro _
      have bodyEqual := boundaryEq_of_noGen noGen cellBody
      exact TwoCellConv.trans
        (TwoCellConv.whiskerLeftCongr oneCell (ihBody bodyEqual))
        (whiskerLeftIdCollapse oneCell bodyEqual)
  | whiskerRight oneCell cellBody ihBody =>
      intro _
      have bodyEqual := boundaryEq_of_noGen noGen cellBody
      exact TwoCellConv.trans
        (TwoCellConv.whiskerRightCongr oneCell (ihBody bodyEqual))
        (whiskerRightIdCollapse oneCell bodyEqual)

/-- ★ **Local thinness** — in a no-generating-2-cell signature ALL parallel free 2-cells are convertible (both
collapse to the common transported identity on their shared boundary). -/
theorem allParallelConv_of_noGen {signature : ModeSignature} (noGen : SignatureHasNoTwoGen signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath) :
    TwoCellConv signature cellAlpha cellBeta :=
  TwoCellConv.trans (collapseToId noGen cellAlpha (boundaryEq_of_noGen noGen cellAlpha))
    (TwoCellConv.symm (collapseToId noGen cellBeta (boundaryEq_of_noGen noGen cellBeta)))

/-- ★ **The locally-thin decider** — a no-generating-2-cell signature's free 2-cell convertibility is decidable
(`isTrue` everywhere, by local thinness).  This is the FIRST genuine `DecidableTwoCellConvFor _.toModeSignature`
inhabitant — LEG A of the dispatch, for the no-2-gen fragment. -/
def locallyThinDecider {signature : ModeSignature} (noGen : SignatureHasNoTwoGen signature) :
    DecidableTwoCellConvFor signature :=
  fun cellAlpha cellBeta => Decidable.isTrue (allParallelConv_of_noGen noGen cellAlpha cellBeta)

/-! ## Reading local thinness off a `ModeComputad` -/

/-- A `ModeComputad` whose 2-generator list has length zero reconstructs to a no-generating-2-cell signature:
its `ReconstructedTwoCell` index lands in `Fin 0`. -/
theorem noGen_of_twoGenLenZero {computad : ModeComputad}
    (lenZero : computad.twoCellGenerators.length = 0) :
    SignatureHasNoTwoGen computad.toModeSignature :=
  fun _ _ reconstructed => Fin.elim0 (lenZero ▸ reconstructed.val)

/-- The pushout of two no-2-generator computads has itself no 2-generators (its 2-generator count is the sum
`0 + 0`). -/
theorem pushout_twoGenLenZero_of_components {comp1 comp2 : ModeComputad}
    (sameModes : comp1.modeCount = comp2.modeCount)
    (leftLenZero : comp1.twoCellGenerators.length = 0)
    (rightLenZero : comp2.twoCellGenerators.length = 0) :
    (pushoutShared comp1 comp2 sameModes).twoCellGenerators.length = 0 := by
  rw [pushoutShared_twoCellCount, leftLenZero, rightLenZero]

/-! ## The dispatch, inhabited for two locally-thin components -/

/-- ★ **The doubly-thin dispatch** — `DispatchDecidability` INHABITED for two no-2-generator components.  Both
component deciders are `locallyThinDecider`; the pushout inherits no 2-generators
(`pushout_twoGenLenZero_of_components`) so its combined decider is `locallyThinDecider` too; the
disjoint-generator precondition holds because the pushout's (empty) 2-generator list satisfies `.all` vacuously.
This is the LEG-B dispatch fragment that closes ZERO-AXIOM — the regime where the free word problem is trivial
because neither doctrine contributes a generating 2-cell. -/
def locallyThinDispatch {comp1 comp2 : ModeComputad} (sameModes : comp1.modeCount = comp2.modeCount)
    (leftLenZero : comp1.twoCellGenerators.length = 0)
    (rightLenZero : comp2.twoCellGenerators.length = 0)
    (disjoint :
      computadGeneratorsDisjoint comp1.modalityGenerators.length (pushoutShared comp1 comp2 sameModes) = true) :
    DispatchDecidability comp1 comp2 sameModes where
  componentOneDecider := locallyThinDecider (noGen_of_twoGenLenZero leftLenZero)
  componentTwoDecider := locallyThinDecider (noGen_of_twoGenLenZero rightLenZero)
  generatorsDisjoint := disjoint
  combinedDecider :=
    locallyThinDecider
      (noGen_of_twoGenLenZero (pushout_twoGenLenZero_of_components sameModes leftLenZero rightLenZero))

/-! ## Concrete instantiations: the walking involution + a second thin doctrine -/

/-- The walking-involution component reconstructs to a no-generating-2-cell signature (its `s.s = id` law is
1-cell level, so `twoCellGenerators = []`). -/
theorem involution_noGen : SignatureHasNoTwoGen involutionComputad.toModeSignature :=
  noGen_of_twoGenLenZero (computad := involutionComputad) rfl

/-- ★ **The walking-involution component decider** — the concrete FIRST genuine
`DecidableTwoCellConvFor _.toModeSignature`, for a real DECIDED walking doctrine.  LEG A, witnessed. -/
def involutionThinDecider : DecidableTwoCellConvFor involutionComputad.toModeSignature :=
  locallyThinDecider involution_noGen

/-- A second single-object no-2-generator computad (the single-object semiring presentation), disjoint from the
involution, to exercise the dispatch on a pushout with TWO 1-generators. -/
def secondThinComputad : ModeComputad := singleObjectSemiringComputad

/-- The involution and the second thin computad share their single mode. -/
theorem involutionSecondSameModes : involutionComputad.modeCount = secondThinComputad.modeCount := rfl

/-- The doubly-thin pushout `involution +_M semiring` — one mode, two 1-generators (`s @ 0`, the semiring's
generator `@ 1`), NO 2-generators. -/
def thinPushout : ModeComputad :=
  pushoutShared involutionComputad secondThinComputad involutionSecondSameModes

/-- The thin pushout has no 2-generators (profile `(1, 2, 0)`). -/
theorem thinPushout_profile : thinPushout.dimensionProfile = (1, 2, 0) := rfl

/-- The disjoint-generator precondition holds for the thin pushout (vacuously — no 2-generators). -/
theorem thinPushout_disjoint :
    computadGeneratorsDisjoint involutionComputad.modalityGenerators.length thinPushout = true := rfl

/-- ★ **The dispatch INHABITED at the concrete involution + semiring pushout** — a genuine
`DispatchDecidability` value assembled from two real locally-thin walking-doctrine deciders. -/
def involutionSecondDispatch :
    DispatchDecidability involutionComputad secondThinComputad involutionSecondSameModes :=
  locallyThinDispatch involutionSecondSameModes rfl rfl thinPushout_disjoint

/-! ## LEG C — a genuine MIXED 2-cell pair, decided -/

/-- The letter `s` (component 1) in the thin pushout's alphabet. -/
def thinSLetter : Fin thinPushout.modalityGenerators.length :=
  embedLeftLetter involutionComputad secondThinComputad involutionSecondSameModes ⟨0, by decide⟩

/-- The letter `u` (component 2, the semiring generator) in the thin pushout's alphabet. -/
def thinULetter : Fin thinPushout.modalityGenerators.length :=
  embedRightLetter involutionComputad secondThinComputad involutionSecondSameModes ⟨0, by decide⟩

/-- The mode `0` of the thin pushout (one mode). -/
def thinMode : Fin thinPushout.modeCount := ⟨0, by decide⟩

/-- A mixed 1-cell path `s . u` over the thin pushout — genuinely uses BOTH components' letters. -/
def thinMixedPath : ModalityPath thinPushout.toModeSignature.graph thinMode thinMode :=
  ModalityPath.cons ⟨thinSLetter, rfl⟩
    (ModalityPath.cons ⟨thinULetter, rfl⟩ (ModalityPath.nil (graph := thinPushout.toModeSignature.graph) thinMode))

/-- The identity 2-cell on the mixed path `s . u`. -/
def thinMixedAlpha : RawTwoCellExpr thinPushout.toModeSignature thinMixedPath thinMixedPath :=
  RawTwoCellExpr.id thinMixedPath

/-- A DISTINCT 2-cell of the same mixed boundary — the identity vertically composed with itself (a genuine
`vcompIdLeft` redex, so `thinMixedBeta ≠ thinMixedAlpha` as expressions). -/
def thinMixedBeta : RawTwoCellExpr thinPushout.toModeSignature thinMixedPath thinMixedPath :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.id thinMixedPath) (RawTwoCellExpr.id thinMixedPath)

/-- The combined decider of the concrete dispatch, applied to the mixed pair, read off as a `Bool`.  Expect
`true` — the two distinct mixed expressions are convertible (locally thin), and the decider COMPUTES the verdict.
The `isFalse` direction is unreachable in the thin fragment (see the honesty markers). -/
def mixedThinVerdict : Bool :=
  match involutionSecondDispatch.combinedDecider thinMixedAlpha thinMixedBeta with
  | Decidable.isTrue _ => true
  | Decidable.isFalse _ => false

-- The mixed pair over the real thin pushout is decided convertible: expect `true`.
#eval mixedThinVerdict

-- The thin pushout's dimension profile: expect `(1, 2, 0)` — one mode, two 1-generators, no 2-generators.
#eval thinPushout.dimensionProfile

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the FIRST genuine `DecidableTwoCellConvFor _.toModeSignature` ships (LEG A partial).**
The transported identity (`idTo`), the boundary collapse (`boundaryEq_of_noGen`), the collapse-to-identity
(`collapseToId`) via the shipped `TwoCellConv` congruences, hence local thinness (`allParallelConv_of_noGen`)
and the `locallyThinDecider`; instantiated at the real walking-involution component (`involutionThinDecider`).
This is a genuine, non-vacuous decider (it returns `isTrue` with an actual `TwoCellConv` proof over
genuinely-distinct expressions).  WALL: it covers exactly the NO-generating-2-cell fragment; a component with
generating 2-cells (the walking monad's `eta` / `mu`) forces the FREE `TwoCellConv` decision into the open
convergence hurdle (`fxMode_hasConvergentThreeCellSystem = false`), and the shipped walker decisions target a
strictly LARGER doctrine-SATURATED relation, not this free interface.  `= true`. -/
def fxAmalg_hasLocallyThinComponentDecider : Bool := true

/-- ★ **Honesty marker — the dispatch INHABITED for two locally-thin components (LEG B fragment + LEG C).**
`locallyThinDispatch` assembles a genuine `DispatchDecidability` from two no-2-generator component deciders (the
pushout inherits no 2-generators, so its combined decider is locally thin too), witnessed concretely at
`involution +_M semiring` (`involutionSecondDispatch`), and a genuine MIXED 2-cell pair over that real pushout
is decided (`mixedThinVerdict`, `#eval`'d).  WALL — the EXACT jam that blocks the general
`fxAmalg_hasDispatchTheorem`: the moment EITHER component contributes a generating 2-cell, (i) the free
`TwoCellConv` decision on that side needs mode-9 convergence (open), and (ii) the disjoint-support Godement
interchange the block-dispatch needs (`fxMode_hasArcBlockCommuteProof = false`) is the SAME open residual, and
(iii) the Nelson-Oppen / Baader-Tinelli purification (freezing alien blocks as opaque wires) bites only on the
doctrine-SATURATED relation the free interface does not carry — with the wire-creating unit/counit generators
breaking the convex-block projection unless the component presentation is left-connected (SDRT II).  So the
general dispatch stays `fxAmalg_hasDispatchTheorem = false`; this file closes the block-stable (both-thin)
fragment.  `= true`. -/
def fxAmalg_hasLocallyThinDispatch : Bool := true

end FX1Poly.Polygraph.Amalgam
