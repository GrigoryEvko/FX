import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine

/-! # mode-3 floor — the Godement spine step + trace equivalence + SOUNDNESS of the trace invariant

`FreeTwoCellSpine` built the **spine** — the flat whiskered-atom list of a free 2-cell — and proved it is
INVARIANT under the eleven interchange-free STRUCTURAL laws (`TwoCellStepInterchangeFree.spine_eq`), but
NOT under the Godement `interchange` law (the documented remaining hurdle).  This file pins down EXACTLY what
interchange does to the spine and uses it to prove the SOUND HALF of the trace-monoid characterization of the
full `TwoCellConv`.

## What this file ships (each piece zero-axiom)

  ★ `RawTwoCellExpr.interchangeRedexSpineDiff` / `interchangeReductSpineDiff` — the interchange redex and reduct
    spines, computed to EXPLICIT nested difference-list forms (each a definitional `rfl`).  Reading them off
    side-by-side exhibits the Godement effect precisely: the two MIDDLE blocks (`cellAlphaUpper` and `cellBeta`)
    are TRANSPOSED, and their whisker contexts SHIFT — `cellAlphaUpper`'s right context `gLow → gMid`
    (`dom cellBeta → cod cellBeta`) and `cellBeta`'s left context `fHigh → fMid` (`cod cellAlphaUpper →
    dom cellAlphaUpper`).  The outer blocks (`cellAlpha`, `cellBetaUpper`) are untouched.
  ★ `SpineGodementStep` — the **Godement / interchange step on spines**, ONE constructor capturing exactly the
    block transposition above (universally quantified over the boundary accumulators, so the constructor already
    absorbs whisker congruence; the `rest` parameter absorbs vertical-composite congruence on the right).  This
    IS the partially-commutative (Mazurkiewicz / trace) monoid independence relation, made concrete on the
    dependently-typed, context-shifting whiskered-atom spine.
  ★ `SpineTraceEquiv` — **trace equivalence**: the reflexive-symmetric-transitive closure of `SpineGodementStep`
    plus a head-cons congruence (so prefixes of independent atoms pass through).
  ★ `SpineTraceEquiv.prependSpineDiff` — prepending any cell's spine preserves trace equivalence (structural
    recursion on the prepended cell, head-cons congruence per generator) — the engine that lets vertical-composite
    congruence thread through.
  ★ `TwoCellStep.spineTraceEquivDiff` — every full 3-cell rewrite (Godement `interchange` INCLUDED) transports
    the spine difference-list WITHIN trace equivalence, for all boundary accumulators: the eleven structural laws
    by `refl` (spine-invariant), the four congruences by the inductive hypothesis / `prependSpineDiff`, and
    `interchange` by the `SpineGodementStep` constructor.
  ★ `TwoCellConv.spineTraceEquiv` (★) — **SOUNDNESS of the trace invariant**: convertible 2-cells have
    trace-equivalent spines.  This is the necessary-condition half of the trace-monoid word-problem
    characterization of `TwoCellConv` — strictly sharper than the generator-count invariant
    (`ComputadWordProblem`), and the NO-direction the fib-3 keystone's full decision needs.

## What is DEFERRED (the precise remaining gap toward the keystone)

`TwoCellConv` is decided by `SpineTraceEquiv` of the spines via the iff whose `→` is shipped here; the `←`
(RECONSTRUCTION — realizing a spine-level trace equivalence as a cell-level `TwoCellConv`, the readback past the
`spine` quotient) and the DECIDABILITY of `SpineTraceEquiv` itself (the list-level Mazurkiewicz word problem — a
source-anchored canonical form over the context-shifting atoms) are the two honest remaining obligations.  They
are assembled around this soundness theorem in `AdjunctionTwoCellWordProblem`, which reduces the keystone
residual to exactly those two.  `fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay
`false`; the convergent-3-polygraph route stays blocked (interchange non-confluence is real — see
`adjunctionInterchangeIsNonDegenerate`).

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the spine computations are `rfl`; the soundness is induction on the step / conversion, CONSTRUCTING the new
`Prop` inductives, never casing them).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## The interchange step's spine, computed -/

/-- The interchange REDEX spine, in explicit nested difference-list form (`rfl`).  Reading it against
`interchangeReductSpineDiff`: the order is `cellAlpha`, `cellAlphaUpper`, `cellBeta`, `cellBetaUpper` — the two
inner blocks are adjacent and on the SAME side as the redex builds them. -/
theorem RawTwoCellExpr.interchangeRedexSpineDiff {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    {overallSource overallTarget : signature.graph.Mode}
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta cellBetaUpper)).spineDiff leftAcc rightAcc rest
      = cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
          (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc)
            (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc
              (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest))) := rfl

/-- The interchange REDUCT spine, in explicit nested difference-list form (`rfl`).  Against
`interchangeRedexSpineDiff`: the middle blocks `cellAlphaUpper` and `cellBeta` are TRANSPOSED, and their whisker
contexts shift — `cellBeta`'s left context `fHigh → fMid`, `cellAlphaUpper`'s right context `gLow → gMid`. -/
theorem RawTwoCellExpr.interchangeReductSpineDiff {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    {overallSource overallTarget : signature.graph.Mode}
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
        (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper)).spineDiff leftAcc rightAcc rest
      = cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
          (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc
            (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc)
              (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest))) := rfl

/-! ## The Godement spine step + trace equivalence -/

/-- The **Godement (interchange) step on spines** — the trace-monoid independence relation made concrete: the
two middle blocks of an interchange redex's spine are transposed and context-shifted (exactly the difference
between `interchangeRedexSpineDiff` and `interchangeReductSpineDiff`).  Universally quantified over the boundary
accumulators (`leftAcc` / `rightAcc`) and the trailing `rest`, so a step under any whisker / right-vcomp context
is one constructor application. -/
inductive SpineGodementStep (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- Transpose-and-shift the two horizontally-independent middle blocks. -/
  | godement {sourceMode middleMode targetMode : signature.graph.Mode}
      {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
      {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
      (cellAlpha : RawTwoCellExpr signature fLow fMid)
      (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
      (cellBeta : RawTwoCellExpr signature gLow gMid)
      (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
      (leftAcc : ModalityPath signature.graph overallSource sourceMode)
      (rightAcc : ModalityPath signature.graph targetMode overallTarget)
      (rest : List (SpineAtom signature overallSource overallTarget)) :
      SpineGodementStep signature
        (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
          (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc)
            (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc
              (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest))))
        (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
          (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc
            (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc)
              (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest))))

/-- **Trace equivalence** of spines — the reflexive-symmetric-transitive closure of the Godement spine step,
plus a head-cons congruence so an independent prefix passes through.  Two interchange-free normal forms are
related by `TwoCellConv` exactly when their spines are `SpineTraceEquiv` (the `→` half — soundness — is
`TwoCellConv.spineTraceEquiv` below; the `←` half is the deferred reconstruction). -/
inductive SpineTraceEquiv (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- A single Godement spine step is a trace equivalence. -/
  | ofStep {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      SpineGodementStep signature firstList secondList → SpineTraceEquiv signature firstList secondList
  /-- Reflexivity. -/
  | refl (spineList : List (SpineAtom signature overallSource overallTarget)) :
      SpineTraceEquiv signature spineList spineList
  /-- Symmetry. -/
  | symm {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      SpineTraceEquiv signature firstList secondList → SpineTraceEquiv signature secondList firstList
  /-- Transitivity. -/
  | trans {firstList secondList thirdList : List (SpineAtom signature overallSource overallTarget)} :
      SpineTraceEquiv signature firstList secondList → SpineTraceEquiv signature secondList thirdList →
      SpineTraceEquiv signature firstList thirdList
  /-- A head atom passes through trace equivalence (independent prefix). -/
  | consCongr (atom : SpineAtom signature overallSource overallTarget)
      {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      SpineTraceEquiv signature firstList secondList →
      SpineTraceEquiv signature (atom :: firstList) (atom :: secondList)

/-- Prepending any cell's spine difference-list preserves trace equivalence — structural recursion on the
prepended cell: a generator prepends one atom (head-cons congruence), an identity prepends nothing, a vertical
composite prepends both factors, a whiskering prepends under shifted accumulators. -/
theorem SpineTraceEquiv.prependSpineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)} →
    SpineTraceEquiv signature firstList secondList →
    SpineTraceEquiv signature (cell.spineDiff leftAcc rightAcc firstList)
      (cell.spineDiff leftAcc rightAcc secondList)
  | _, _, leftAcc, rightAcc, _, _, .gen generator, _, _, equiv =>
      SpineTraceEquiv.consCongr ⟨_, _, leftAcc, _, _, generator, rightAcc⟩ equiv
  | _, _, _, _, _, _, .id _, _, _, equiv => equiv
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLeft cellRight, _, _, equiv =>
      SpineTraceEquiv.prependSpineDiff leftAcc rightAcc cellLeft
        (SpineTraceEquiv.prependSpineDiff leftAcc rightAcc cellRight equiv)
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, _, _, equiv =>
      SpineTraceEquiv.prependSpineDiff (composePath leftAcc oneCell) rightAcc body equiv
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, _, _, equiv =>
      SpineTraceEquiv.prependSpineDiff leftAcc (composePath oneCell rightAcc) body equiv

/-! ## Soundness of the trace invariant -/

/-- A full `TwoCellStep` (Godement `interchange` INCLUDED) transports the spine difference-list WITHIN trace
equivalence, for all boundary accumulators.  By induction on the step: the eleven structural laws preserve the
spine ON THE NOSE (`refl`), the two vcomp congruences thread the inductive hypothesis / `prependSpineDiff`, the
two whisker congruences thread it under shifted accumulators, and `interchange` is one `SpineGodementStep`. -/
theorem TwoCellStep.spineTraceEquivDiff {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) :
    ∀ {overallSource overallTarget : signature.graph.Mode}
      (leftAcc : ModalityPath signature.graph overallSource sourceMode)
      (rightAcc : ModalityPath signature.graph targetMode overallTarget)
      (rest : List (SpineAtom signature overallSource overallTarget)),
      SpineTraceEquiv signature (expr.spineDiff leftAcc rightAcc rest)
        (reduct.spineDiff leftAcc rightAcc rest) := by
  induction step with
  | vcompIdLeft _ => intro _ _ _ _ _; exact SpineTraceEquiv.refl _
  | vcompIdRight _ => intro _ _ _ _ _; exact SpineTraceEquiv.refl _
  | vcompAssoc _ _ _ => intro _ _ _ _ _; exact SpineTraceEquiv.refl _
  | whiskerLeftId _ _ => intro _ _ _ _ _; exact SpineTraceEquiv.refl _
  | whiskerRightId _ _ => intro _ _ _ _ _; exact SpineTraceEquiv.refl _
  | whiskerLeftVcomp _ _ _ => intro _ _ _ _ _; exact SpineTraceEquiv.refl _
  | whiskerRightVcomp _ _ _ => intro _ _ _ _ _; exact SpineTraceEquiv.refl _
  | vcompCongrLeft cellBeta _ inductionHypothesis =>
      intro _ _ leftAcc rightAcc rest
      exact inductionHypothesis leftAcc rightAcc (cellBeta.spineDiff leftAcc rightAcc rest)
  | vcompCongrRight cellAlpha _ inductionHypothesis =>
      intro _ _ leftAcc rightAcc rest
      exact SpineTraceEquiv.prependSpineDiff leftAcc rightAcc cellAlpha
        (inductionHypothesis leftAcc rightAcc rest)
  | whiskerLeftCongr oneCell _ inductionHypothesis =>
      intro _ _ leftAcc rightAcc rest
      exact inductionHypothesis (composePath leftAcc oneCell) rightAcc rest
  | whiskerRightCongr oneCell _ inductionHypothesis =>
      intro _ _ leftAcc rightAcc rest
      exact inductionHypothesis leftAcc (composePath oneCell rightAcc) rest
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      intro _ _ leftAcc rightAcc rest
      exact SpineTraceEquiv.ofStep
        (SpineGodementStep.godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest)

/-- ★ **Soundness of the trace invariant.**  Convertible 2-cells have trace-equivalent spines: `TwoCellConv` is
mapped into `SpineTraceEquiv` of the spines.  By induction on the conversion — a single step via
`TwoCellStep.spineTraceEquivDiff` at the empty boundary, reflexivity / symmetry / transitivity via the matching
`SpineTraceEquiv` constructors.  This is the NECESSARY-condition (NO-direction) half of the trace-monoid
characterization of `TwoCellConv` — sharper than the generator-count invariant, since it tracks the atoms'
partial-commutation order, not merely their number. -/
theorem TwoCellConv.spineTraceEquiv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature expr reduct) :
    SpineTraceEquiv signature expr.spine reduct.spine := by
  induction conv with
  | ofStep step => exact step.spineTraceEquivDiff (identityPath _) (identityPath _) []
  | refl _ => exact SpineTraceEquiv.refl _
  | symm _ inductionHypothesis => exact SpineTraceEquiv.symm inductionHypothesis
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## Honesty marker -/

/-- **Honesty marker.**  Only the SOUND (NO-direction) half of the trace-monoid characterization of
`TwoCellConv` is shipped here (`TwoCellConv.spineTraceEquiv` : convertible ⟹ trace-equivalent spines).  The
RECONSTRUCTION (`SpineTraceEquiv` of the spines ⟹ `TwoCellConv` — the readback past the `spine` quotient) and
the DECIDABILITY of `SpineTraceEquiv` (the list-level Mazurkiewicz word problem) remain open; they are the two
obligations the keystone residual reduces to in `AdjunctionTwoCellWordProblem`.  Hence
`fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay `false`.  `= false`. -/
def fxMode_hasSpineTraceReconstruction : Bool := false

end FX1Poly.Tier0
