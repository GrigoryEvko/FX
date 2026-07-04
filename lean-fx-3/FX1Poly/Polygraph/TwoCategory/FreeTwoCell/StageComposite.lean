import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FrontExtraction

/-! # StageComposite — the head-stage 1-cell is a trace invariant (FREE-6b)

The geometric half of the same-least-front argument: the 1-cell the HEAD atom's stage
acts on (left context, generator DOMAIN, right context — the spine's source boundary)
is invariant under the whole atomic trace equivalence.  A head swap re-associates the
same five factors (the moved right generator's stage sees the left generator's INPUT
column, which is exactly the left atom's domain), and every other closure operator
leaves the head alone.

Consequence (`FrontExtraction.frontStageComposite_eq`): EVERY front extraction's front
atom acts on the SAME fixed 1-cell — the original head's stage composite.  So the front
forms of the candidates are factorizations of one fixed path; equal context lengths will
force equal contexts (the length-split determinacy, next brick), which is what makes the
measure-least selection well-defined across trace-equivalent inputs.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The stage composite -/

/-- The 1-cell an atom's stage acts on: left context, generator DOMAIN, right context.
For the head atom of a cell's spine this is the cell's source boundary path. -/
def SpineAtom.stageComposite {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget) :
    ModalityPath signature.graph overallSource overallTarget :=
  composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)

/-- The head atom's stage composite, `none` on the empty spine. -/
def headStageComposite {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    Option (ModalityPath signature.graph overallSource overallTarget)
  | [] => none
  | atom :: _ => some atom.stageComposite

/-! ## Invariance -/

/-- A head swap preserves the head stage composite: both sides re-associate the same
five factors (left accumulator, left generator's domain, inert zone, right generator's
domain, right accumulator). -/
theorem SpineAtomSwap.headStageComposite_eq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList) :
    headStageComposite firstList = headStageComposite secondList := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath
      rightAcc rest =>
      dsimp only [headStageComposite, SpineAtom.stageComposite]
      rw [composePath_assoc inertPath oneCellGLow rightAcc,
        composePath_assoc (composePath leftAcc oneCellFMid) inertPath
          (composePath oneCellGLow rightAcc),
        composePath_assoc leftAcc oneCellFMid
          (composePath inertPath (composePath oneCellGLow rightAcc))]

/-- ★ **The head stage composite is a trace invariant**: swaps re-associate it, the
closure operators transport it, and the head-cons congruence leaves the head alone. -/
theorem AtomicTraceEquiv.headStageComposite_eq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature firstList secondList) :
    headStageComposite firstList = headStageComposite secondList := by
  induction traceEquiv with
  | ofSwap swapStep => exact swapStep.headStageComposite_eq
  | refl spineList => rfl
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ _ => rfl

/-- Every front extraction's front atom acts on the SAME fixed 1-cell — the original
head's stage composite.  The candidates' front forms are factorizations of one path. -/
theorem FrontExtraction.frontStageComposite_eq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom : SpineAtom signature overallSource overallTarget}
    {rest : List (SpineAtom signature overallSource overallTarget)}
    (extraction : FrontExtraction (headAtom :: rest)) :
    extraction.frontAtom.stageComposite = headAtom.stageComposite :=
  Option.some.inj extraction.isTraceEquivalent.headStageComposite_eq

end FX1Poly.Polygraph
