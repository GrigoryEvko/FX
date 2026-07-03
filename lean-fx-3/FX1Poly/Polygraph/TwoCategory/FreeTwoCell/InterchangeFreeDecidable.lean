import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeNormalize
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExprDecidableEq

/-! # mode-3 floor — interchange-free 2-cell convertibility is DECIDABLE

`FreeTwoCellInterchangeFreeNormalize` reduced interchange-free convertibility to normal-form equality
(`interchangeFreeConv_iff_normalFormEq`, the convergent normalizer fed the shipped unconditional confluence).
`FreeTwoCellExprDecidableEq` then decided syntactic equality of free 2-cell expressions
(`RawTwoCellExpr.decidableEq`).  Composing the two closes the loop:

  ★ `decidableInterchangeFreeConv` — interchange-free 2-cell convertibility
    (`Core.EquationalTheory (fun a b => TwoCellStepInterchangeFree signature a b)`) is a literal `Decidable`,
    for ANY signature with decidable modes / modality generators / 2-cell generators.  Built by the GENERIC
    engine `Core.decidableEquationalTheoryOfReducerSN` (normalize both, compare normal forms): the
    interchange-free reducer `reduceOnce` (sound + complete), its inherited strong normalization, the
    unconditional confluence, and the now-available `DecidableEq` on the carrier.

This is the convergence-floor DECISION of the confluence-modulo-interchange route to the fib-3 keystone: it
decides 2-cell equality UP TO the eleven structural laws (Godement `interchange` withdrawn).  The remaining
brick toward the full `fxMode_hasModeRelativeConvDecision` flip is the modulo-interchange (Godement) quotient
of the resulting normal forms — an honest next step, not discharged here.  Together with the shipped sound
NEGATIVE half (`TwoCellConv.not_of_generatorCount_ne`) and the sound POSITIVE half
(`normalFormEq_imp_twoCellConv`), the full `TwoCellConv` decision is reduced to EXACTLY the modulo-interchange
cases — distinct interchange-free normal forms with EQUAL generator count.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the assembly is the
generic SN-decision engine instantiated at the fragment's reducer + the carrier's `DecidableEq`).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- ★ **Interchange-free 2-cell convertibility is decidable.**  For a signature with decidable modes,
modality generators, and 2-cell generators, the interchange-free fragment's convertibility (the equational
theory of `TwoCellStepInterchangeFree`) is a literal `Decidable`: normalize both cells with the convergent
`reduceOnce` normalizer and compare normal forms via `RawTwoCellExpr.decidableEq`.  The generic SN-decision
engine `Core.decidableEquationalTheoryOfReducerSN` does the assembly; the fragment supplies the reducer
(sound + complete), its strong normalization, and its unconditional confluence. -/
def decidableInterchangeFreeConv {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath) :
    Decidable (Core.EquationalTheory
      (fun (leftCell rightCell : RawTwoCellExpr signature sourcePath targetPath) =>
        TwoCellStepInterchangeFree signature leftCell rightCell) cellFirst cellSecond) :=
  letI : DecidableEq (RawTwoCellExpr signature sourcePath targetPath) :=
    RawTwoCellExpr.decidableEq modeDecEq modalityDecEq twoCellDecEq
  Core.decidableEquationalTheoryOfReducerSN
    RawTwoCellExpr.reduceOnce
    (fun fired => RawTwoCellExpr.reduceOnce_sound fired)
    (fun halted next => RawTwoCellExpr.reduceOnce_complete halted next)
    (fun cell => twoCellStepInterchangeFree_isStronglyNormalizing cell)
    (twoCellStepInterchangeFree_isConfluentUnconditional signature)
    cellFirst cellSecond

end FX1Poly.Polygraph
