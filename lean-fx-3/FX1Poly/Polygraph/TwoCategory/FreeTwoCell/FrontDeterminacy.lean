import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.StageComposite
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.OrientedAtomSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExprDecidableEq

/-! # FrontDeterminacy — equal measures on one stage pin the whole atom (FREE-6b)

The determinacy half of the same-least-front argument: two atoms acting on the SAME
stage 1-cell with EQUAL measure triples (left-context length, right-context length,
generator key) are EQUAL.  The stage composite pins `leftContext`, `generatorDom`, and
`rightContext` through two applications of the length-split determinacy
(`composePath_splitPackEqOfPrefixLengthEq`) — but NOT `generatorCod`, which is free of
the composite.  Closing that residual gap is the keying's job:

  * `GeneratorSeparatingKeying` — the honest strengthening of `GeneratorKeying` the
    normal-form DECISION needs: keys additionally separate CODOMAINS at a shared domain
    (equal keys at the same `domPath` force equal `codPath`, whence
    `keyOf_injectiveOnFiber` finishes).  Plain per-fiber injectivity is enough for
    TERMINATION (FREE-6a) but not for canonical-form determinacy: the measure triple
    cannot see the codomain.  Concrete finite signatures key globally, so both
    structures are trivially inhabited there;
  * `GeneratorSeparatingKeying.generatorPackEqOfKeyEq` — equal keys at a shared domain
    identify the (codomain, generator) dependent pair;
  * `SpineAtom.eqOfStageCompositeAndMeasureEq` — ★ the determinacy theorem: equal stage
    composites + equal measure triples imply atom equality.  With
    `FrontExtraction.frontStageComposite_eq` this says the measure-least FRONT FORM is
    the same for all trace-equivalent inputs — the selection half of the invariance
    theorem's exchange argument.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The separating keying -/

/-- The keying strengthening the normal-form decision needs: keys separate CODOMAINS at
a shared domain.  The stage composite pins an atom's left context, domain, and right
context, but the codomain is invisible to it — so canonical-form determinacy needs the
key to tell generators with the same domain but different codomains apart.  Any global
injective enumeration (every concrete finite signature) satisfies this. -/
structure GeneratorSeparatingKeying (signature : ModeSignature)
    extends GeneratorKeying signature where
  /-- Equal keys at a shared domain force equal codomains. -/
  keyOf_separatesCodomains : ∀ {sourceMode targetMode : signature.graph.Mode}
    {domPath codPathOne codPathTwo : ModalityPath signature.graph sourceMode targetMode}
    (firstGenerator : signature.twoCell domPath codPathOne)
    (secondGenerator : signature.twoCell domPath codPathTwo),
    keyOf firstGenerator = keyOf secondGenerator → codPathOne = codPathTwo

/-- Equal keys at a shared domain identify the (codomain, generator) dependent pair:
the separation gives the codomains, the per-fiber injectivity gives the generators. -/
theorem GeneratorSeparatingKeying.generatorPackEqOfKeyEq {signature : ModeSignature}
    (keying : GeneratorSeparatingKeying signature)
    {sourceMode targetMode : signature.graph.Mode}
    {domPath codPathOne codPathTwo : ModalityPath signature.graph sourceMode targetMode}
    (firstGenerator : signature.twoCell domPath codPathOne)
    (secondGenerator : signature.twoCell domPath codPathTwo)
    (keysEqual : keying.keyOf firstGenerator = keying.keyOf secondGenerator) :
    (⟨codPathOne, firstGenerator⟩ :
      PSigma fun codPath : ModalityPath signature.graph sourceMode targetMode =>
        signature.twoCell domPath codPath)
      = ⟨codPathTwo, secondGenerator⟩ := by
  have codsEqual : codPathOne = codPathTwo :=
    keying.keyOf_separatesCodomains firstGenerator secondGenerator keysEqual
  subst codsEqual
  exact congrArg
    (fun generator =>
      (⟨codPathOne, generator⟩ :
        PSigma fun codPath : ModalityPath signature.graph sourceMode targetMode =>
          signature.twoCell domPath codPath))
    (keying.keyOf_injectiveOnFiber firstGenerator secondGenerator keysEqual)

/-! ## The determinacy theorem -/

/-- ★ **Front-form determinacy**: two atoms acting on the SAME stage 1-cell with equal
measure triples are EQUAL.  The composite pins the left context (first length split),
then the domain and right context (second length split, with the domain length recovered
by right-cancellation); the separating key pins the codomain and the generator. -/
theorem SpineAtom.eqOfStageCompositeAndMeasureEq {signature : ModeSignature}
    (keying : GeneratorSeparatingKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    (firstAtom secondAtom : SpineAtom signature overallSource overallTarget)
    (compositesEqual : firstAtom.stageComposite = secondAtom.stageComposite)
    (leftLengthsEqual : firstAtom.leftContext.length = secondAtom.leftContext.length)
    (rightLengthsEqual : firstAtom.rightContext.length = secondAtom.rightContext.length)
    (keysEqual : keying.keyOf firstAtom.generator = keying.keyOf secondAtom.generator) :
    firstAtom = secondAtom := by
  cases firstAtom with
  | mk leftMidModeOne rightMidModeOne leftContextOne generatorDomOne generatorCodOne
      generatorOne rightContextOne =>
  cases secondAtom with
  | mk leftMidModeTwo rightMidModeTwo leftContextTwo generatorDomTwo generatorCodTwo
      generatorTwo rightContextTwo =>
  have compositesReduced : composePath leftContextOne
        (composePath generatorDomOne rightContextOne)
      = composePath leftContextTwo (composePath generatorDomTwo rightContextTwo) :=
    compositesEqual
  have leftLengthsReduced : leftContextOne.length = leftContextTwo.length :=
    leftLengthsEqual
  have rightLengthsReduced : rightContextOne.length = rightContextTwo.length :=
    rightLengthsEqual
  have keysReduced : keying.keyOf generatorOne = keying.keyOf generatorTwo := keysEqual
  have leftPack := composePath_splitPackEqOfPrefixLengthEq leftContextOne
    (composePath generatorDomOne rightContextOne) leftContextTwo
    (composePath generatorDomTwo rightContextTwo) compositesReduced leftLengthsReduced
  have leftMidModesEqual : leftMidModeOne = leftMidModeTwo :=
    congrArg (fun pack => pack.fst) leftPack
  subst leftMidModesEqual
  injection leftPack with _outerFstEqual innerLeftPack
  injection innerLeftPack with leftContextsEqual suffixesEqual
  subst leftContextsEqual
  have suffixLengths := congrArg ModalityPath.length suffixesEqual
  rw [lengthComposePath, lengthComposePath, rightLengthsReduced] at suffixLengths
  have domLengthsEqual : generatorDomOne.length = generatorDomTwo.length :=
    natAddRightCancel suffixLengths
  have rightPack := composePath_splitPackEqOfPrefixLengthEq generatorDomOne
    rightContextOne generatorDomTwo rightContextTwo suffixesEqual domLengthsEqual
  have rightMidModesEqual : rightMidModeOne = rightMidModeTwo :=
    congrArg (fun pack => pack.fst) rightPack
  subst rightMidModesEqual
  injection rightPack with _rightFstEqual innerRightPack
  injection innerRightPack with generatorDomsEqual rightContextsEqual
  subst generatorDomsEqual
  subst rightContextsEqual
  have generatorPack := keying.generatorPackEqOfKeyEq generatorOne generatorTwo
    keysReduced
  have generatorCodsEqual : generatorCodOne = generatorCodTwo :=
    congrArg (fun pack => pack.fst) generatorPack
  subst generatorCodsEqual
  injection generatorPack with _codFstEqual generatorsEqual
  subst generatorsEqual
  rfl

end FX1Poly.Polygraph
