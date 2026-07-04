import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExprDecidableEq
import FX1Poly.Polygraph.Computad.PathFactorization

/-! # SwapRecognizer — the computable adjacent-swap decision (FREE-6b)

Whether two ADJACENT spine atoms form a `SpineAtomSwap` pair is a pair of prefix
factorizations of their whiskering contexts.  This file ships the atom-level recognizer:

  * `AdjacentSwapWitness` — the certificate that a pair `(leftAtom, rightAtom)` matches the
    swap constructor's LHS: the inert middle zone plus the two context-factorization
    equations.  All other constructor parameters are the atoms' own fields, so the witness
    is a COMPLETE characterization;
  * `AdjacentSwapWitness.firstAfterSwap` / `secondAfterSwap` — the transposed pair the swap
    produces (right generator moves first, contexts shift across the inert zone);
  * `AdjacentSwapWitness.toSwap` — soundness: a witnessed pair swaps, at every tail;
  * `recognizeAdjacentSwap` — the decision, in the self-certifying `PSum` discipline (both
    certificates ride in the value; no companion lemmas): the first factorization is
    `ModalityPath.splitPrefix`, the second is `modalityPathDecEq`; the negative legs use the
    splitter's own negative certificate and inert-zone uniqueness (`composePathLeftCancel`).

This is the computation layer for the FUNCTIONAL trace normal form (the insertion /
lex-least construction) — the oriented system is NOT confluent (see the
`fxMode_hasOrientedAtomSwapTermination` docstring), so the canonical form is computed by
insertion, with this recognizer deciding which adjacent pairs commute.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The swap-pair certificate -/

/-- **The adjacent-swap certificate**: the pair `(leftAtom, rightAtom)` matches the
`SpineAtomSwap.swap` constructor's LHS with inert middle zone `inertPath`.  The two
factorization equations pin the constructor's `inertPath`/`leftAcc`/`rightAcc`/generator
parameters to the atoms' own fields, so this witness is a complete characterization of
swappability. -/
structure AdjacentSwapWitness {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (leftAtom rightAtom : SpineAtom signature overallSource overallTarget) where
  /-- The inert middle zone between the two generators' columns. -/
  inertPath : ModalityPath signature.graph leftAtom.rightMidMode rightAtom.leftMidMode
  /-- The right atom's left context is the left atom's OUTPUT column extended by the inert
  zone. -/
  leftContextFactors : rightAtom.leftContext
    = composePath (composePath leftAtom.leftContext leftAtom.generatorCod) inertPath
  /-- The left atom's right context is the inert zone extended by the right atom's INPUT
  column. -/
  rightContextFactors : leftAtom.rightContext
    = composePath (composePath inertPath rightAtom.generatorDom) rightAtom.rightContext

/-- The atom standing FIRST after the swap: the right generator, its left context now
tracking the left generator's INPUT state. -/
def AdjacentSwapWitness.firstAfterSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {leftAtom rightAtom : SpineAtom signature overallSource overallTarget}
    (witness : AdjacentSwapWitness leftAtom rightAtom) :
    SpineAtom signature overallSource overallTarget :=
  ⟨rightAtom.leftMidMode, rightAtom.rightMidMode,
    composePath (composePath leftAtom.leftContext leftAtom.generatorDom) witness.inertPath,
    rightAtom.generatorDom, rightAtom.generatorCod, rightAtom.generator,
    rightAtom.rightContext⟩

/-- The atom standing SECOND after the swap: the left generator, its right context now
tracking the right generator's OUTPUT state. -/
def AdjacentSwapWitness.secondAfterSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {leftAtom rightAtom : SpineAtom signature overallSource overallTarget}
    (witness : AdjacentSwapWitness leftAtom rightAtom) :
    SpineAtom signature overallSource overallTarget :=
  ⟨leftAtom.leftMidMode, leftAtom.rightMidMode, leftAtom.leftContext,
    leftAtom.generatorDom, leftAtom.generatorCod, leftAtom.generator,
    composePath (composePath witness.inertPath rightAtom.generatorCod)
      rightAtom.rightContext⟩

/-- **Soundness**: a witnessed adjacent pair swaps, at every tail.  The two factorization
equations rewrite the given atoms into the constructor's LHS forms (structure eta makes the
`congrArg` reshaping definitional); the constructor's RHS forms ARE
`firstAfterSwap`/`secondAfterSwap` definitionally. -/
theorem AdjacentSwapWitness.toSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {leftAtom rightAtom : SpineAtom signature overallSource overallTarget}
    (witness : AdjacentSwapWitness leftAtom rightAtom)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    SpineAtomSwap signature (leftAtom :: rightAtom :: rest)
      (witness.firstAfterSwap :: witness.secondAfterSwap :: rest) := by
  have leftAtomReshaped : leftAtom
      = ⟨leftAtom.leftMidMode, leftAtom.rightMidMode, leftAtom.leftContext,
          leftAtom.generatorDom, leftAtom.generatorCod, leftAtom.generator,
          composePath (composePath witness.inertPath rightAtom.generatorDom)
            rightAtom.rightContext⟩ :=
    congrArg (fun context => SpineAtom.mk leftAtom.leftMidMode leftAtom.rightMidMode
        leftAtom.leftContext leftAtom.generatorDom leftAtom.generatorCod leftAtom.generator
        context)
      witness.rightContextFactors
  have rightAtomReshaped : rightAtom
      = ⟨rightAtom.leftMidMode, rightAtom.rightMidMode,
          composePath (composePath leftAtom.leftContext leftAtom.generatorCod)
            witness.inertPath,
          rightAtom.generatorDom, rightAtom.generatorCod, rightAtom.generator,
          rightAtom.rightContext⟩ :=
    congrArg (fun context => SpineAtom.mk rightAtom.leftMidMode rightAtom.rightMidMode
        context rightAtom.generatorDom rightAtom.generatorCod rightAtom.generator
        rightAtom.rightContext)
      witness.leftContextFactors
  have listReshaped : leftAtom :: rightAtom :: rest
      = (⟨leftAtom.leftMidMode, leftAtom.rightMidMode, leftAtom.leftContext,
            leftAtom.generatorDom, leftAtom.generatorCod, leftAtom.generator,
            composePath (composePath witness.inertPath rightAtom.generatorDom)
              rightAtom.rightContext⟩ :
          SpineAtom signature overallSource overallTarget) ::
        (⟨rightAtom.leftMidMode, rightAtom.rightMidMode,
            composePath (composePath leftAtom.leftContext leftAtom.generatorCod)
              witness.inertPath,
            rightAtom.generatorDom, rightAtom.generatorCod, rightAtom.generator,
            rightAtom.rightContext⟩ :
          SpineAtom signature overallSource overallTarget) :: rest :=
    (congrArg (fun atom => atom :: rightAtom :: rest) leftAtomReshaped).trans
      (congrArg (fun atom =>
          (⟨leftAtom.leftMidMode, leftAtom.rightMidMode, leftAtom.leftContext,
              leftAtom.generatorDom, leftAtom.generatorCod, leftAtom.generator,
              composePath (composePath witness.inertPath rightAtom.generatorDom)
                rightAtom.rightContext⟩ :
            SpineAtom signature overallSource overallTarget) :: atom :: rest)
        rightAtomReshaped)
  exact listReshaped ▸ SpineAtomSwap.swap leftAtom.generator rightAtom.generator
    leftAtom.leftContext witness.inertPath rightAtom.rightContext rest

/-! ## The decision -/

/-- ★ **The adjacent-swap recognizer**: either the swap certificate, or a proof that the
pair does not swap — for ANY inert zone (the zone is unique by left-cancellation, so the
one candidate `splitPrefix` produces is the only one to check). -/
def recognizeAdjacentSwap {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (leftAtom rightAtom : SpineAtom signature overallSource overallTarget) :
    PSum (AdjacentSwapWitness leftAtom rightAtom)
      (AdjacentSwapWitness leftAtom rightAtom → False) :=
  match ModalityPath.splitPrefix modeDecEq modalityDecEq
      (composePath leftAtom.leftContext leftAtom.generatorCod) rightAtom.leftContext with
  | .inr leftContextNeverFactors =>
      PSum.inr (fun witness =>
        leftContextNeverFactors witness.inertPath witness.leftContextFactors)
  | .inl ⟨inertPath, inertFactors⟩ =>
      match modalityPathDecEq modeDecEq modalityDecEq leftAtom.rightContext
          (composePath (composePath inertPath rightAtom.generatorDom)
            rightAtom.rightContext) with
      | .isTrue rightContextFactors =>
          PSum.inl ⟨inertPath, inertFactors, rightContextFactors⟩
      | .isFalse rightContextDiffers =>
          PSum.inr (fun witness =>
            have inertZonesCoincide : witness.inertPath = inertPath :=
              composePathLeftCancel
                (composePath leftAtom.leftContext leftAtom.generatorCod)
                (witness.leftContextFactors.symm.trans inertFactors)
            rightContextDiffers (inertZonesCoincide ▸ witness.rightContextFactors))

end FX1Poly.Polygraph
