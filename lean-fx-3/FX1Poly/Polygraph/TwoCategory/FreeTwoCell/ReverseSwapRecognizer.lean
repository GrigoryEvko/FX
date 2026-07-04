import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapRecognizer

/-! # ReverseSwapRecognizer — the reverse adjacent-swap decision (FREE-6b)

★ THE COMPLETENESS BUG THIS FIXES.  A `SpineAtomSwap` is DIRECTED: its LHS lists the
lower-column atom first, its RHS the higher-column atom first.  The forward recognizer
(`recognizeAdjacentSwap`) therefore only certifies moving a HIGHER-column atom left past
a lower-column one.  But extraction must also move a LOWER-column atom left past a
higher-column head — the constructor's RHS-to-LHS direction.  Concretely: after the swap
`x :: y ⇝ y' :: x'` (side-by-side generators, `x` on the lower column), the occurrence
`x'` in `y' :: x'` can only reach the front by the REVERSE transposition; the forward
recognizer rejects the pair `(y', x')` on lengths.  A forward-only enumeration is
INCOMPLETE and breaks normal-form invariance (`nf (x :: y)` starts with `x`;
forward-only `nf (y' :: x')` cannot).  This file ships the missing direction:

  * `ReverseAdjacentSwapWitness` — the certificate that the adjacent pair
    `(headAtom, movingAtom)` is a swap's RHS: the inert zone plus two factorization
    equations, the exact dom/cod MIRROR of `AdjacentSwapWitness` (the head's left
    context factors through the mover's DOMAIN; the mover's right context factors
    through the head's CODOMAIN);
  * `movedFront` / `stayedBehind` — the reconstructed pre-swap pair (the mover
    relocated first, its right context now tracking the head's INPUT; the head behind,
    its left context now tracking the mover's OUTPUT);
  * `ReverseAdjacentSwapWitness.toSwap` — soundness: the pre-swap pair swaps FORWARD
    onto the given pair, at every tail (the forward witness of the pre-swap pair is
    literally `⟨inertPath, rfl, rfl⟩`);
  * `recognizeReverseAdjacentSwap` — the decision, in the self-certifying `PSum`
    discipline, mirroring the forward recognizer.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The reverse certificate -/

/-- **The reverse adjacent-swap certificate**: the pair `(headAtom, movingAtom)` is the
RHS of a swap whose LHS puts the mover first.  Dom/cod mirror of
`AdjacentSwapWitness`. -/
structure ReverseAdjacentSwapWitness {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (headAtom movingAtom : SpineAtom signature overallSource overallTarget) where
  /-- The inert middle zone between the mover's column and the head's column. -/
  inertPath : ModalityPath signature.graph movingAtom.rightMidMode headAtom.leftMidMode
  /-- The head's left context is the mover's INPUT column extended by the inert zone. -/
  headLeftContextFactors : headAtom.leftContext
    = composePath (composePath movingAtom.leftContext movingAtom.generatorDom) inertPath
  /-- The mover's right context is the inert zone extended by the head's OUTPUT
  column. -/
  movingRightContextFactors : movingAtom.rightContext
    = composePath (composePath inertPath headAtom.generatorCod) headAtom.rightContext

/-- The mover relocated to the front: its right context now tracks the head's INPUT
state (it acts before the head). -/
def ReverseAdjacentSwapWitness.movedFront {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom movingAtom : SpineAtom signature overallSource overallTarget}
    (witness : ReverseAdjacentSwapWitness headAtom movingAtom) :
    SpineAtom signature overallSource overallTarget :=
  ⟨movingAtom.leftMidMode, movingAtom.rightMidMode, movingAtom.leftContext,
    movingAtom.generatorDom, movingAtom.generatorCod, movingAtom.generator,
    composePath (composePath witness.inertPath headAtom.generatorDom)
      headAtom.rightContext⟩

/-- The head staying behind: its left context now tracks the mover's OUTPUT state. -/
def ReverseAdjacentSwapWitness.stayedBehind {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom movingAtom : SpineAtom signature overallSource overallTarget}
    (witness : ReverseAdjacentSwapWitness headAtom movingAtom) :
    SpineAtom signature overallSource overallTarget :=
  ⟨headAtom.leftMidMode, headAtom.rightMidMode,
    composePath (composePath movingAtom.leftContext movingAtom.generatorCod)
      witness.inertPath,
    headAtom.generatorDom, headAtom.generatorCod, headAtom.generator,
    headAtom.rightContext⟩

/-- **Soundness**: the reconstructed pre-swap pair swaps FORWARD onto the given pair, at
every tail.  The pre-swap pair's forward witness is `⟨inertPath, rfl, rfl⟩` (both
factorizations hold by construction); the two reverse factorization equations reshape
the swap's RHS atoms into the given head and mover. -/
theorem ReverseAdjacentSwapWitness.toSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom movingAtom : SpineAtom signature overallSource overallTarget}
    (witness : ReverseAdjacentSwapWitness headAtom movingAtom)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    SpineAtomSwap signature (witness.movedFront :: witness.stayedBehind :: rest)
      (headAtom :: movingAtom :: rest) := by
  have headReshaped : headAtom
      = (⟨headAtom.leftMidMode, headAtom.rightMidMode,
            composePath (composePath movingAtom.leftContext movingAtom.generatorDom)
              witness.inertPath,
            headAtom.generatorDom, headAtom.generatorCod, headAtom.generator,
            headAtom.rightContext⟩ :
          SpineAtom signature overallSource overallTarget) :=
    congrArg (fun context => SpineAtom.mk headAtom.leftMidMode headAtom.rightMidMode
        context headAtom.generatorDom headAtom.generatorCod headAtom.generator
        headAtom.rightContext)
      witness.headLeftContextFactors
  have movingReshaped : movingAtom
      = (⟨movingAtom.leftMidMode, movingAtom.rightMidMode, movingAtom.leftContext,
            movingAtom.generatorDom, movingAtom.generatorCod, movingAtom.generator,
            composePath (composePath witness.inertPath headAtom.generatorCod)
              headAtom.rightContext⟩ :
          SpineAtom signature overallSource overallTarget) :=
    congrArg (fun context => SpineAtom.mk movingAtom.leftMidMode movingAtom.rightMidMode
        movingAtom.leftContext movingAtom.generatorDom movingAtom.generatorCod
        movingAtom.generator context)
      witness.movingRightContextFactors
  have swapAtReshaped : SpineAtomSwap signature
      (witness.movedFront :: witness.stayedBehind :: rest)
      ((⟨headAtom.leftMidMode, headAtom.rightMidMode,
          composePath (composePath movingAtom.leftContext movingAtom.generatorDom)
            witness.inertPath,
          headAtom.generatorDom, headAtom.generatorCod, headAtom.generator,
          headAtom.rightContext⟩ :
         SpineAtom signature overallSource overallTarget) ::
        (⟨movingAtom.leftMidMode, movingAtom.rightMidMode, movingAtom.leftContext,
           movingAtom.generatorDom, movingAtom.generatorCod, movingAtom.generator,
           composePath (composePath witness.inertPath headAtom.generatorCod)
             headAtom.rightContext⟩ :
          SpineAtom signature overallSource overallTarget) :: rest) :=
    AdjacentSwapWitness.toSwap
      (⟨witness.inertPath, rfl, rfl⟩ :
        AdjacentSwapWitness witness.movedFront witness.stayedBehind) rest
  rw [← headReshaped, ← movingReshaped] at swapAtReshaped
  exact swapAtReshaped

/-! ## The decision -/

/-- ★ **The reverse adjacent-swap recognizer**: either the reverse certificate, or a
proof that the pair is not a swap's RHS — for ANY inert zone (unique by
left-cancellation, so the one candidate `splitPrefix` produces is the only one to
check). -/
def recognizeReverseAdjacentSwap {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (headAtom movingAtom : SpineAtom signature overallSource overallTarget) :
    PSum (ReverseAdjacentSwapWitness headAtom movingAtom)
      (ReverseAdjacentSwapWitness headAtom movingAtom → False) :=
  match ModalityPath.splitPrefix modeDecEq modalityDecEq
      (composePath movingAtom.leftContext movingAtom.generatorDom)
      headAtom.leftContext with
  | .inr headLeftContextNeverFactors =>
      PSum.inr (fun witness =>
        headLeftContextNeverFactors witness.inertPath witness.headLeftContextFactors)
  | .inl ⟨inertPath, inertFactors⟩ =>
      match modalityPathDecEq modeDecEq modalityDecEq movingAtom.rightContext
          (composePath (composePath inertPath headAtom.generatorCod)
            headAtom.rightContext) with
      | .isTrue movingRightContextFactors =>
          PSum.inl ⟨inertPath, inertFactors, movingRightContextFactors⟩
      | .isFalse movingRightContextDiffers =>
          PSum.inr (fun witness =>
            have inertZonesCoincide : witness.inertPath = inertPath :=
              composePathLeftCancel
                (composePath movingAtom.leftContext movingAtom.generatorDom)
                (witness.headLeftContextFactors.symm.trans inertFactors)
            movingRightContextDiffers
              (inertZonesCoincide ▸ witness.movingRightContextFactors))

end FX1Poly.Polygraph
