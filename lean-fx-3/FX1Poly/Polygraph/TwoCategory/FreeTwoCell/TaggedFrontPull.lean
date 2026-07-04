import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TaggedSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ReverseSwapRecognizer

/-! # TaggedFrontPull — the certified pull-by-tag extraction (FREE-7)

The class-enumeration endgame reconstructs a trace from a target tag order by REPLAY:
repeatedly pull the occurrence carrying the next tag to the front through certified
adjacent swaps.  This file ships the per-tag pull:

  * `AdjacentSwapWitness.toTaggedSwap` / `ReverseAdjacentSwapWitness.toTaggedSwap` — the
    recognizer certificates lift to the TAGGED swap: the context algebra is the shipped
    untagged reshaping verbatim, with the occurrence tags riding their generators (the
    moved atom carries its tag to the front);
  * `TaggedFrontPull` — one certified extraction: the head atom carrying the target tag,
    the once-mutated remainder behind it, the `TaggedTraceEquiv` certificate, and the tag
    equation, all riding in the value (the self-certifying discipline);
  * ★ `pullTagToFront?` — the computable pull: scan for the target tag; at each level lift
    the tail's pull past the kept head by ONE adjacent swap, trying the forward recognizer
    first and the reverse recognizer second (a `SpineAtomSwap` is directed, so the mover
    may sit on either side of the constructor; `symm` reorients the reverse case).  Fails
    honestly with `none` when the target tag is absent or some crossing is dependent.

Downstream (the remaining FREE-7 rungs): iterating the pull over a whole tag order gives
the replay function; determination (equal tag orders ⇒ equal reachable traces) then makes
replay COMPLETE for the class, and `SaturationFuelBound` turns the resulting enumeration
into the unconditional decider.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The recognizer certificates lift to the tagged swap -/

/-- **Forward lift**: a witnessed adjacent pair swaps as TAGGED atoms, the tags riding
their generators — the right atom moves to the front carrying `rightTag`.  The shipped
untagged reshaping (`AdjacentSwapWitness.toSwap`) verbatim, under the tag wrappers. -/
theorem AdjacentSwapWitness.toTaggedSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {leftAtom rightAtom : SpineAtom signature overallSource overallTarget}
    (witness : AdjacentSwapWitness leftAtom rightAtom) (leftTag rightTag : Nat)
    (taggedRest : List (TaggedSpineAtom signature overallSource overallTarget)) :
    TaggedSpineAtomSwap signature
      (⟨leftTag, leftAtom⟩ :: ⟨rightTag, rightAtom⟩ :: taggedRest)
      (⟨rightTag, witness.firstAfterSwap⟩ :: ⟨leftTag, witness.secondAfterSwap⟩ ::
        taggedRest) := by
  have leftAtomReshaped : leftAtom
      = ⟨leftAtom.leftMidMode, leftAtom.rightMidMode, leftAtom.leftContext,
          leftAtom.generatorDom, leftAtom.generatorCod, leftAtom.generator,
          composePath (composePath witness.inertPath rightAtom.generatorDom)
            rightAtom.rightContext⟩ :=
    congrArg (fun context => SpineAtom.mk leftAtom.leftMidMode leftAtom.rightMidMode
        leftAtom.leftContext leftAtom.generatorDom leftAtom.generatorCod
        leftAtom.generator context)
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
  have listReshaped : (⟨leftTag, leftAtom⟩ :
        TaggedSpineAtom signature overallSource overallTarget) ::
        ⟨rightTag, rightAtom⟩ :: taggedRest
      = (⟨leftTag, ⟨leftAtom.leftMidMode, leftAtom.rightMidMode, leftAtom.leftContext,
            leftAtom.generatorDom, leftAtom.generatorCod, leftAtom.generator,
            composePath (composePath witness.inertPath rightAtom.generatorDom)
              rightAtom.rightContext⟩⟩ :
          TaggedSpineAtom signature overallSource overallTarget) ::
        (⟨rightTag, ⟨rightAtom.leftMidMode, rightAtom.rightMidMode,
            composePath (composePath leftAtom.leftContext leftAtom.generatorCod)
              witness.inertPath,
            rightAtom.generatorDom, rightAtom.generatorCod, rightAtom.generator,
            rightAtom.rightContext⟩⟩ :
          TaggedSpineAtom signature overallSource overallTarget) :: taggedRest :=
    (congrArg (fun atom =>
        (⟨leftTag, atom⟩ : TaggedSpineAtom signature overallSource overallTarget) ::
          ⟨rightTag, rightAtom⟩ :: taggedRest)
      leftAtomReshaped).trans
      (congrArg (fun atom =>
          (⟨leftTag, ⟨leftAtom.leftMidMode, leftAtom.rightMidMode, leftAtom.leftContext,
              leftAtom.generatorDom, leftAtom.generatorCod, leftAtom.generator,
              composePath (composePath witness.inertPath rightAtom.generatorDom)
                rightAtom.rightContext⟩⟩ :
            TaggedSpineAtom signature overallSource overallTarget) ::
            (⟨rightTag, atom⟩ :
              TaggedSpineAtom signature overallSource overallTarget) :: taggedRest)
        rightAtomReshaped)
  exact listReshaped ▸ TaggedSpineAtomSwap.swap leftAtom.generator rightAtom.generator
    leftTag rightTag leftAtom.leftContext witness.inertPath rightAtom.rightContext
    taggedRest

/-- **Reverse lift**: the reconstructed pre-swap tagged pair swaps FORWARD onto the given
tagged pair — the mover carries `movingTag` at the front of the LHS.  Derived from the
forward lift at the reconstructed pair (both factorizations hold by construction), the
reverse factorization equations reshaping the RHS. -/
theorem ReverseAdjacentSwapWitness.toTaggedSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom movingAtom : SpineAtom signature overallSource overallTarget}
    (witness : ReverseAdjacentSwapWitness headAtom movingAtom) (headTag movingTag : Nat)
    (taggedRest : List (TaggedSpineAtom signature overallSource overallTarget)) :
    TaggedSpineAtomSwap signature
      (⟨movingTag, witness.movedFront⟩ :: ⟨headTag, witness.stayedBehind⟩ :: taggedRest)
      (⟨headTag, headAtom⟩ :: ⟨movingTag, movingAtom⟩ :: taggedRest) := by
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
  have swapAtReshaped : TaggedSpineAtomSwap signature
      (⟨movingTag, witness.movedFront⟩ :: ⟨headTag, witness.stayedBehind⟩ :: taggedRest)
      ((⟨headTag, ⟨headAtom.leftMidMode, headAtom.rightMidMode,
          composePath (composePath movingAtom.leftContext movingAtom.generatorDom)
            witness.inertPath,
          headAtom.generatorDom, headAtom.generatorCod, headAtom.generator,
          headAtom.rightContext⟩⟩ :
         TaggedSpineAtom signature overallSource overallTarget) ::
        (⟨movingTag, ⟨movingAtom.leftMidMode, movingAtom.rightMidMode,
           movingAtom.leftContext, movingAtom.generatorDom, movingAtom.generatorCod,
           movingAtom.generator,
           composePath (composePath witness.inertPath headAtom.generatorCod)
             headAtom.rightContext⟩⟩ :
          TaggedSpineAtom signature overallSource overallTarget) :: taggedRest) :=
    AdjacentSwapWitness.toTaggedSwap
      (⟨witness.inertPath, rfl, rfl⟩ :
        AdjacentSwapWitness witness.movedFront witness.stayedBehind)
      movingTag headTag taggedRest
  rw [← headReshaped, ← movingReshaped] at swapAtReshaped
  exact swapAtReshaped

/-! ## The certified pull -/

/-- **One certified pull-by-tag**: the head atom carrying the target tag, the remainder
behind it, and the trace-equivalence certificate — everything a replay step needs rides
in the value. -/
structure TaggedFrontPull (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} (targetTag : Nat)
    (taggedTrace : List (TaggedSpineAtom signature overallSource overallTarget)) where
  /-- The atom pulled to the front. -/
  pulledHead : TaggedSpineAtom signature overallSource overallTarget
  /-- The once-mutated remainder behind it. -/
  pulledRest : List (TaggedSpineAtom signature overallSource overallTarget)
  /-- The pull is a chain of certified adjacent swaps. -/
  isEquivalent : TaggedTraceEquiv signature taggedTrace (pulledHead :: pulledRest)
  /-- The pulled atom carries the target tag. -/
  hasTargetTag : pulledHead.occurrenceTag = targetTag

/-- ★ **The computable pull-by-tag**: scan for the target tag; lift the tail's pull past
each kept head by one adjacent swap, forward recognizer first, reverse second (the swap
constructor is directed — the mover may sit at either column, and `symm` reorients the
reverse case).  `none` when the tag is absent or a crossing is dependent. -/
def pullTagToFront? {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode} (targetTag : Nat) :
    (taggedTrace : List (TaggedSpineAtom signature overallSource overallTarget)) →
    Option (TaggedFrontPull signature targetTag taggedTrace)
  | [] => none
  | taggedHead :: taggedRest =>
      match Nat.decEq taggedHead.occurrenceTag targetTag with
      | Decidable.isTrue tagMatches =>
          some ⟨taggedHead, taggedRest, TaggedTraceEquiv.refl _, tagMatches⟩
      | Decidable.isFalse _ =>
          match pullTagToFront? modeDecEq modalityDecEq targetTag taggedRest with
          | none => none
          | some tailPull =>
              match recognizeAdjacentSwap modeDecEq modalityDecEq taggedHead.atom
                  tailPull.pulledHead.atom with
              | PSum.inl forwardWitness =>
                  some ⟨⟨tailPull.pulledHead.occurrenceTag,
                      forwardWitness.firstAfterSwap⟩,
                    ⟨taggedHead.occurrenceTag, forwardWitness.secondAfterSwap⟩ ::
                      tailPull.pulledRest,
                    TaggedTraceEquiv.trans
                      (TaggedTraceEquiv.consCongr taggedHead tailPull.isEquivalent)
                      (TaggedTraceEquiv.ofSwap
                        (forwardWitness.toTaggedSwap taggedHead.occurrenceTag
                          tailPull.pulledHead.occurrenceTag tailPull.pulledRest)),
                    tailPull.hasTargetTag⟩
              | PSum.inr _ =>
                  match recognizeReverseAdjacentSwap modeDecEq modalityDecEq
                      taggedHead.atom tailPull.pulledHead.atom with
                  | PSum.inl reverseWitness =>
                      some ⟨⟨tailPull.pulledHead.occurrenceTag,
                          reverseWitness.movedFront⟩,
                        ⟨taggedHead.occurrenceTag, reverseWitness.stayedBehind⟩ ::
                          tailPull.pulledRest,
                        TaggedTraceEquiv.trans
                          (TaggedTraceEquiv.consCongr taggedHead tailPull.isEquivalent)
                          (TaggedTraceEquiv.symm (TaggedTraceEquiv.ofSwap
                            (reverseWitness.toTaggedSwap taggedHead.occurrenceTag
                              tailPull.pulledHead.occurrenceTag tailPull.pulledRest))),
                        tailPull.hasTargetTag⟩
                  | PSum.inr _ => none

end FX1Poly.Polygraph
