import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.TraceDecision

/-! # SpineListDecEq — generic decidable equality of spine traces (FREE-DECEQ)

The class-saturation decision procedure (the corrected FREE-6b/7 route after the
Eckmann–Hilton falsification) is a bounded reachability search over spine traces: it
keeps a visited list and tests membership, so it needs `DecidableEq` on spine LISTS
generically over the signature.

The atom-level decision already exists generically (`spineAtomDecEq` in
`WalkingAdjunction/TraceDecision.lean` — the mode/1-cell/generator cascade, with the
generator fibers' decidable equality supplied as choice data), and the walking-adjunction
engine already instantiates the LIST level at its seed (`adjunctionSpineListDecEq`).
This file ships the missing GENERIC list level — the one definition FREE-DECEQ still
lacked.  (Importing across from `FreeTwoCell/` follows the `SpineTraceDecision.lean`
precedent.)

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **Decidable equality of spine traces over any signature** — the saturation
search's membership test: the generic atom decision lifted along the list instance. -/
def spineListDecEq {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} :
    DecidableEq (List (SpineAtom signature overallSource overallTarget)) :=
  @instDecidableEqList _ (spineAtomDecEq modeDecEq modalityDecEq twoCellDecEq)

end FX1Poly.Polygraph
