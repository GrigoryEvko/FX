import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FrontExtraction
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.OrientedAtomSwap

/-! # TraceNormalForm — the minimal-extraction normal form + its soundness (FREE-6b)

The normal-form FUNCTION: repeatedly extract the measure-least front candidate (the
classical lexicographic trace-normal-form algorithm, keyed by the `GeneratorKeying`
measure triple), with fuel-structural recursion (fuel = list length, exact by
`FrontExtraction.lengthEq`) so the definition is zero-axiom and computes by `rfl`.

  * `isMeasureLexSmaller` — the Boolean triple-lex comparison on atoms
    (left-context length, then right-context length, then generator key) — the same
    per-atom triple `spineTraceVector` flattens;
  * `selectMinimalExtraction` — first-wins fold selecting the measure-least candidate;
  * `normalizeSpine` / `normalizeSpineWithFuel` — the normal form;
  * `normalizeSpine_isTraceEquivalent` — SOUNDNESS: the normal form is trace-equivalent
    to the input.  The proof consumes the selected extraction's OWN certificate (the
    self-certifying discipline) — no lemma about the fold is needed, because whatever
    candidate the fold returns carries its trace-equivalence proof in the value.

STILL OPEN (the FREE-6b/c closers): the invariance theorem — trace-equivalent inputs
share the normal form (the same-least-front exchange argument; needs the front-form
well-definedness over the fixed overall domain path and a tie analysis strengthening the
keying across fibers) — and whence completeness + the decision (FREE-7).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The measure comparison -/

/-- The Boolean triple-lex comparison on atoms: left-context length, then right-context
length, then generator key — exactly the per-atom triple `spineTraceVector` flattens. -/
def isMeasureLexSmaller {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    (firstAtom secondAtom : SpineAtom signature overallSource overallTarget) : Bool :=
  Nat.blt firstAtom.leftContext.length secondAtom.leftContext.length ||
    (firstAtom.leftContext.length == secondAtom.leftContext.length &&
      (Nat.blt firstAtom.rightContext.length secondAtom.rightContext.length ||
        (firstAtom.rightContext.length == secondAtom.rightContext.length &&
          Nat.blt (keying.keyOf firstAtom.generator) (keying.keyOf secondAtom.generator))))

/-- Select the measure-least front candidate, first-wins on ties — the deterministic
selection the normal form recurses on. -/
def selectMinimalExtraction {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {originalList : List (SpineAtom signature overallSource overallTarget)}
    (headCandidate : FrontExtraction originalList)
    (otherCandidates : List (FrontExtraction originalList)) :
    FrontExtraction originalList :=
  otherCandidates.foldl
    (fun currentBest challenger =>
      if isMeasureLexSmaller keying challenger.frontAtom currentBest.frontAtom then
        challenger
      else currentBest)
    headCandidate

/-! ## The normal form -/

/-- The fuel-structural normal-form worker: extract the measure-least front candidate,
recurse on its remainder.  Fuel is the list length (exact by
`FrontExtraction.lengthEq`); the fuel-exhausted and no-candidate arms return the input
unchanged (unreachable on the canonical call, total without proofs). -/
def normalizeSpineWithFuel {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode} :
    Nat → List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget)
  | 0, spineList => spineList
  | _fuel + 1, [] => []
  | fuel + 1, atom :: rest =>
      match frontExtractions modeDecEq modalityDecEq (atom :: rest) with
      | [] => atom :: rest
      | headCandidate :: otherCandidates =>
          (selectMinimalExtraction keying headCandidate otherCandidates).frontAtom ::
            normalizeSpineWithFuel keying modeDecEq modalityDecEq fuel
              (selectMinimalExtraction keying headCandidate otherCandidates).remainder

/-- ★ **The minimal-extraction trace normal form**: repeatedly extract the measure-least
front candidate.  This is the FUNCTIONAL canonical form — greedy oriented rewriting is
not confluent and naive insertion is trapped at the same local minimum (see
`FrontExtraction.lean`), so the normal form is computed by whole-list extraction. -/
def normalizeSpine {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (spineList : List (SpineAtom signature overallSource overallTarget)) :
    List (SpineAtom signature overallSource overallTarget) :=
  normalizeSpineWithFuel keying modeDecEq modalityDecEq spineList.length spineList

/-! ## Soundness -/

/-- The worker is sound at every fuel: the output is trace-equivalent to the input.  The
selected extraction's OWN certificate discharges the head step — no fold lemma needed. -/
theorem normalizeSpineWithFuel_isTraceEquivalent {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (fuel : Nat) :
    ∀ (spineList : List (SpineAtom signature overallSource overallTarget)),
      AtomicTraceEquiv signature
        (normalizeSpineWithFuel keying modeDecEq modalityDecEq fuel spineList) spineList := by
  induction fuel with
  | zero => intro spineList; exact AtomicTraceEquiv.refl spineList
  | succ fuel innerHypothesis =>
      intro spineList
      cases spineList with
      | nil => exact AtomicTraceEquiv.refl []
      | cons atom rest =>
          dsimp only [normalizeSpineWithFuel]
          cases hCandidates : frontExtractions modeDecEq modalityDecEq (atom :: rest) with
          | nil => exact AtomicTraceEquiv.refl (atom :: rest)
          | cons headCandidate otherCandidates =>
              exact AtomicTraceEquiv.trans
                (AtomicTraceEquiv.consCongr
                  (selectMinimalExtraction keying headCandidate otherCandidates).frontAtom
                  (innerHypothesis
                    (selectMinimalExtraction keying headCandidate otherCandidates).remainder))
                (selectMinimalExtraction keying headCandidate
                  otherCandidates).isTraceEquivalent

/-- ★ **Soundness of the normal form**: `normalizeSpine` is trace-equivalent to its
input. -/
theorem normalizeSpine_isTraceEquivalent {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (spineList : List (SpineAtom signature overallSource overallTarget)) :
    AtomicTraceEquiv signature
      (normalizeSpine keying modeDecEq modalityDecEq spineList) spineList :=
  normalizeSpineWithFuel_isTraceEquivalent keying modeDecEq modalityDecEq
    spineList.length spineList

end FX1Poly.Polygraph
