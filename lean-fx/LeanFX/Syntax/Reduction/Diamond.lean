import LeanFX.Syntax.Reduction.CdLemmaStarWithBi

namespace LeanFX.Syntax
open LeanFX.Mode

/-! # Typed-level diamond property.

The Tait-Martin-Löf complete-development trick at the typed
level: `Term.cd a` is the universal common reduct of every
βι-witnessed parallel step from `a`.

* `Step.par.cd_lemma_star bi : Step.parStar b (Term.cd a)` for
  any `Step.par a b` with βι-witness (proved in
  `CdLemmaStarWithBi.lean`).

The diamond follows immediately: pick `c := Term.cd a`, both
legs are `cd_lemma_star` applied to each input's witness.

Closes #884 (W8.2 typed diamond).  Strip and Church-Rosser
(W8.3 / #885) need additional infrastructure — at typed level
`cd_lemma_star` produces a chain (`Step.parStar`), not a single
step, so the standard strip-tile-confluence pattern from the
raw level (`RawConfluence.lean`) needs a different shape: see
`Confluence.lean`. -/

/-- **Diamond property** for typed parallel reduction.  Two
βι-witnessed parallel steps from a common source meet at
`Term.cd source` via further parallel chains.  Proof: `cd a` is
the common reduct; both legs follow from `cd_lemma_star`. -/
theorem Step.par.diamond
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm leftTarget rightTarget : Term ctx termType}
    {leftStep : Step.par sourceTerm leftTarget}
    {rightStep : Step.par sourceTerm rightTarget}
    (leftBi : Step.par.isBi leftStep)
    (rightBi : Step.par.isBi rightStep) :
    ∃ commonReduct,
      Step.parStar leftTarget commonReduct ∧
      Step.parStar rightTarget commonReduct :=
  ⟨Term.cd sourceTerm,
   Step.par.cd_lemma_star leftBi,
   Step.par.cd_lemma_star rightBi⟩

/-- **Diamond** with βι-witnesses preserved on both legs.  Both
output chains are isBi-only — every link satisfies
`Step.par.isBi`.  Used downstream when chain confluence has to
keep the recursive chain in the βι-restricted regime. -/
theorem Step.par.diamond_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm leftTarget rightTarget : Term ctx termType}
    {leftStep : Step.par sourceTerm leftTarget}
    {rightStep : Step.par sourceTerm rightTarget}
    (leftBi : Step.par.isBi leftStep)
    (rightBi : Step.par.isBi rightStep) :
    ∃ commonReduct,
      ∃ leftLeg : Step.parStar leftTarget commonReduct,
        Step.parStar.isBi leftLeg ∧
      ∃ rightLeg : Step.parStar rightTarget commonReduct,
        Step.parStar.isBi rightLeg :=
  ⟨Term.cd sourceTerm,
   Step.par.cd_lemma_star leftBi, Step.par.cd_lemma_star_isBi leftBi,
   Step.par.cd_lemma_star rightBi, Step.par.cd_lemma_star_isBi rightBi⟩

end LeanFX.Syntax
