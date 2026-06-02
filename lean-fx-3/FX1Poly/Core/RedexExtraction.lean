import FX1Poly.Core.RawTermNF
import FX1Poly.Core.Step

/-! # FX1Poly/Core/RedexExtraction
    — productive redex extraction: a root-redex source actually takes a `Step` (toward weak normalization)

`RawTermNF` ships `RawTerm.isStepNormalForm_blocks_step` — the SOUNDNESS direction of the structural
normality check: a structurally-normal term blocks every `Step`.  This file builds the CONVERSE
(completeness-with-witness) direction, per root-redex shape: when `RawTerm.hasRootStepSource`'s per-eliminator
check fires, the cell genuinely takes a `Step`, and the proof PRODUCES the reduct.

This is the missing ingredient for WEAK NORMALIZATION from strong normalization (the `Acc StepSuccessor`
descent must, at a non-normal term, extract an actual reduct to recurse on), which in turn feeds decidable
conversion on the strongly-normalizing fragment (#267) and the WHNF migration (#374).  The grind is one brick
per root-redex shape; this file ships the FUNCTION (beta) and PRODUCT (fst/snd) redexes.  The inductive-
eliminator iotas (boolElim / natElim / natRec / listElim / optionMatch / eitherMatch / idJ / idStrictRec) have
constructor-shaped scrutinees and are deferred to subsequent bricks.

Each brick has two parts: a shallow shape inversion (`isXxxSource t = true → t` has the constructor shape) and
the extraction proper (destructure the spine, invert the source, apply the matching `Step` constructor).

## Zero-axiom verification

`dsimp only` reduces the structural check on the literal `mkGen` scrutinee to the generator `if`; `by_cases`
on the generator equality + `if_neg` discharges the non-matching branch (`by decide` on `false = true`); the
matching branch destructures the child spine and applies the `Step` constructor.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- A `gen_lam`-rooted term (per `isLamSource`) is a lambda cell. -/
theorem isLamSource_eq_lam {scope : Nat} {functionTerm : RawTerm scope}
    (sourceIsLam : RawTerm.isLamSource functionTerm = true) :
    ∃ body : RawTerm (scope + 1), functionTerm = .mkGen .gen_lam () (.childCons body .childNil) := by
  match functionTerm with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isLamSource] at sourceIsLam
      by_cases generatorIsLam : generator = .gen_lam
      · subst generatorIsLam
        match children with
        | .childCons body .childNil => exact ⟨body, rfl⟩
      · rw [if_neg generatorIsLam] at sourceIsLam
        exact absurd sourceIsLam (by decide)

/-- **Beta redex extraction.**  If the children of a `gen_app` cell have a beta root (`hasAppBetaRoot` — the
function child is a lambda), the application takes a `Step` (the beta reduct). -/
theorem hasAppBetaRoot_exists_step {scope : Nat}
    (children : RawTermChildren [0, 0] scope)
    (betaRoot : RawTermChildren.hasAppBetaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_app () children) target := by
  match children with
  | .childCons functionTerm (.childCons argumentTerm .childNil) =>
      dsimp only [RawTermChildren.hasAppBetaRoot] at betaRoot
      obtain ⟨body, functionIsLam⟩ := isLamSource_eq_lam betaRoot
      subst functionIsLam
      exact ⟨RawTerm.subst0 body argumentTerm, Step.beta⟩

/-- A `gen_pair`-rooted term (per `isPairSource`) is a pair cell. -/
theorem isPairSource_eq_pair {scope : Nat} {pairTerm : RawTerm scope}
    (sourceIsPair : RawTerm.isPairSource pairTerm = true) :
    ∃ firstValue secondValue : RawTerm scope,
      pairTerm = .mkGen .gen_pair ()
        (.childCons firstValue (.childCons secondValue .childNil)) := by
  match pairTerm with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isPairSource] at sourceIsPair
      by_cases generatorIsPair : generator = .gen_pair
      · subst generatorIsPair
        match children with
        | .childCons firstValue (.childCons secondValue .childNil) =>
            exact ⟨firstValue, secondValue, rfl⟩
      · rw [if_neg generatorIsPair] at sourceIsPair
        exact absurd sourceIsPair (by decide)

/-- **Fst-projection iota redex extraction.**  If the child of a `gen_fst` cell has a pair-projection root
(`hasPairProjectionIotaRoot` — the projected term is a pair), the projection takes a `Step` (the first
component). -/
theorem hasPairProjectionIotaRoot_exists_step_fst {scope : Nat}
    (children : RawTermChildren [0] scope)
    (iotaRoot : RawTermChildren.hasPairProjectionIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_fst () children) target := by
  match children with
  | .childCons pairTerm .childNil =>
      dsimp only [RawTermChildren.hasPairProjectionIotaRoot] at iotaRoot
      obtain ⟨firstValue, secondValue, pairShape⟩ := isPairSource_eq_pair iotaRoot
      subst pairShape
      exact ⟨firstValue, Step.iotaFstPair⟩

/-- **Snd-projection iota redex extraction.**  Symmetric to `…_fst`: a `gen_snd` cell over a pair takes a
`Step` to the second component. -/
theorem hasPairProjectionIotaRoot_exists_step_snd {scope : Nat}
    (children : RawTermChildren [0] scope)
    (iotaRoot : RawTermChildren.hasPairProjectionIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_snd () children) target := by
  match children with
  | .childCons pairTerm .childNil =>
      dsimp only [RawTermChildren.hasPairProjectionIotaRoot] at iotaRoot
      obtain ⟨firstValue, secondValue, pairShape⟩ := isPairSource_eq_pair iotaRoot
      subst pairShape
      exact ⟨secondValue, Step.iotaSndPair⟩

end FX1Poly.Core
