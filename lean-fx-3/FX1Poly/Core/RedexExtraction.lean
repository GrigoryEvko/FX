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
per root-redex shape; this file ships the FUNCTION (beta), PRODUCT (fst/snd), BOOLEAN (boolElim), and NATURAL
(natElim / natRec) redexes.  The remaining inductive-eliminator iotas (listElim / optionMatch / eitherMatch /
idJ / idStrictRec) have the same shape and are deferred to subsequent bricks.

Each brick has two parts: a shallow shape inversion (`isXxxSource t = true → t` has the constructor shape) and
the extraction proper (destructure the spine, invert the source, apply the matching `Step` constructor).  For
the two-constructor eliminators (the scrutinee is one of two constructors) the boolean root check is a
disjunction `isXxxSource scrutinee || isYyySource scrutinee`; the case split is done by `cases h :
isXxxSource scrutinee` (NOT `rw [Bool.or_eq_true]`, which leaks `propext` through the iff-rewrite), with the
false branch collapsing `false || b ≡ b` by definitional reduction.

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

/-- A `gen_boolTrue`-rooted term is the `boolTrue` cell. -/
theorem isBoolTrueSource_eq_boolTrue {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsBoolTrue : RawTerm.isBoolTrueSource scrutinee = true) :
    scrutinee = .mkGen .gen_boolTrue () .childNil := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isBoolTrueSource] at sourceIsBoolTrue
      by_cases generatorIsBoolTrue : generator = .gen_boolTrue
      · subst generatorIsBoolTrue
        match children with
        | .childNil => rfl
      · rw [if_neg generatorIsBoolTrue] at sourceIsBoolTrue
        exact absurd sourceIsBoolTrue (by decide)

/-- A `gen_boolFalse`-rooted term is the `boolFalse` cell. -/
theorem isBoolFalseSource_eq_boolFalse {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsBoolFalse : RawTerm.isBoolFalseSource scrutinee = true) :
    scrutinee = .mkGen .gen_boolFalse () .childNil := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isBoolFalseSource] at sourceIsBoolFalse
      by_cases generatorIsBoolFalse : generator = .gen_boolFalse
      · subst generatorIsBoolFalse
        match children with
        | .childNil => rfl
      · rw [if_neg generatorIsBoolFalse] at sourceIsBoolFalse
        exact absurd sourceIsBoolFalse (by decide)

/-- **boolElim iota redex extraction.**  If the scrutinee child of a `gen_boolElim` cell is `boolTrue` or
`boolFalse` (`hasBoolElimIotaRoot`), the eliminator takes a `Step` (the selected branch).  The disjunctive
root check is split by `cases` on the boolean (propext-free), the false branch collapsing `false || b`. -/
theorem hasBoolElimIotaRoot_exists_step {scope : Nat}
    (children : RawTermChildren [0, 0, 0] scope)
    (iotaRoot : RawTermChildren.hasBoolElimIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_boolElim () children) target := by
  match children with
  | .childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)) =>
      replace iotaRoot :
          (RawTerm.isBoolTrueSource scrutinee || RawTerm.isBoolFalseSource scrutinee) = true := iotaRoot
      cases trueValue : RawTerm.isBoolTrueSource scrutinee with
      | true =>
          rw [isBoolTrueSource_eq_boolTrue trueValue]
          exact ⟨thenBranch, Step.iotaBoolTrue⟩
      | false =>
          rw [trueValue] at iotaRoot
          replace iotaRoot : RawTerm.isBoolFalseSource scrutinee = true := iotaRoot
          rw [isBoolFalseSource_eq_boolFalse iotaRoot]
          exact ⟨elseBranch, Step.iotaBoolFalse⟩

/-- A `gen_natZero`-rooted term is the `natZero` cell. -/
theorem isNatZeroSource_eq_natZero {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsNatZero : RawTerm.isNatZeroSource scrutinee = true) :
    scrutinee = .mkGen .gen_natZero () .childNil := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isNatZeroSource] at sourceIsNatZero
      by_cases generatorIsNatZero : generator = .gen_natZero
      · subst generatorIsNatZero
        match children with
        | .childNil => rfl
      · rw [if_neg generatorIsNatZero] at sourceIsNatZero
        exact absurd sourceIsNatZero (by decide)

/-- A `gen_natSucc`-rooted term is a `natSucc` cell over its predecessor. -/
theorem isNatSuccSource_eq_natSucc {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsNatSucc : RawTerm.isNatSuccSource scrutinee = true) :
    ∃ predecessor : RawTerm scope,
      scrutinee = .mkGen .gen_natSucc () (.childCons predecessor .childNil) := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isNatSuccSource] at sourceIsNatSucc
      by_cases generatorIsNatSucc : generator = .gen_natSucc
      · subst generatorIsNatSucc
        match children with
        | .childCons predecessor .childNil => exact ⟨predecessor, rfl⟩
      · rw [if_neg generatorIsNatSucc] at sourceIsNatSucc
        exact absurd sourceIsNatSucc (by decide)

/-- **natElim iota redex extraction.**  A `gen_natElim` over a `natZero`/`natSucc` scrutinee
(`hasNatElimIotaRoot`) takes a `Step` (zero branch, or the step-case app-chain). -/
theorem hasNatElimIotaRoot_exists_step_natElim {scope : Nat}
    (children : RawTermChildren [0, 0, 0] scope)
    (iotaRoot : RawTermChildren.hasNatElimIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_natElim () children) target := by
  match children with
  | .childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)) =>
      replace iotaRoot :
          (RawTerm.isNatZeroSource scrutinee || RawTerm.isNatSuccSource scrutinee) = true := iotaRoot
      cases zeroValue : RawTerm.isNatZeroSource scrutinee with
      | true =>
          rw [isNatZeroSource_eq_natZero zeroValue]
          exact ⟨zeroBranch, Step.iotaNatElimZero⟩
      | false =>
          rw [zeroValue] at iotaRoot
          replace iotaRoot : RawTerm.isNatSuccSource scrutinee = true := iotaRoot
          obtain ⟨predecessor, succShape⟩ := isNatSuccSource_eq_natSucc iotaRoot
          rw [succShape]
          exact ⟨_, Step.iotaNatElimSucc⟩

/-- **natRec iota redex extraction.**  The `gen_natRec` twin of `…_natElim` (same root check; the v2
substrate treats `gen_natElim` and `gen_natRec` identically). -/
theorem hasNatElimIotaRoot_exists_step_natRec {scope : Nat}
    (children : RawTermChildren [0, 0, 0] scope)
    (iotaRoot : RawTermChildren.hasNatElimIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_natRec () children) target := by
  match children with
  | .childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)) =>
      replace iotaRoot :
          (RawTerm.isNatZeroSource scrutinee || RawTerm.isNatSuccSource scrutinee) = true := iotaRoot
      cases zeroValue : RawTerm.isNatZeroSource scrutinee with
      | true =>
          rw [isNatZeroSource_eq_natZero zeroValue]
          exact ⟨zeroBranch, Step.iotaNatRecZero⟩
      | false =>
          rw [zeroValue] at iotaRoot
          replace iotaRoot : RawTerm.isNatSuccSource scrutinee = true := iotaRoot
          obtain ⟨predecessor, succShape⟩ := isNatSuccSource_eq_natSucc iotaRoot
          rw [succShape]
          exact ⟨_, Step.iotaNatRecSucc⟩

end FX1Poly.Core
