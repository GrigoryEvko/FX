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
conversion on the strongly-normalizing fragment and the WHNF migration.  The grind is one brick
per root-redex shape, and this file now covers ALL of them: FUNCTION (beta), PRODUCT (fst/snd), BOOLEAN
(boolElim), NATURAL (natElim / natRec), LIST (listElim), OPTION (optionMatch), EITHER (eitherMatch), and
IDENTITY (idJ / idStrictRec).  With every `hasXxxRoot`-shape covered, the next step is the assembly
`hasRootStepSource = true → ∃ target, Step source target` (a generator case-split dispatching to these bricks),
then the mutual `exists_step_of_not_isStepNormalForm` and weak normalization.

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

/-- A `gen_lam`-rooted term (per `isLamSource`) is a lambda cell.

Church-style: the lambda carries a domain annotation as its first child,
with the body under one binder. -/
theorem isLamSource_eq_lam {scope : Nat} {functionTerm : RawTerm scope}
    (sourceIsLam : RawTerm.isLamSource functionTerm = true) :
    ∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)),
      functionTerm =
        .mkGen .gen_lam ()
          (.childCons domainAnn (.childCons body .childNil)) := by
  match functionTerm with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isLamSource] at sourceIsLam
      by_cases generatorIsLam : generator = .gen_lam
      · subst generatorIsLam
        match children with
        | .childCons domainAnn (.childCons body .childNil) =>
            exact ⟨domainAnn, body, rfl⟩
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
      obtain ⟨domainAnn, body, functionIsLam⟩ := isLamSource_eq_lam betaRoot
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
root check is split by `cases` on the boolean (propext-free), the false branch collapsing `false || b`.
Phase-Z spine `[1, 0, 0, 0]`: children are `(motive, then, else, scrutinee)` with the scrutinee LAST. -/
theorem hasBoolElimIotaRoot_exists_step {scope : Nat}
    (children : RawTermChildren [1, 0, 0, 0] scope)
    (iotaRoot : RawTermChildren.hasBoolElimIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_boolElim () children) target := by
  match children with
  | .childCons _motive
      (.childCons thenBranch (.childCons elseBranch (.childCons scrutinee .childNil))) =>
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
(`hasNatElimIotaRoot`) takes a `Step` (zero branch, or the substituting succ reduct).  Phase-Z spine
`[1, 0, 2, 0]`: children are `(motive, zeroBranch, succBranch, scrutinee)` with the scrutinee LAST. -/
theorem hasNatElimIotaRoot_exists_step_natElim {scope : Nat}
    (children : RawTermChildren [1, 0, 2, 0] scope)
    (iotaRoot : RawTermChildren.hasNatElimIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_natElim () children) target := by
  match children with
  | .childCons _motive
      (.childCons zeroBranch (.childCons _succBranch (.childCons scrutinee .childNil))) =>
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
substrate treats `gen_natElim` and `gen_natRec` identically).  Phase-Z spine `[1, 0, 2, 0]`. -/
theorem hasNatElimIotaRoot_exists_step_natRec {scope : Nat}
    (children : RawTermChildren [1, 0, 2, 0] scope)
    (iotaRoot : RawTermChildren.hasNatElimIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_natRec () children) target := by
  match children with
  | .childCons _motive
      (.childCons zeroBranch (.childCons _succBranch (.childCons scrutinee .childNil))) =>
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

/-- A `gen_listNil`-rooted term is the `listNil` cell. -/
theorem isListNilSource_eq_listNil {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsListNil : RawTerm.isListNilSource scrutinee = true) :
    scrutinee = .mkGen .gen_listNil () .childNil := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isListNilSource] at sourceIsListNil
      by_cases generatorIsListNil : generator = .gen_listNil
      · subst generatorIsListNil
        match children with
        | .childNil => rfl
      · rw [if_neg generatorIsListNil] at sourceIsListNil
        exact absurd sourceIsListNil (by decide)

/-- A `gen_listCons`-rooted term is a `listCons` cell over its head and tail. -/
theorem isListConsSource_eq_listCons {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsListCons : RawTerm.isListConsSource scrutinee = true) :
    ∃ headVal tailVal : RawTerm scope,
      scrutinee = .mkGen .gen_listCons () (.childCons headVal (.childCons tailVal .childNil)) := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isListConsSource] at sourceIsListCons
      by_cases generatorIsListCons : generator = .gen_listCons
      · subst generatorIsListCons
        match children with
        | .childCons headVal (.childCons tailVal .childNil) => exact ⟨headVal, tailVal, rfl⟩
      · rw [if_neg generatorIsListCons] at sourceIsListCons
        exact absurd sourceIsListCons (by decide)

/-- A `gen_optionNone`-rooted term is the `optionNone` cell. -/
theorem isOptionNoneSource_eq_optionNone {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsOptionNone : RawTerm.isOptionNoneSource scrutinee = true) :
    scrutinee = .mkGen .gen_optionNone () .childNil := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isOptionNoneSource] at sourceIsOptionNone
      by_cases generatorIsOptionNone : generator = .gen_optionNone
      · subst generatorIsOptionNone
        match children with
        | .childNil => rfl
      · rw [if_neg generatorIsOptionNone] at sourceIsOptionNone
        exact absurd sourceIsOptionNone (by decide)

/-- A `gen_optionSome`-rooted term is an `optionSome` cell over its value. -/
theorem isOptionSomeSource_eq_optionSome {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsOptionSome : RawTerm.isOptionSomeSource scrutinee = true) :
    ∃ value : RawTerm scope,
      scrutinee = .mkGen .gen_optionSome () (.childCons value .childNil) := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isOptionSomeSource] at sourceIsOptionSome
      by_cases generatorIsOptionSome : generator = .gen_optionSome
      · subst generatorIsOptionSome
        match children with
        | .childCons value .childNil => exact ⟨value, rfl⟩
      · rw [if_neg generatorIsOptionSome] at sourceIsOptionSome
        exact absurd sourceIsOptionSome (by decide)

/-- A `gen_eitherInl`-rooted term is an `eitherInl` cell over its value. -/
theorem isEitherInlSource_eq_eitherInl {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsEitherInl : RawTerm.isEitherInlSource scrutinee = true) :
    ∃ value : RawTerm scope,
      scrutinee = .mkGen .gen_eitherInl () (.childCons value .childNil) := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isEitherInlSource] at sourceIsEitherInl
      by_cases generatorIsEitherInl : generator = .gen_eitherInl
      · subst generatorIsEitherInl
        match children with
        | .childCons value .childNil => exact ⟨value, rfl⟩
      · rw [if_neg generatorIsEitherInl] at sourceIsEitherInl
        exact absurd sourceIsEitherInl (by decide)

/-- A `gen_eitherInr`-rooted term is an `eitherInr` cell over its value. -/
theorem isEitherInrSource_eq_eitherInr {scope : Nat} {scrutinee : RawTerm scope}
    (sourceIsEitherInr : RawTerm.isEitherInrSource scrutinee = true) :
    ∃ value : RawTerm scope,
      scrutinee = .mkGen .gen_eitherInr () (.childCons value .childNil) := by
  match scrutinee with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isEitherInrSource] at sourceIsEitherInr
      by_cases generatorIsEitherInr : generator = .gen_eitherInr
      · subst generatorIsEitherInr
        match children with
        | .childCons value .childNil => exact ⟨value, rfl⟩
      · rw [if_neg generatorIsEitherInr] at sourceIsEitherInr
        exact absurd sourceIsEitherInr (by decide)

/-- A `gen_refl`-rooted term is a `refl` cell over its witness. -/
theorem isReflSource_eq_refl {scope : Nat} {witness : RawTerm scope}
    (sourceIsRefl : RawTerm.isReflSource witness = true) :
    ∃ rawWitness : RawTerm scope,
      witness = .mkGen .gen_refl () (.childCons rawWitness .childNil) := by
  match witness with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isReflSource] at sourceIsRefl
      by_cases generatorIsRefl : generator = .gen_refl
      · subst generatorIsRefl
        match children with
        | .childCons rawWitness .childNil => exact ⟨rawWitness, rfl⟩
      · rw [if_neg generatorIsRefl] at sourceIsRefl
        exact absurd sourceIsRefl (by decide)

/-- **listElim iota redex extraction.**  A `gen_listElim` over a `listNil`/`listCons` scrutinee takes a
`Step` (nil branch, or the step-case app-chain).  Phase-Z spine `[1, 0, 0, 0]`: children are
`(motive, nil, cons, scrutinee)` with the scrutinee LAST. -/
theorem hasListElimIotaRoot_exists_step {scope : Nat}
    (children : RawTermChildren [1, 0, 0, 0] scope)
    (iotaRoot : RawTermChildren.hasListElimIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_listElim () children) target := by
  match children with
  | .childCons _motive
      (.childCons nilBranch (.childCons consBranch (.childCons scrutinee .childNil))) =>
      replace iotaRoot :
          (RawTerm.isListNilSource scrutinee || RawTerm.isListConsSource scrutinee) = true := iotaRoot
      cases nilValue : RawTerm.isListNilSource scrutinee with
      | true =>
          rw [isListNilSource_eq_listNil nilValue]
          exact ⟨nilBranch, Step.iotaListElimNil⟩
      | false =>
          rw [nilValue] at iotaRoot
          replace iotaRoot : RawTerm.isListConsSource scrutinee = true := iotaRoot
          obtain ⟨headVal, tailVal, consShape⟩ := isListConsSource_eq_listCons iotaRoot
          rw [consShape]
          exact ⟨_, Step.iotaListElimCons⟩

/-- **optionMatch iota redex extraction.**  Phase-Z spine `[1, 0, 0, 0]`: children are
`(motive, noneBranch, someBranch, scrutinee)` with the scrutinee LAST. -/
theorem hasOptionMatchIotaRoot_exists_step {scope : Nat}
    (children : RawTermChildren [1, 0, 0, 0] scope)
    (iotaRoot : RawTermChildren.hasOptionMatchIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_optionMatch () children) target := by
  match children with
  | .childCons _motive
      (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))) =>
      replace iotaRoot :
          (RawTerm.isOptionNoneSource scrutinee || RawTerm.isOptionSomeSource scrutinee) = true := iotaRoot
      cases noneValue : RawTerm.isOptionNoneSource scrutinee with
      | true =>
          rw [isOptionNoneSource_eq_optionNone noneValue]
          exact ⟨noneBranch, Step.iotaOptionMatchNone⟩
      | false =>
          rw [noneValue] at iotaRoot
          replace iotaRoot : RawTerm.isOptionSomeSource scrutinee = true := iotaRoot
          obtain ⟨value, someShape⟩ := isOptionSomeSource_eq_optionSome iotaRoot
          rw [someShape]
          exact ⟨_, Step.iotaOptionMatchSome⟩

/-- **eitherMatch iota redex extraction** (both scrutinee constructors are unary).  Phase-Z spine
`[1, 0, 0, 0]`: children are `(motive, leftBranch, rightBranch, scrutinee)` with the scrutinee LAST. -/
theorem hasEitherMatchIotaRoot_exists_step {scope : Nat}
    (children : RawTermChildren [1, 0, 0, 0] scope)
    (iotaRoot : RawTermChildren.hasEitherMatchIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_eitherMatch () children) target := by
  match children with
  | .childCons _motive
      (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))) =>
      replace iotaRoot :
          (RawTerm.isEitherInlSource scrutinee || RawTerm.isEitherInrSource scrutinee) = true := iotaRoot
      cases inlValue : RawTerm.isEitherInlSource scrutinee with
      | true =>
          obtain ⟨value, inlShape⟩ := isEitherInlSource_eq_eitherInl inlValue
          rw [inlShape]
          exact ⟨_, Step.iotaEitherMatchInl⟩
      | false =>
          rw [inlValue] at iotaRoot
          replace iotaRoot : RawTerm.isEitherInrSource scrutinee = true := iotaRoot
          obtain ⟨value, inrShape⟩ := isEitherInrSource_eq_eitherInr iotaRoot
          rw [inrShape]
          exact ⟨_, Step.iotaEitherMatchInr⟩

/-- **idJ iota redex extraction.**  Phase-Z spine `[2, 0, 0]`: children are `(motive, baseCase, witness)`
with the witness LAST and the motive a term under two binders.  The identity eliminator's root check is a
single `isReflSource` on the witness child (no disjunction); a `refl` witness yields the base case. -/
theorem hasIdElimIotaRoot_exists_step_idJ {scope : Nat}
    (children : RawTermChildren [2, 0, 0] scope)
    (iotaRoot : RawTermChildren.hasIdElimIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_idJ () children) target := by
  match children with
  | .childCons _motive (.childCons baseCase (.childCons witness .childNil)) =>
      replace iotaRoot : RawTerm.isReflSource witness = true := iotaRoot
      obtain ⟨rawWitness, reflShape⟩ := isReflSource_eq_refl iotaRoot
      rw [reflShape]
      exact ⟨baseCase, Step.iotaIdJRefl⟩

/-- **idStrictRec iota redex extraction** (same root check as idJ; `gen_idStrictRec`).  Phase-Z spine
`[2, 0, 0]`: children are `(motive, baseCase, witness)` with the witness LAST. -/
theorem hasIdElimIotaRoot_exists_step_idStrictRec {scope : Nat}
    (children : RawTermChildren [2, 0, 0] scope)
    (iotaRoot : RawTermChildren.hasIdElimIotaRoot children = true) :
    ∃ target : RawTerm scope, Step (.mkGen .gen_idStrictRec () children) target := by
  match children with
  | .childCons _motive (.childCons baseCase (.childCons witness .childNil)) =>
      replace iotaRoot : RawTerm.isReflSource witness = true := iotaRoot
      obtain ⟨rawWitness, reflShape⟩ := isReflSource_eq_refl iotaRoot
      rw [reflShape]
      exact ⟨baseCase, Step.iotaIdStrictRecRefl⟩

end FX1Poly.Core
