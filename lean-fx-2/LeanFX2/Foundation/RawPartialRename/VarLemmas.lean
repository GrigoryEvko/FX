import LeanFX2.Foundation.RawPartialRename.Function

/-! # LeanFX2.Foundation.RawPartialRename.VarLemmas

Variable and binder-level lemmas that exercise `partialRename?` /
`unweaken?` / `constantPathBody?` at the leaves before the giant
inversion theorem.  Includes:

* `unweaken?_newest_var_none`, `unweaken?_weaken_var`,
  `partialRename?_lift_preserves_binder_var` (var-position guardrails)
* `lift_rename_some` (lift preserves pointwise rename-survival)
* `partialRename?_rename_some` (every variable of a total renaming
  survives the partial renaming, giving the full body back)
* `unweaken?_weaken` (the generic positive case the constant-path
  recognizer leans on)
* `constantPathBody?_pathLam_weaken` and a battery of pathLam
  compile-time guardrails covering binder, dropped-outer, escape,
  nested-binder, and unit-non-path corner cases.

## Root status

Kernel reductions and structural inductions; no axioms. -/

namespace LeanFX2

/-- The newest variable cannot be lowered across the dropped binder. -/
theorem RawTerm.unweaken?_newest_var_none {scope : Nat} :
    RawTerm.unweaken? (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩) = none := rfl

/-- A weakened variable lowers to its original position. -/
theorem RawTerm.unweaken?_weaken_var {scope : Nat}
    (position : Fin scope) :
    RawTerm.unweaken? (RawTerm.var (RawRenaming.weaken position)) =
      some (RawTerm.var position) := rfl

/-- Binder variables are preserved while lowering across an outer
weakening.  This guards the bug that a naive `dropNewest?` would make
under `lam` and `pathLam`. -/
theorem RawTerm.partialRename?_lift_preserves_binder_var
    {sourceScope targetScope : Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope) :
    RawTerm.partialRename?
      (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
      partialRenaming.lift =
      some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩) := rfl

/-- Lifting preserves the pointwise "this source variable survives"
condition used by `partialRename?_rename_some`. -/
theorem PartialRawRenaming.lift_rename_some
    {sourceScope middleScope targetScope : Nat}
    {sourceRenaming : RawRenaming sourceScope middleScope}
    {targetRenaming : RawRenaming sourceScope targetScope}
    {partialRenaming : PartialRawRenaming middleScope targetScope}
    (renamingSurvives :
      ∀ position, partialRenaming (sourceRenaming position) =
        some (targetRenaming position)) :
    ∀ position,
      partialRenaming.lift (sourceRenaming.lift position) =
        some (targetRenaming.lift position)
  | ⟨0, _⟩ => rfl
  | ⟨index + 1, indexLt⟩ => by
      cases sourceRenaming ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩ with
      | mk middleIndex middleLt =>
          simp only [PartialRawRenaming.lift, RawRenaming.lift, Fin.succ]
          rw [renamingSurvives ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩]

/-- If a partial renaming accepts every variable produced by a total
renaming, it accepts the whole renamed raw term and produces the
corresponding target-renamed term. -/
theorem RawTerm.partialRename?_rename_some
    {sourceScope middleScope targetScope : Nat}
    (term : RawTerm sourceScope)
    (sourceRenaming : RawRenaming sourceScope middleScope)
    (targetRenaming : RawRenaming sourceScope targetScope)
    (partialRenaming : PartialRawRenaming middleScope targetScope)
    (renamingSurvives :
      ∀ position, partialRenaming (sourceRenaming position) =
        some (targetRenaming position)) :
    RawTerm.partialRename? (term.rename sourceRenaming) partialRenaming =
      some (term.rename targetRenaming) := by
  induction term generalizing middleScope targetScope with
  | var position =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [renamingSurvives position]
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [bodyIH sourceRenaming.lift targetRenaming.lift
        partialRenaming.lift
        (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | app functionTerm argumentTerm functionIH argumentIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [functionIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        argumentIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | pair firstValue secondValue firstIH secondIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        secondIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | fst pairTerm pairIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [pairIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | snd pairTerm pairIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [pairIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        thenIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        elseIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | natZero => rfl
  | natSucc predecessor predecessorIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [predecessorIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | natElim scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        zeroIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        succIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | natRec scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        zeroIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        succIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [headIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        tailIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | listElim scrutinee nilBranch consBranch scrutineeIH nilIH consIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        nilIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        consIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | optionNone => rfl
  | optionSome valueTerm valueIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [valueIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | optionMatch scrutinee noneBranch someBranch scrutineeIH noneIH someIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        noneIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        someIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | eitherInl valueTerm valueIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [valueIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | eitherInr valueTerm valueIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [valueIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | eitherMatch scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | refl witness witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | idJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | modIntro innerTerm innerIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | modElim innerTerm innerIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | subsume innerTerm innerIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp intervalTerm intervalIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [intervalIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | pathLam body bodyIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [bodyIH sourceRenaming.lift targetRenaming.lift
        partialRenaming.lift
        (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [pathIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        intervalIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        partialIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | glueElim gluedValue gluedIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [gluedIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | transp pathTerm sourceTerm pathIH sourceIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [pathIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        sourceIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | transpFill pathTy currentInterval source pathTyIH intervalIH sourceIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [pathTyIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        intervalIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        sourceIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | hcomp sidesTerm capTerm sidesIH capIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [sidesIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        capIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | oeqRefl witness witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [pointwiseIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | idStrictRefl witness witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [forwardIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        backwardIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | equivApp equivTerm argument equivIH argumentIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [equivIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        argumentIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | refineIntro rawValue predicateProof valueIH proofIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [valueIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        proofIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | refineElim refinedValue refinedIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [refinedIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | recordIntro firstField firstIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [firstIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | recordProj recordValue recordIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [recordIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | codataUnfold initialState transition stateIH transitionIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [stateIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        transitionIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | codataDest codataValue codataIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [codataIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | sessionSend channel payload channelIH payloadIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [channelIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        payloadIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | sessionRecv channel channelIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [channelIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | effectPerform operationTag arguments tagIH argumentsIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [tagIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        argumentsIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | universeCode innerLevel => rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        codomainIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        codomainIH sourceRenaming.lift targetRenaming.lift partialRenaming.lift
          (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        codomainIH sourceRenaming.lift targetRenaming.lift partialRenaming.lift
          (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | productCode firstCode secondCode firstIH secondIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        secondIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | sumCode leftCode rightCode leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | listCode elementCode elementIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [elementIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | optionCode elementCode elementIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [elementIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | eitherCode leftCode rightCode leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [typeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | cumulUpMarker innerCode innerIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | uaToEquiv proofRaw proofIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [proofIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | equivApply equivRaw argRaw equivIH argIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [equivIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        argIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | idToEquiv proofRaw proofIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [proofIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        secondIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        secondIH sourceRenaming targetRenaming partialRenaming renamingSurvives]

/-- Weakening followed by `unweaken?` recovers any raw term.  This is the
generic form of the constant-path recognizer's positive case and is the
fact future transport computation rules must use instead of per-ctor
ad hoc reductions. -/
theorem RawTerm.unweaken?_weaken {scope : Nat}
    (term : RawTerm scope) :
    RawTerm.unweaken? term.weaken = some term := by
  dsimp only [RawTerm.unweaken?, RawTerm.weaken]
  rw [RawTerm.partialRename?_rename_some term RawRenaming.weaken
    RawRenaming.identity PartialRawRenaming.dropNewest
    PartialRawRenaming.dropNewest_weaken]
  rw [RawTerm.rename_identity]

/-- Compile-time guardrail: the constant-path recognizer accepts every
path whose body is literally an outer-scope term weakened under the
interval binder.  This is the positive all-constructors counterpart to
the interval-escape rejection tests below. -/
theorem RawTerm.constantPathBody?_pathLam_weaken {scope : Nat}
    (term : RawTerm scope) :
    RawTerm.constantPathBody? (RawTerm.pathLam term.weaken) =
      some term := by
  unfold RawTerm.constantPathBody?
  change RawTerm.unweaken? term.weaken = some term
  rw [RawTerm.unweaken?_weaken]

/-- Compile-time guardrail: under `pathLam`, the path binder itself must
survive `unweaken?`.  If binder lifting is wired incorrectly, this stops
being definitional. -/
theorem RawTerm.unweaken?_pathLam_binder_var {scope : Nat} :
    RawTerm.unweaken?
      (RawTerm.pathLam
        (RawTerm.var ⟨0, Nat.zero_lt_succ (scope + 1)⟩)) =
      some
        (RawTerm.pathLam
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) := rfl

/-- Compile-time guardrail: under `pathLam`, the dropped outer variable is
index 1 and must be rejected.  This is the shape that blocks an unsound
"constant path" transport rule from accepting a captured variable. -/
theorem RawTerm.unweaken?_pathLam_dropped_outer_var_none {scope : Nat} :
    RawTerm.unweaken?
      (RawTerm.pathLam
        (RawTerm.var
          ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩)) =
      none := rfl

/-- The constant-path recognizer rejects a path body that mentions the
interval binder.  Such a path is not constant, so future transport must
not compute by the constant-path rule. -/
theorem RawTerm.constantPathBody?_pathLam_interval_var_none {scope : Nat} :
    RawTerm.constantPathBody?
      (RawTerm.pathLam
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) =
      none := rfl

/-- The constant-path recognizer accepts a body that is exactly a
weakened outer variable. -/
theorem RawTerm.constantPathBody?_pathLam_weaken_var {scope : Nat}
    (position : Fin scope) :
    RawTerm.constantPathBody?
      (RawTerm.pathLam
        (RawTerm.var (RawRenaming.weaken position))) =
      some (RawTerm.var position) := rfl

/-- The recognizer treats an inner path binder as local to that inner
path, not as a use of the outer interval binder. -/
theorem RawTerm.constantPathBody?_pathLam_nested_binder_var {scope : Nat} :
    RawTerm.constantPathBody?
      (RawTerm.pathLam
        (RawTerm.pathLam
          (RawTerm.var ⟨0, Nat.zero_lt_succ (scope + 1)⟩))) =
      some
        (RawTerm.pathLam
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) := rfl

/-- The recognizer rejects a nested body that mentions the outer
interval binder.  This is the compile-time tripwire for the classic
unsound constant-transport shortcut. -/
theorem RawTerm.constantPathBody?_pathLam_nested_interval_escape_none
    {scope : Nat} :
    RawTerm.constantPathBody?
      (RawTerm.pathLam
        (RawTerm.pathLam
          (RawTerm.var
            ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩))) =
      none := rfl

/-- A non-path term is not a constant path. -/
theorem RawTerm.constantPathBody?_unit_none {scope : Nat} :
    RawTerm.constantPathBody? (RawTerm.unit (scope := scope)) = none := rfl

end LeanFX2
