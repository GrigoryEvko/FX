import FX1Poly.Typed.Metatheory.SubjectReduction.RecursorElimObligationsDriftBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.DataEliminatorBranchTypeStepStable

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/DependentElimObligationsDriftBounded
    — SR-WF-TIEOFF (elim third): the FUEL-BOUNDED `ObligationsDriftBelow` for the dependent-match eliminators

The fuel-bounded twin of `DependentElimObligationsDrift.lean`.  The dependent-match eliminators
(`boolElim` / `optionMatch` / `eitherMatch` / `listElim` / `idJ`) are CONTEXT-FIXED — their branch binders live
INSIDE the branch TYPE at the ambient scope, and the motive obligation's context (`context.cons <scrutineeType>`)
is motive-INDEPENDENT — so a motive step never drifts a context HEAD (no `consContextHeadConv`).  But the branch
CLASSIFIERS read the motive, so a motive step drifts them: the `subst0 motive <constructor>` branches and the
binder-extended `piTyCode` branches.  Each such drift is the bounded `consClassifierConv` arm — subject FIXED,
classifier drifts via a `Conv`, the after-formedness supplied DIRECTLY from the motive's re-typed universe
membership (bounded-safe, the motive IS a structural cell-child), NOT by folding child-SR along the multi-step
branch-classifier chain (the wall).

This commit ships `boolElim` — the representative whose BOTH branches are `subst0 motive <constructor>`
(`motive[true]` / `motive[false]`), so the after-formedness is the already-shipped
`dependentMotiveOutputFormed_ofMotiveAndArgument` from the re-typed motive and the nullary constructor's typing.
The `boolElim` cell PERMUTES `args = (motive, scrutinee, then, else)` into the spine `(motive, then, else,
scrutinee)`, so the fuel bound `(boolElimRule.memberCell scope args).size` is the SPINE size; each stepping child's
size witness is taken at its SPINE position (`headChildBelowCellSize` at spine 0 … `fourthChildBelowCellSize` at
spine 3) so the witness's `childCons … + 1` is defeq to the spine `mkGen … .size`.  The `option` / `either` /
`list` / `idJ` rows (whose dependent branch types need the future `*_formedFromMotive` family) follow.

## Zero-axiom

`cases` on the (mutual-inductive) `StepChildren` + `ObligationsDriftBelow.{cons,consClassifierConv}` + the FUEL-
BOUNDED child-SR (`universeMembershipPreservedUnderStepBelow`) + `dependentMotiveOutputFormed_ofMotiveAndArgument`
+ `Conv.fromStepStar` over `StepStar.subst0Body` + nullary `boolTrue` / `boolFalse` intros.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **`boolTrue : boolType` in any context.**  The nullary `boolTrue` introducer typed at `boolTypeCell` — the
data argument the then-branch output-formedness substitutes for the motive's binder. -/
theorem boolTrueTypedInContext {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope) :
    HasTypeUnion profile context (RawTerm.mkGen .gen_boolTrue () .childNil) boolTypeCell := by
  refine HasTypeUnion.intro context .gen_boolTrue boolTrueIntroRule .childNil .childNil
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_ ?_
  · intro obligation hmem
    cases hmem
  · intro obligation hmem
    cases hmem

/-- **`boolFalse : boolType` in any context** — the `boolTrue` twin for the else-branch output. -/
theorem boolFalseTypedInContext {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope) :
    HasTypeUnion profile context (RawTerm.mkGen .gen_boolFalse () .childNil) boolTypeCell := by
  refine HasTypeUnion.intro context .gen_boolFalse boolFalseIntroRule .childNil .childNil
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_ ?_
  · intro obligation hmem
    cases hmem
  · intro obligation hmem
    cases hmem

/-- **`none : option(A)` in any context**, given the element type `A` is formed.  The nullary `optionNone`
introducer typed at `optionTypeCell elementType` — the data argument the dependent `none`-branch
output-formedness substitutes for the motive's binder (`dependentMotiveOutputFormed_ofMotiveAndArgument` with
argument `optionNoneCell`).  Its sole obligation is the element-at-universe formedness, supplied by the caller
(at the option scrutinee's inverted element level/flag). -/
theorem optionNoneTypedInContext {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
    (elementType : RawTerm scope) (elementLevel : LevelExpr) (flag : UniverseFlag)
    (locksInterval : context.AllLocksAreInterval)
    (elementTypeFormed : HasTypeUnion profile context elementType (universeCodeCell elementLevel flag)) :
    HasTypeUnion profile context optionNoneCell (optionTypeCell elementType) :=
  HasTypeUnion.intro context .gen_optionNone optionNoneIntroRule
    .childNil (.childCons elementType .childNil)
    elementLevel elementLevel flag rfl trivial
    (fun obligation hmem => by
      cases hmem with
      | head => exact elementTypeFormed
      | tail _ hmem => cases hmem)
    (fun obligation hmem => by
      cases hmem with
      | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval elementTypeFormed
      | tail _ hmem => cases hmem)

/-- **`nil : List(A)` in any context**, given the element type `A` is formed — the `optionNone` twin for the
dependent `listElim` `nil`-branch output (`dependentMotiveOutputFormed_ofMotiveAndArgument` with argument
`listNilCell`). -/
theorem listNilTypedInContext {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
    (elementType : RawTerm scope) (elementLevel : LevelExpr) (flag : UniverseFlag)
    (locksInterval : context.AllLocksAreInterval)
    (elementTypeFormed : HasTypeUnion profile context elementType (universeCodeCell elementLevel flag)) :
    HasTypeUnion profile context listNilCell (listTypeCell elementType) :=
  HasTypeUnion.intro context .gen_listNil listNilIntroRule
    .childNil (.childCons elementType .childNil)
    elementLevel elementLevel flag rfl trivial
    (fun obligation hmem => by
      cases hmem with
      | head => exact elementTypeFormed
      | tail _ hmem => cases hmem)
    (fun obligation hmem => by
      cases hmem with
      | head => exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval elementTypeFormed
      | tail _ hmem => cases hmem)

/-- **★ `boolElim`'s fuel-bounded obligation drift under one arg step.**  The bounded twin of
`boolElimObligationsDriftUnderArgStep`: a motive step drifts both `subst0 motive boolTrue` / `subst0 motive
boolFalse` branch classifiers (`consClassifierConv`, after-formedness from the re-typed motive and the constructor's
typing) and the motive subject; any other child step drifts only that subject.  Consumes the motive's universe
typing and `UnionChildSubjectReductionBelow profile (boolElimRule.memberCell scope args).size`. -/
theorem boolElimObligationsDriftUnderArgStepBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (motiveTyped : HasTypeUnion profile (context.cons boolTypeCell) motive (universeCodeCell level0 flag))
    (scrutineeClassifierFormed : UnionClassifierIsType profile context boolTypeCell)
    (thenBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive (RawTerm.mkGen .gen_boolTrue () .childNil)))
    (elseBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive (RawTerm.mkGen .gen_boolFalse () .childNil)))
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile
      (boolElimRule.memberCell scope
        (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))))).size)
    {argsAfter : RawTermChildren [1, 0, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))
        : RawTermChildren [1, 0, 0, 0] scope) argsAfter) :
    ObligationsDriftBelow profile
      (boolElimRule.memberCell scope
        (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))))).size
      (boolElimRule.obligations scope context
        (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))))
        .childNil level0 level1 flag)
      (boolElimRule.obligations scope context argsAfter .childNil level0 level1 flag) := by
  have motiveClassifierFormed : UnionClassifierIsType profile (context.cons boolTypeCell)
      (universeCodeCell level0 flag) :=
    ⟨_, _, HasTypeUnion.universeFormation (context.cons boolTypeCell) level0 flag⟩
  cases childStep with
  | here _ motiveStep =>
      have motiveAfterTyped := universeMembershipPreservedUnderStepBelow motiveTyped motiveStep
        (headChildBelowCellSize 1 motive _)
        childSubjectReductionBelow
      have thenFormedAfter := UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument
        context boolTypeCell _ (RawTerm.mkGen .gen_boolTrue () .childNil) level0 flag motiveAfterTyped
        (boolTrueTypedInContext context)
        (isSubjectUsableAtModality_ofNonVarHead context .gen_boolTrue () .childNil .fibrant (by decide))
      have elseFormedAfter := UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument
        context boolTypeCell _ (RawTerm.mkGen .gen_boolFalse () .childNil) level0 flag motiveAfterTyped
        (boolFalseTypedInContext context)
        (isSubjectUsableAtModality_ofNonVarHead context .gen_boolFalse () .childNil .fibrant (by decide))
      exact ObligationsDriftBelow.cons (.fixed scrutinee) scrutineeClassifierFormed
        (ObligationsDriftBelow.consClassifierConv
          (Conv.fromStepStar
            (StepStar.subst0Body (RawTerm.mkGen .gen_boolTrue () .childNil) (StepStar.single motiveStep)))
          thenFormedAfter
          (ObligationsDriftBelow.consClassifierConv
            (Conv.fromStepStar
              (StepStar.subst0Body (RawTerm.mkGen .gen_boolFalse () .childNil) (StepStar.single motiveStep)))
            elseFormedAfter
            (ObligationsDriftBelow.cons
              (.stepsBelow motiveStep (headChildBelowCellSize 1 motive _))
              motiveClassifierFormed ObligationsDriftBelow.nil)))
  | there _ tail1 =>
      cases tail1 with
      | here _ scrutineeStep =>
          exact ObligationsDriftBelow.cons
            (.stepsBelow scrutineeStep
              (fourthChildBelowCellSize 1 0 0 0 motive thenBranch elseBranch scrutinee _))
            scrutineeClassifierFormed
            (ObligationsDriftBelow.cons (.fixed thenBranch) thenBranchClassifierFormed
              (ObligationsDriftBelow.cons (.fixed elseBranch) elseBranchClassifierFormed
                (ObligationsDriftBelow.cons (.fixed motive) motiveClassifierFormed ObligationsDriftBelow.nil)))
      | there _ tail2 =>
          cases tail2 with
          | here _ thenStep =>
              exact ObligationsDriftBelow.cons (.fixed scrutinee) scrutineeClassifierFormed
                (ObligationsDriftBelow.cons
                  (.stepsBelow thenStep
                    (secondChildBelowCellSize 1 0 motive thenBranch _))
                  thenBranchClassifierFormed
                  (ObligationsDriftBelow.cons (.fixed elseBranch) elseBranchClassifierFormed
                    (ObligationsDriftBelow.cons (.fixed motive) motiveClassifierFormed ObligationsDriftBelow.nil)))
          | there _ tail3 =>
              cases tail3 with
              | here _ elseStep =>
                  exact ObligationsDriftBelow.cons (.fixed scrutinee) scrutineeClassifierFormed
                    (ObligationsDriftBelow.cons (.fixed thenBranch) thenBranchClassifierFormed
                      (ObligationsDriftBelow.cons
                        (.stepsBelow elseStep
                          (thirdChildBelowCellSize 1 0 0 motive thenBranch elseBranch _))
                        elseBranchClassifierFormed
                        (ObligationsDriftBelow.cons (.fixed motive) motiveClassifierFormed
                          ObligationsDriftBelow.nil)))
              | there _ emptyTailStep => cases emptyTailStep

end FX1Poly.Typed
