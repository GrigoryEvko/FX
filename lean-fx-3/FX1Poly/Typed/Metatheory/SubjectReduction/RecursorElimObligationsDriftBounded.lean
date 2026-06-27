import FX1Poly.Typed.Metatheory.SubjectReduction.CleanElimObligationsDriftBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentBranchTypeMotiveCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentBranchTypeFormedFromMotive

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/RecursorElimObligationsDriftBounded
    — SR-WF-TIEOFF (elim third): the FUEL-BOUNDED `ObligationsDriftBelow` for the recursors (`natElim` / `natRec`)

The fuel-bounded twin of `RecursorElimObligationsDrift.lean`.  `natElim` / `natRec` are the BINDER-EXTENDED
recursors whose step-branch obligation lives in the two-binder context `(context.cons natTypeCell).cons motive`
whose HEAD binding IS the motive.  When the motive (arg 0) steps, three obligations drift at once, each by the
fuel-bounded route — NO child-SR folds a multi-step branch-classifier chain:

  * the **motive** obligation: subject drifts (`SubjectDriftBelow.stepsBelow`, source `motive.size <
    (natElimRule.memberCell scope args).size`), classifier (`universeCode`) FIXED;
  * the **base branch** obligation: subject FIXED, classifier `subst0 motive natZero` drifts via a `Conv`, the
    after-formedness `subst0 motiveAfter natZero` supplied DIRECTLY by
    `dependentMotiveOutputFormed_ofMotiveAndArgument` from the motive's re-typed universe membership and `natZero :
    natType` (`consClassifierConv`);
  * the **step branch** obligation: context-head AND classifier drift, the after-formedness
    `natElimDependentSuccBranchType motiveAfter` supplied DIRECTLY by
    `natElimDependentSuccBranchType_formed_ofMotive` from the re-typed motive (`consContextHeadConv`).

The re-typed motive `motiveAfter : universeCode` is recovered from the FUEL-BOUNDED child-SR
(`universeMembershipPreservedUnderStepBelow`) — the motive IS a structural cell-child, so `motive.size < bound`,
and the bounded child-SR re-types it (NOT the whole branch type, which can exceed the bound).  Every other arg
position is context-fixed and clean (`SubjectDriftBelow`).  `natRec` reuses `natElim`'s drift by definitional
equality of the two `obligations` / `memberCell`-size projections.

## Zero-axiom

`cases` on the (mutual-inductive) `StepChildren` + `ObligationsDriftBelow.{cons,consClassifierConv,
consContextHeadConv}` + the shipped motive-step congruence / formedness lemmas + the FUEL-BOUNDED child-SR +
`Conv.fromStep{Star}` + `universeFormation` + a nullary `natZero` intro.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **`natZero : natType` in any context.**  The nullary `natZero` introducer typed at `natTypeCell` — the data
argument the base-branch output-formedness (`dependentMotiveOutputFormed_ofMotiveAndArgument`) substitutes for the
motive's binder.  Built directly from the `natZero` intro row (empty obligations, vacuous side condition). -/
theorem natZeroTypedInContext {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope) :
    HasTypeUnion profile context natZeroCell natTypeCell := by
  refine HasTypeUnion.intro context .gen_natZero natZeroIntroRule .childNil .childNil
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
  intro obligation hmem
  cases hmem

/-- **A universe-code membership survives one reduction step at its SAME universe code — FUEL-BOUNDED.**  The
bounded twin of `universeMembershipPreservedUnderStep`: given `subject : universeCode level flag`, `subject ⟶
subjectAfter`, and `subject.size < bound`, the FUEL-BOUNDED child-SR re-types the reduct and universe rigidity pins
it back to the SAME `universeCode level flag`.  This is the bounded typed witness feeding the recursors'
after-branch formedness from the re-typed motive. -/
theorem universeMembershipPreservedUnderStepBelow {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject subjectAfter : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag} {bound : Nat}
    (subjectTyped : HasTypeUnion profile context subject (universeCodeCell level flag))
    (subjectStep : Step subject subjectAfter)
    (subjectBelow : subject.size < bound)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile bound) :
    HasTypeUnion profile context subjectAfter (universeCodeCell level flag) := by
  obtain ⟨afterType, afterTyped, convClassifier⟩ := childSubjectReductionBelow subjectBelow subjectTyped subjectStep
  exact HasTypeUnion.reclassifyToType afterTyped convClassifier.sym
    ⟨_, _, HasTypeUnion.universeFormation context level flag⟩

/-- **★ `natElim`'s fuel-bounded obligation drift under one arg step.**  The bounded twin of
`natElimObligationsDriftUnderArgStep`: a motive step drifts the base branch (`consClassifierConv`), the step branch
(`consContextHeadConv`) and the motive subject (`SubjectDriftBelow.stepsBelow`); any other child step drifts only
that subject.  Consumes `UnionChildSubjectReductionBelow profile (natElimRule.memberCell scope args).size`. -/
theorem natElimObligationsDriftUnderArgStepBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {baseBranch scrutinee : RawTerm scope} {stepBranch : RawTerm (scope + 2)}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (motiveTyped : HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell level0 flag))
    (scrutineeClassifierFormed : UnionClassifierIsType profile context natTypeCell)
    (baseBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive natZeroCell))
    (stepBranchClassifierFormed : UnionClassifierIsType profile ((context.cons natTypeCell).cons motive)
      (natElimDependentSuccBranchType motive))
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile
      (natElimRule.memberCell scope
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))).size)
    {argsAfter : RawTermChildren [1, 0, 2, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 2, 0] scope) argsAfter) :
    ObligationsDriftBelow profile
      (natElimRule.memberCell scope
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))).size
      (natElimRule.obligations scope context
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
        .childNil level0 level1 flag)
      (natElimRule.obligations scope context argsAfter .childNil level0 level1 flag) := by
  have motiveClassifierFormed : UnionClassifierIsType profile (context.cons natTypeCell)
      (universeCodeCell level0 flag) :=
    ⟨_, _, HasTypeUnion.universeFormation (context.cons natTypeCell) level0 flag⟩
  have motiveBindingFormed : UnionClassifierIsType profile (context.cons natTypeCell) motive :=
    ⟨level0, flag, motiveTyped⟩
  cases childStep with
  | here _ motiveStep =>
      have motiveAfterTyped := universeMembershipPreservedUnderStepBelow motiveTyped motiveStep
        (headChildBelowCellSize 1 motive _) childSubjectReductionBelow
      have baseBranchFormedAfter := UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument
        context natTypeCell _ natZeroCell level0 flag motiveAfterTyped (natZeroTypedInContext context)
      have stepBranchFormedAfter : UnionClassifierIsType profile
          ((context.cons natTypeCell).cons _) (natElimDependentSuccBranchType _) :=
        ⟨level0, flag, natElimDependentSuccBranchType_formed_ofMotive context _ level0 flag motiveAfterTyped⟩
      exact ObligationsDriftBelow.cons (.fixed scrutinee) scrutineeClassifierFormed
        (ObligationsDriftBelow.consClassifierConv
          (Conv.fromStepStar (StepStar.subst0Body natZeroCell (StepStar.single motiveStep))) baseBranchFormedAfter
          (ObligationsDriftBelow.consContextHeadConv (Conv.fromStep motiveStep) motiveBindingFormed
            (natElimDependentSuccBranchType_isConvStableUnderMotiveStep motiveStep) stepBranchFormedAfter
            (ObligationsDriftBelow.cons (.stepsBelow motiveStep (headChildBelowCellSize 1 motive _))
              motiveClassifierFormed ObligationsDriftBelow.nil)))
  | there _ tail1 =>
      cases tail1 with
      | here _ baseBranchStep =>
          exact ObligationsDriftBelow.cons (.fixed scrutinee) scrutineeClassifierFormed
            (ObligationsDriftBelow.cons (.stepsBelow baseBranchStep (secondChildBelowCellSize 1 0 motive baseBranch _))
              baseBranchClassifierFormed
              (ObligationsDriftBelow.cons (.fixed stepBranch) stepBranchClassifierFormed
                (ObligationsDriftBelow.cons (.fixed motive) motiveClassifierFormed ObligationsDriftBelow.nil)))
      | there _ tail2 =>
          cases tail2 with
          | here _ stepBranchStep =>
              exact ObligationsDriftBelow.cons (.fixed scrutinee) scrutineeClassifierFormed
                (ObligationsDriftBelow.cons (.fixed baseBranch) baseBranchClassifierFormed
                  (ObligationsDriftBelow.cons
                    (.stepsBelow stepBranchStep (thirdChildBelowCellSize 1 0 2 motive baseBranch stepBranch _))
                    stepBranchClassifierFormed
                    (ObligationsDriftBelow.cons (.fixed motive) motiveClassifierFormed ObligationsDriftBelow.nil)))
          | there _ tail3 =>
              cases tail3 with
              | here _ scrutineeStep =>
                  exact ObligationsDriftBelow.cons
                    (.stepsBelow scrutineeStep
                      (fourthChildBelowCellSize 1 0 2 0 motive baseBranch stepBranch scrutinee _))
                    scrutineeClassifierFormed
                    (ObligationsDriftBelow.cons (.fixed baseBranch) baseBranchClassifierFormed
                      (ObligationsDriftBelow.cons (.fixed stepBranch) stepBranchClassifierFormed
                        (ObligationsDriftBelow.cons (.fixed motive) motiveClassifierFormed ObligationsDriftBelow.nil)))
              | there _ emptyTailStep => cases emptyTailStep

/-- **`natRec`'s fuel-bounded obligation drift** — `natRec` shares `natElim`'s obligation function and `memberCell`
size verbatim (the rules differ only in the cell former), so its bounded drift IS `natElim`'s, accepted by
definitional equality of the two projections. -/
theorem natRecElimObligationsDriftUnderArgStepBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {baseBranch scrutinee : RawTerm scope} {stepBranch : RawTerm (scope + 2)}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (motiveTyped : HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell level0 flag))
    (scrutineeClassifierFormed : UnionClassifierIsType profile context natTypeCell)
    (baseBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive natZeroCell))
    (stepBranchClassifierFormed : UnionClassifierIsType profile ((context.cons natTypeCell).cons motive)
      (natElimDependentSuccBranchType motive))
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile
      (natRecElimRule.memberCell scope
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))).size)
    {argsAfter : RawTermChildren [1, 0, 2, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 2, 0] scope) argsAfter) :
    ObligationsDriftBelow profile
      (natRecElimRule.memberCell scope
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))).size
      (natRecElimRule.obligations scope context
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
        .childNil level0 level1 flag)
      (natRecElimRule.obligations scope context argsAfter .childNil level0 level1 flag) :=
  natElimObligationsDriftUnderArgStepBounded level0 level1 flag motiveTyped scrutineeClassifierFormed
    baseBranchClassifierFormed stepBranchClassifierFormed childSubjectReductionBelow childStep

end FX1Poly.Typed
