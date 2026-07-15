import FX1Poly.Typed.Metatheory.SubjectReduction.ElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentBranchTypeMotiveCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentBranchTypeFormedFromMotive

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/RecursorElimObligationsDrift
    — SR-DSL-4: `ObligationsDrift` for the BINDER-EXTENDED recursors (`natElim` / `natRec`)

`natElim` / `natRec` are the only eliminators whose step-branch obligation lives in a context whose HEAD binding
IS the motive: `(context.cons natTypeCell).cons motive` at `scope + 2`.  When the motive steps, that obligation's
context drifts (`motive ⟶ motiveAfter` in the head) AND its classifier drifts
(`natElimDependentSuccBranchType motive ⟶ … motiveAfter`).  This is exactly the `ObligationsDrift.consContext-
HeadConv` case — convert the head binding, then reclassify the classifier along its `Conv`-drift, with the
after-classifier formedness supplied DIRECTLY (the motive's universe typing carried forward through the step, then
`natElimDependentSuccBranchType_formed_ofMotive`), NOT derived by SR (the SR keystone needs a fixed context, which
this position does not have).

Every OTHER arg position is context-fixed and uses the ordinary `ObligationsDrift.cons`: the scrutinee at `natType`
(constant), the base branch at `subst0 motive natZero` (the `subst0Body` motive drift), and the motive obligation
itself at its `universeCode` (subject drifts, `universeCode` classifier fixed, `context.cons natType` fixed because
`natType` is motive-independent).

`natRec` shares `natElim`'s obligation function verbatim (the rules differ only in the cell former), so its drift
is `natElim`'s, reused by definitional equality of the two `obligations` projections.

## Zero-axiom

`cases` on the (mutual-inductive) `StepChildren` + `ObligationsDrift.{cons,consContextHeadConv}` + the shipped
motive-step congruence / formedness lemmas + `childSubjectReduction` + `universeFormation` (for the universe-code
re-pin).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-- **A universe-code membership survives one reduction step at its SAME universe code.**  Given
`subject : universeCode level flag` and `subject ⟶ subjectAfter`, single-step subject reduction re-types the reduct
at a `Conv`-equal classifier and universe rigidity (`reclassifyToType` over `universeFormation`) pins it back to the
SAME `universeCode level flag`.  This is `UnionClassifierIsType.preservedUnderStep` at typed strength — the
binder-extended recursor drift needs the TYPED witness (to feed `natElimDependentSuccBranchType_formed_ofMotive`),
not merely `IsType`. -/
theorem universeMembershipPreservedUnderStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject subjectAfter : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (subjectTyped : HasTypeUnion profile context subject (universeCodeCell level flag))
    (subjectStep : Step subject subjectAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    HasTypeUnion profile context subjectAfter (universeCodeCell level flag) := by
  obtain ⟨afterType, afterTyped, convClassifier⟩ := childSubjectReduction subjectTyped subjectStep
  exact HasTypeUnion.reclassifyToType afterTyped convClassifier.sym
    ⟨_, _, HasTypeUnion.universeFormation context level flag⟩

/-- **★ `natElim`'s obligation drift under one arg step — the binder-extended recursor.**  Four obligations:
scrutinee at `natType`, base branch at `subst0 motive natZero`, step branch at `natElimDependentSuccBranchType
motive` in the two-binder context `(context.cons natType).cons motive`, and the motive at its universe code in
`context.cons natType`.  When the motive (arg 0) steps, the step-branch obligation drifts in BOTH context-head and
classifier (`consContextHeadConv`); the base branch's classifier drifts (`subst0Body`); the motive's own subject
drifts.  When any other child steps, only that subject drifts (every context is then fixed).

The motive's universe typing `motiveTyped` is gate-supplied (it IS the motive obligation's premise); it feeds both
the head-binding formedness `⟨_, _, motiveTyped⟩` and — carried across the step — the after-step-branch formedness. -/
theorem natElimObligationsDriftUnderArgStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {baseBranch scrutinee : RawTerm scope} {stepBranch : RawTerm (scope + 2)}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (motiveTyped : HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell level0 flag))
    (scrutineeClassifierFormed : UnionClassifierIsType profile context natTypeCell)
    (baseBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive natZeroCell))
    (stepBranchClassifierFormed : UnionClassifierIsType profile ((context.cons natTypeCell).cons motive)
      (natElimDependentSuccBranchType motive))
    (childSubjectReduction : UnionChildSubjectReduction profile)
    {argsAfter : RawTermChildren [1, 0, 2, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 2, 0] scope) argsAfter) :
    ObligationsDrift profile
      (natElimRule.obligations scope context
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
        .childNil level0 level1 flag)
      (natElimRule.obligations scope context argsAfter .childNil level0 level1 flag) := by
  -- The motive obligation's `universeCode` classifier is formed unconditionally; the head-binding formedness is the
  -- motive's universe typing repackaged.
  have motiveClassifierFormed : UnionClassifierIsType profile (context.cons natTypeCell)
      (universeCodeCell level0 flag) :=
    ⟨_, _, HasTypeUnion.universeFormation (context.cons natTypeCell) level0 flag⟩
  have motiveBindingFormed : UnionClassifierIsType profile (context.cons natTypeCell) motive :=
    ⟨level0, flag, motiveTyped⟩
  cases childStep with
  | here _ motiveStep =>
      -- The motive carried across the step (typed witness), then the after-step-branch formedness.
      have motiveAfterTyped := universeMembershipPreservedUnderStep motiveTyped motiveStep childSubjectReduction
      have stepBranchFormedAfter : UnionClassifierIsType profile
          ((context.cons natTypeCell).cons _) (natElimDependentSuccBranchType _) :=
        ⟨level0, flag, natElimDependentSuccBranchType_formed_ofMotive context _ level0 flag motiveAfterTyped⟩
      exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
        (ObligationsDrift.cons (StepStar.refl _)
          (StepStar.subst0Body natZeroCell (StepStar.single motiveStep)) baseBranchClassifierFormed
          (ObligationsDrift.consContextHeadConv (Conv.fromStep motiveStep) motiveBindingFormed
            (natElimDependentSuccBranchType_isConvStableUnderMotiveStep motiveStep) stepBranchFormedAfter
            (ObligationsDrift.cons (StepStar.single motiveStep) (StepStar.refl _) motiveClassifierFormed
              ObligationsDrift.nil)))
  | there _ tail1 =>
      cases tail1 with
      | here _ baseBranchStep =>
          exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
            (ObligationsDrift.cons (StepStar.single baseBranchStep) (StepStar.refl _) baseBranchClassifierFormed
              (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) stepBranchClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                  ObligationsDrift.nil)))
      | there _ tail2 =>
          cases tail2 with
          | here _ stepBranchStep =>
              exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) baseBranchClassifierFormed
                  (ObligationsDrift.cons (StepStar.single stepBranchStep) (StepStar.refl _)
                    stepBranchClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                      ObligationsDrift.nil)))
          | there _ tail3 =>
              cases tail3 with
              | here _ scrutineeStep =>
                  exact ObligationsDrift.cons (StepStar.single scrutineeStep) (StepStar.refl _)
                    scrutineeClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) baseBranchClassifierFormed
                      (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) stepBranchClassifierFormed
                        (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                          ObligationsDrift.nil)))
              | there _ emptyTailStep => cases emptyTailStep

/-- **`natRec`'s obligation drift under one arg step** — `natRec` shares `natElim`'s obligation function verbatim
(the rules differ only in the cell former, not the obligations / argShifts), so its drift IS `natElim`'s, accepted
by definitional equality of the two `obligations` projections. -/
theorem natRecElimObligationsDriftUnderArgStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {baseBranch scrutinee : RawTerm scope} {stepBranch : RawTerm (scope + 2)}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (motiveTyped : HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell level0 flag))
    (scrutineeClassifierFormed : UnionClassifierIsType profile context natTypeCell)
    (baseBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive natZeroCell))
    (stepBranchClassifierFormed : UnionClassifierIsType profile ((context.cons natTypeCell).cons motive)
      (natElimDependentSuccBranchType motive))
    (childSubjectReduction : UnionChildSubjectReduction profile)
    {argsAfter : RawTermChildren [1, 0, 2, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 2, 0] scope) argsAfter) :
    ObligationsDrift profile
      (natRecElimRule.obligations scope context
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
        .childNil level0 level1 flag)
      (natRecElimRule.obligations scope context argsAfter .childNil level0 level1 flag) :=
  natElimObligationsDriftUnderArgStep level0 level1 flag motiveTyped scrutineeClassifierFormed
    baseBranchClassifierFormed stepBranchClassifierFormed childSubjectReduction childStep

end FX1Poly.Typed
