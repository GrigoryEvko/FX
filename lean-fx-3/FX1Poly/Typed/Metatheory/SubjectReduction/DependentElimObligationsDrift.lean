import FX1Poly.Typed.Metatheory.SubjectReduction.ElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.DataEliminatorBranchTypeStepStable
import FX1Poly.Typed.Metatheory.SubjectReduction.TemplateStepStarUnderChildStep

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/DependentElimObligationsDrift
    — SR-DSL-4: `ObligationsDrift` from an arg step for the AMBIENT-context dependent eliminators

`optionMatch` / `eitherMatch` / `boolElim` are the dependent eliminators whose obligations are ALL context-fixed:
the branch obligations sit at the ambient context (their branch TYPE is a `piTyCode`, the binder is inside the
type), and the motive obligation sits at `context.cons <scrutineeType>` where `<scrutineeType>`
(`boolType` / `optionType A` / `eitherType A B`) is a PARAM / constant — motive-INDEPENDENT — so that context is
fixed under a motive step too.  Hence all four obligations fit the context-fixed `ObligationsDrift` and feed
`premisesHoldUnderObligationsDrift` directly.

This file builds each row's `ObligationsDrift` under one arg step.  The `cases` splits the four child positions
(motive / two branches / scrutinee) plus the empty tail.  When the MOTIVE steps the branch classifiers drift —
the dependent-branch types via the shipped `*_stepStable` lemmas, the `subst0`-re-based branches via
`StepStar.subst0Body` — while the motive obligation's own subject drifts and its `universeCode` classifier stays
put; when a branch / scrutinee steps only that subject drifts and every classifier is fixed.

The classifier-formedness witnesses are gate-supplied (via `classifierIsType` over `WfContextUnion`); the motive
obligation's `universeCode` formedness is constructed inline (`universeFormation` is unconditional).

## Zero-axiom

`cases` on the (mutual-inductive) `StepChildren` + `StepStar.{single,refl,subst0Body}` + the shipped `*_stepStable`
lemmas + `ObligationsDrift` constructors + `universeFormation`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **`optionMatch`'s obligation drift under one arg step.**  Four obligations — scrutinee at `optionType A`,
noneBranch at `subst0 motive optionNone`, someBranch at the dependent some-branch type, and the motive at its
universe code (in `context.cons (optionType A)`).  A motive step drifts the two motive-reading branch classifiers
(`subst0Body` for none, `_stepStable` for some) and the motive obligation's subject; any other child step drifts
only that subject. -/
theorem optionMatchObligationsDriftUnderArgStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch scrutinee typeParamA typeParamB : RawTerm scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (scrutineeClassifierFormed : UnionClassifierIsType profile context (optionTypeCell typeParamA))
    (noneBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive optionNoneCell))
    (someBranchClassifierFormed : UnionClassifierIsType profile context
      (optionMatchDependentSomeBranchType motive typeParamA))
    {argsAfter : RawTermChildren [1, 0, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 0, 0] scope) argsAfter) :
    ObligationsDrift profile
      (optionMatchElimRule.obligations scope context
        (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))
        (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag)
      (optionMatchElimRule.obligations scope context argsAfter
        (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag) := by
  -- The motive obligation's `universeCode` classifier is formed unconditionally.
  have motiveClassifierFormed : UnionClassifierIsType profile (context.cons (optionTypeCell typeParamA))
      (universeCodeCell level0 flag) :=
    ⟨_, _, HasTypeUnion.universeFormation (context.cons (optionTypeCell typeParamA)) level0 flag⟩
  cases childStep with
  | here _ motiveStep =>
      exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
        (ObligationsDrift.cons (StepStar.refl _) (StepStar.subst0Body optionNoneCell (StepStar.single motiveStep))
          noneBranchClassifierFormed
          (ObligationsDrift.cons (StepStar.refl _)
            (optionMatchDependentSomeBranchType_stepStable (StepStar.single motiveStep)) someBranchClassifierFormed
            (ObligationsDrift.cons (StepStar.single motiveStep) (StepStar.refl _) motiveClassifierFormed
              ObligationsDrift.nil)))
  | there _ tail1 =>
      cases tail1 with
      | here _ noneBranchStep =>
          exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
            (ObligationsDrift.cons (StepStar.single noneBranchStep) (StepStar.refl _) noneBranchClassifierFormed
              (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) someBranchClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                  ObligationsDrift.nil)))
      | there _ tail2 =>
          cases tail2 with
          | here _ someBranchStep =>
              exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) noneBranchClassifierFormed
                  (ObligationsDrift.cons (StepStar.single someBranchStep) (StepStar.refl _)
                    someBranchClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                      ObligationsDrift.nil)))
          | there _ tail3 =>
              cases tail3 with
              | here _ scrutineeStep =>
                  exact ObligationsDrift.cons (StepStar.single scrutineeStep) (StepStar.refl _)
                    scrutineeClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) noneBranchClassifierFormed
                      (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) someBranchClassifierFormed
                        (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                          ObligationsDrift.nil)))
              | there _ emptyTailStep => cases emptyTailStep

/-- **`eitherMatch`'s obligation drift under one arg step** — the two-branch twin of `optionMatch`, with both the
inl and inr branch classifiers drifting (via their `_stepStable` lemmas) when the motive steps. -/
theorem eitherMatchObligationsDriftUnderArgStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch scrutinee typeParamA typeParamB : RawTerm scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (scrutineeClassifierFormed : UnionClassifierIsType profile context (eitherTypeCell typeParamA typeParamB))
    (leftBranchClassifierFormed : UnionClassifierIsType profile context
      (eitherMatchDependentInlBranchType motive typeParamA))
    (rightBranchClassifierFormed : UnionClassifierIsType profile context
      (eitherMatchDependentInrBranchType motive typeParamB))
    {argsAfter : RawTermChildren [1, 0, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 0, 0] scope) argsAfter) :
    ObligationsDrift profile
      (eitherMatchElimRule.obligations scope context
        (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))
        (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag)
      (eitherMatchElimRule.obligations scope context argsAfter
        (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag) := by
  have motiveClassifierFormed : UnionClassifierIsType profile
      (context.cons (eitherTypeCell typeParamA typeParamB)) (universeCodeCell level0 flag) :=
    ⟨_, _, HasTypeUnion.universeFormation (context.cons (eitherTypeCell typeParamA typeParamB)) level0 flag⟩
  cases childStep with
  | here _ motiveStep =>
      exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
        (ObligationsDrift.cons (StepStar.refl _)
          (eitherMatchDependentInlBranchType_stepStable (StepStar.single motiveStep)) leftBranchClassifierFormed
          (ObligationsDrift.cons (StepStar.refl _)
            (eitherMatchDependentInrBranchType_stepStable (StepStar.single motiveStep)) rightBranchClassifierFormed
            (ObligationsDrift.cons (StepStar.single motiveStep) (StepStar.refl _) motiveClassifierFormed
              ObligationsDrift.nil)))
  | there _ tail1 =>
      cases tail1 with
      | here _ leftBranchStep =>
          exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
            (ObligationsDrift.cons (StepStar.single leftBranchStep) (StepStar.refl _) leftBranchClassifierFormed
              (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) rightBranchClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                  ObligationsDrift.nil)))
      | there _ tail2 =>
          cases tail2 with
          | here _ rightBranchStep =>
              exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) leftBranchClassifierFormed
                  (ObligationsDrift.cons (StepStar.single rightBranchStep) (StepStar.refl _)
                    rightBranchClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                      ObligationsDrift.nil)))
          | there _ tail3 =>
              cases tail3 with
              | here _ scrutineeStep =>
                  exact ObligationsDrift.cons (StepStar.single scrutineeStep) (StepStar.refl _)
                    scrutineeClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) leftBranchClassifierFormed
                      (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) rightBranchClassifierFormed
                        (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                          ObligationsDrift.nil)))
              | there _ emptyTailStep => cases emptyTailStep

/-- **`boolElim`'s obligation drift under one arg step.**  Like `optionMatch` but both branches are `subst0`-re-based
(`motive[true]` / `motive[false]`), so a motive step drifts both branch classifiers via `StepStar.subst0Body`; the
scrutinee is at `boolType`, the motive at its universe code in `context.cons boolType`.  `boolElim` has no type
params. -/
theorem boolElimObligationsDriftUnderArgStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (scrutineeClassifierFormed : UnionClassifierIsType profile context boolTypeCell)
    (thenBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive (RawTerm.mkGen .gen_boolTrue () .childNil)))
    (elseBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive (RawTerm.mkGen .gen_boolFalse () .childNil)))
    {argsAfter : RawTermChildren [1, 0, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))
        : RawTermChildren [1, 0, 0, 0] scope) argsAfter) :
    ObligationsDrift profile
      (boolElimRule.obligations scope context
        (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))))
        .childNil level0 level1 flag)
      (boolElimRule.obligations scope context argsAfter .childNil level0 level1 flag) := by
  have motiveClassifierFormed : UnionClassifierIsType profile (context.cons boolTypeCell)
      (universeCodeCell level0 flag) :=
    ⟨_, _, HasTypeUnion.universeFormation (context.cons boolTypeCell) level0 flag⟩
  cases childStep with
  | here _ motiveStep =>
      exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
        (ObligationsDrift.cons (StepStar.refl _)
          (StepStar.subst0Body (RawTerm.mkGen .gen_boolTrue () .childNil) (StepStar.single motiveStep))
          thenBranchClassifierFormed
          (ObligationsDrift.cons (StepStar.refl _)
            (StepStar.subst0Body (RawTerm.mkGen .gen_boolFalse () .childNil) (StepStar.single motiveStep))
            elseBranchClassifierFormed
            (ObligationsDrift.cons (StepStar.single motiveStep) (StepStar.refl _) motiveClassifierFormed
              ObligationsDrift.nil)))
  | there _ tail1 =>
      cases tail1 with
      | here _ scrutineeStep =>
          exact ObligationsDrift.cons (StepStar.single scrutineeStep) (StepStar.refl _) scrutineeClassifierFormed
            (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) thenBranchClassifierFormed
              (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) elseBranchClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                  ObligationsDrift.nil)))
      | there _ tail2 =>
          cases tail2 with
          | here _ thenBranchStep =>
              exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
                (ObligationsDrift.cons (StepStar.single thenBranchStep) (StepStar.refl _) thenBranchClassifierFormed
                  (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) elseBranchClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                      ObligationsDrift.nil)))
          | there _ tail3 =>
              cases tail3 with
              | here _ elseBranchStep =>
                  exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) thenBranchClassifierFormed
                      (ObligationsDrift.cons (StepStar.single elseBranchStep) (StepStar.refl _)
                        elseBranchClassifierFormed
                        (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                          ObligationsDrift.nil)))
              | there _ emptyTailStep => cases emptyTailStep

/-- **`listElim`'s obligation drift under one arg step** — the recursive list eliminator.  Although `listElim`'s
cons branch is a THREE-binder dependent recursive function, that whole binder nest lives INSIDE the branch TYPE
`listElimDependentConsBranchType motive elementType` (a `piTyCode` curry at the AMBIENT scope), so every
obligation context is fixed — `listElim` is context-fixed exactly like `optionMatch` / `eitherMatch`.  A motive
step drifts the nil-branch classifier (`subst0Body listNil`) and the cons-branch classifier (the recursive
`_stepStable` lemma, element type held fixed) plus the motive subject; any other child step drifts one subject. -/
theorem listElimObligationsDriftUnderArgStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch elementType resultType : RawTerm scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (scrutineeClassifierFormed : UnionClassifierIsType profile context (listTypeCell elementType))
    (nilBranchClassifierFormed : UnionClassifierIsType profile context
      (RawTerm.subst0 motive listNilCell))
    (consBranchClassifierFormed : UnionClassifierIsType profile context
      (listElimDependentConsBranchType motive elementType))
    {argsAfter : RawTermChildren [1, 0, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))
        : RawTermChildren [1, 0, 0, 0] scope) argsAfter) :
    ObligationsDrift profile
      (listElimRule.obligations scope context
        (.childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))))
        (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag)
      (listElimRule.obligations scope context argsAfter
        (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag) := by
  have motiveClassifierFormed : UnionClassifierIsType profile (context.cons (listTypeCell elementType))
      (universeCodeCell level0 flag) :=
    ⟨_, _, HasTypeUnion.universeFormation (context.cons (listTypeCell elementType)) level0 flag⟩
  cases childStep with
  | here _ motiveStep =>
      exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
        (ObligationsDrift.cons (StepStar.refl _)
          (StepStar.subst0Body listNilCell (StepStar.single motiveStep)) nilBranchClassifierFormed
          (ObligationsDrift.cons (StepStar.refl _)
            (listElimDependentConsBranchType_stepStable (StepStar.single motiveStep) (StepStar.refl elementType))
            consBranchClassifierFormed
            (ObligationsDrift.cons (StepStar.single motiveStep) (StepStar.refl _) motiveClassifierFormed
              ObligationsDrift.nil)))
  | there _ tail1 =>
      cases tail1 with
      | here _ scrutineeStep =>
          exact ObligationsDrift.cons (StepStar.single scrutineeStep) (StepStar.refl _) scrutineeClassifierFormed
            (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) nilBranchClassifierFormed
              (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) consBranchClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                  ObligationsDrift.nil)))
      | there _ tail2 =>
          cases tail2 with
          | here _ nilBranchStep =>
              exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
                (ObligationsDrift.cons (StepStar.single nilBranchStep) (StepStar.refl _) nilBranchClassifierFormed
                  (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) consBranchClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                      ObligationsDrift.nil)))
          | there _ tail3 =>
              cases tail3 with
              | here _ consBranchStep =>
                  exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) scrutineeClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) nilBranchClassifierFormed
                      (ObligationsDrift.cons (StepStar.single consBranchStep) (StepStar.refl _)
                        consBranchClassifierFormed
                        (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                          ObligationsDrift.nil)))
              | there _ emptyTailStep => cases emptyTailStep

/-- **`idJ`'s obligation drift under one arg step** — genuine Paulin-Mohring path induction.  Although `idJ`'s
motive obligation sits at the two-binder context `(context.cons typeCode).cons (idJMotiveSecondBinderType typeCode
left)`, that context head `idJMotiveSecondBinderType typeCode left` is MOTIVE-INDEPENDENT (it reads only the
params), so it is fixed under a motive step — `idJ` is context-fixed.  When the motive steps, only the base-case
classifier `idJMotiveAt motive left (refl left)` drifts (via `idJMotiveAt_bodyStepStable`, a `subst` body
congruence) plus the motive subject; any other child step drifts one subject.  Three args (`motive` at binderShift
2, `baseCase`, `witness`); three params (`typeCode`, `leftEndpoint`, `rightEndpoint`). -/
theorem idJObligationsDriftUnderArgStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 2)} {baseCase witness typeParamCode leftEndpoint rightEndpoint : RawTerm scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (witnessClassifierFormed : UnionClassifierIsType profile context
      (idTypeCell typeParamCode leftEndpoint rightEndpoint))
    (rightEndpointClassifierFormed : UnionClassifierIsType profile context typeParamCode)
    (baseCaseClassifierFormed : UnionClassifierIsType profile context
      (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)))
    {argsAfter : RawTermChildren [2, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons baseCase (.childCons witness .childNil))
        : RawTermChildren [2, 0, 0] scope) argsAfter) :
    ObligationsDrift profile
      (idJElimRule.obligations scope context
        (.childCons motive (.childCons baseCase (.childCons witness .childNil)))
        (.childCons typeParamCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
        level0 level1 flag)
      (idJElimRule.obligations scope context argsAfter
        (.childCons typeParamCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
        level0 level1 flag) := by
  have motiveClassifierFormed : UnionClassifierIsType profile
      ((context.cons typeParamCode).cons (idJMotiveSecondBinderType typeParamCode leftEndpoint))
      (universeCodeCell level0 flag) :=
    ⟨_, _, HasTypeUnion.universeFormation
      ((context.cons typeParamCode).cons (idJMotiveSecondBinderType typeParamCode leftEndpoint)) level0 flag⟩
  cases childStep with
  | here _ motiveStep =>
      exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) witnessClassifierFormed
        (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) rightEndpointClassifierFormed
          (ObligationsDrift.cons (StepStar.refl _)
            (idJMotiveAt_bodyStepStable leftEndpoint (reflCell leftEndpoint) (StepStar.single motiveStep))
            baseCaseClassifierFormed
            (ObligationsDrift.cons (StepStar.single motiveStep) (StepStar.refl _) motiveClassifierFormed
              ObligationsDrift.nil)))
  | there _ tail1 =>
      cases tail1 with
      | here _ baseCaseStep =>
          exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) witnessClassifierFormed
            (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) rightEndpointClassifierFormed
              (ObligationsDrift.cons (StepStar.single baseCaseStep) (StepStar.refl _) baseCaseClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                  ObligationsDrift.nil)))
      | there _ tail2 =>
          cases tail2 with
          | here _ witnessStep =>
              exact ObligationsDrift.cons (StepStar.single witnessStep) (StepStar.refl _) witnessClassifierFormed
                (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) rightEndpointClassifierFormed
                  (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) baseCaseClassifierFormed
                    (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) motiveClassifierFormed
                      ObligationsDrift.nil)))
          | there _ emptyTailStep => cases emptyTailStep

end FX1Poly.Typed
