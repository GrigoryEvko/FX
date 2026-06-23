import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion

/-! # FX1Poly/Typed/HasTypeUnionRecursiveInversion — NATIVE-37 part d: per-head inversions for the
    remaining recursive eliminator heads (natRec and listElim).

The `natElim` head shipped in `HasTypeUnionInversion`; this file adds its `gen_natRec` twin (the
`natRecElimRule` row of `elimRuleOf`) and the `listElim` head (the `listElimRule` row).

  * **natRec** — survivor is the unified `elim` arm pinned to the `gen_natRec` row.  Surfaced premises:
    the scrutinee union-typed at `Nat`, the base (zero) branch union-typed at the classifier.  Identical
    in shape to `invertAtNatElimHead`, only the surviving row differs (`natRecElimRule` vs `natElimRule`,
    same `[1, 0, 2, 0]` arg shifts and obligation list `[scrutinee@Nat, base@result, step@scope+2]`).
  * **listElim** — survivor is the unified `elim` arm pinned to the `gen_listElim` row.  Surfaced premises:
    the scrutinee UNION-typed at `List(elementType)` (the NATIVE-42 re-shape made the scrutinee premise
    union-recursive, retiring the last zoo judgment named inside the union), the nil/cons branches
    UNION-typed at the result / 3-arg curried step type.  THE TYTAB-1 ELIM-COLLAPSE RESHAPE: the nil/cons
    branches were GROWN premises in the pre-collapse `listElim` arm; the unified `elimRuleOf` table makes
    every branch a union obligation (`ElimRuleTable.listElimRule.obligations`), so the surfaced branch
    premises are now `HasTypeUnion`, not `HasTypeDescPi`.  The reverse adequacy for listElim is therefore
    RELATIVIZED like every other head (the scrutinee reconstruction map is where computed-list scrutinees
    fall outside the bespoke engine).

## Zero-axiom

Free-subject `induction` + the shipped `elimRuleOf_cases` row inverter + the `elimMemberCellRootGenerator`
head-projection helper + `rcases subjectShape with ⟨⟩`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (1) Inversion at the natRec head -/

/-- **★ Inversion at the natRec head.**  A union typing of a `natRecCell`-headed subject is EXACTLY a
recursive-eliminator typing at the `gen_natRec` row of `elimRuleOf`: the scrutinee is union-typed at `Nat`
and the base (zero) branch is union-typed at the classifier.  (The motive and step branch are stored, not
surfaced — premise parity with the natElim twin.)  No grown disjunct: `natRecCell` is untypable in the
grown engine.  The `gen_natRec` twin of `HasTypeUnion.invertAtNatElimHead`. -/
theorem HasTypeUnion.invertAtNatRecHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = natRecCell motive zeroBranch stepBranch scrutinee) :
    HasTypeUnion profile context scrutinee natTypeCell ∧
    HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
    Conv (RawTerm.subst0 motive scrutinee) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨scrutineeTyped, zeroBranchTyped, outputConv⟩ := innerInversion subjectShape
      exact ⟨scrutineeTyped, zeroBranchTyped, outputConv.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.natRecCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      ihPremises =>
      -- The unified introducer arm: no introducer row produces a `natRec`-headed cell (natRec is an
      -- eliminator), so every introducer row's generator clashes with `gen_natRec`.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: pin BOTH the generator and the row.  Only the `gen_natRec` row
      -- survives (its member cell IS the natRec cell); the other ten eliminator heads clash with the
      -- `natRec` subject head (`memberCellHead = generator` from `elimMemberCellRootGenerator`, then a
      -- concrete clash).
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- app
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathApp
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ natRec — the SURVIVOR.  Destructure the children (no params — the dependent rule has
      -- `paramShifts = []`); surface the scrutinee at `Nat` + base branch at `subst0 motive natZeroCell`;
      -- the output `subst0 motive scrutinee` IS the classifier, so the conversion leg is `Conv.refl`.
      · match args with
        | .childCons _armMotive (.childCons _armBase (.childCons _armStep (.childCons _armScrut .childNil))) =>
          rcases subjectShape with ⟨⟩
          exact ⟨premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)),
            Conv.refl _⟩
      -- boolElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- idJ
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- fst
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- snd
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

/-- **★ Full inversion at the natRec head — all four DEPENDENT `natRecElimRule` premises surfaced.**  The richer
twin of `invertAtNatRecHead`, and the `gen_natRec` mirror of `invertAtNatElimHeadAllPremises`: a union typing of
a `natRecCell`-headed subject surfaces the scrutinee at `Nat`, the base branch at its dependent zero type
`subst0 motive natZeroCell`, the step branch at the two-binder dependent succ type
`natElimDependentSuccBranchType motive` in `(context.cons natTypeCell).cons motive`, the motive's universe
formedness over `context.cons natTypeCell`, and the `Conv` of the dependent output `subst0 motive scrutinee` to
the ambient classifier.  `natRecElimRule` is structurally identical to `natElimRule` (same `[1, 0, 2, 0]` arg
shifts, same dependent obligation list, shared `natElimDependentSuccBranchType`), so the surviving-row body is
the natElim body verbatim with the `gen_natRec` row as survivor.  The exact premise set the unconditional
natRec-succ subject reduction needs.  No grown disjunct (`natRecCellHasNoTyping`). -/
theorem HasTypeUnion.invertAtNatRecHeadAllPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = natRecCell motive zeroBranch stepBranch scrutinee) :
    ∃ (resultLevel : FX1Poly.Universe.LevelExpr)
      (resultFlag : FX1Poly.Universe.UniverseFlag),
      HasTypeUnion profile context scrutinee natTypeCell ∧
      HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
      HasTypeUnion profile ((context.cons natTypeCell).cons motive)
        stepBranch (natElimDependentSuccBranchType motive) ∧
      HasTypeUnion profile (context.cons natTypeCell) motive
        (universeCodeCell resultLevel resultFlag) ∧
      Conv (RawTerm.subst0 motive scrutinee) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨resultLevel, resultFlag, scrutineeTyped, zeroBranchTyped, stepBranchTyped,
        motiveFormed, innerConv⟩ := innerInversion subjectShape
      exact ⟨resultLevel, resultFlag, scrutineeTyped, zeroBranchTyped, stepBranchTyped,
        motiveFormed, innerConv.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.natRecCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- app
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathApp
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ natRec — the SURVIVOR.  Read all four DEPENDENT obligations; the output `subst0 motive
      -- scrutinee` IS the classifier here, so the conversion leg is `Conv.refl`.
      · match args with
        | .childCons _armMotive (.childCons _armBase (.childCons _armStep (.childCons _armScrut .childNil))) =>
          rcases subjectShape with ⟨⟩
          exact ⟨level0, flag,
            premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)),
            premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
            premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
            Conv.refl _⟩
      -- boolElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- idJ
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- fst
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- snd
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

/-! ## (1) Inversion at the listElim head -/

/-- **★ Inversion at the listElim head.**  A union typing of a `listElimCell`-headed subject is EXACTLY a
listElim typing at the `gen_listElim` row of `elimRuleOf`: the scrutinee is UNION-typed at `List(elementType)`
(the NATIVE-42 union-recursive premise), the nil branch is UNION-typed at the classifier, the cons branch is
UNION-typed at the 3-arg curried step type.  THE TYTAB-1 RESHAPE: the nil/cons branch premises were GROWN
(`HasTypeDescPi`) before the elim collapse; the unified `listElimRule.obligations` makes every branch a union
obligation, so they surface UNION-typed here.  No grown disjunct: `listElimCell` is untypable in the grown
engine. -/
theorem HasTypeUnion.invertAtListElimHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = listElimCell motive scrutinee nilBranch consBranch) :
    ∃ elementType : RawTerm scope,
      HasTypeUnion profile context scrutinee (listTypeCell elementType) ∧
      HasTypeUnion profile context nilBranch (RawTerm.subst0 motive listNilCell) ∧
      HasTypeUnion profile context consBranch
        (listElimDependentConsBranchType motive elementType) ∧
      Conv (RawTerm.subst0 motive scrutinee) classifier ∧
      (∃ (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
        HasTypeUnion profile (context.cons (listTypeCell elementType)) motive
          (universeCodeCell resultLevel resultFlag)) := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨elementType, scrutineeTyped, nilTyped, consTyped, convInner,
        motiveFormed⟩ := innerInversion subjectShape
      exact ⟨elementType, scrutineeTyped, nilTyped, consTyped,
        convInner.trans converts, motiveFormed⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.listElimCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      ihPremises =>
      -- The unified introducer arm: no introducer row produces a `listElim`-headed cell (listElim is an
      -- eliminator), so every introducer row's generator clashes with `gen_listElim`.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: pin BOTH the generator and the row.  Only the `gen_listElim` row
      -- survives (its member cell IS the listElim cell); the other ten eliminator heads clash with the
      -- `listElim` subject head.
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- app
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathApp
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natRec
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherMatch
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- idJ
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- fst
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- snd
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ listElim — the SURVIVOR.  Destructure the children + params, recover the children from
      -- `subjectShape`, and surface the scrutinee + nil + cons premises from `premisesHold`.  The
      -- pinned classifier is the row's `resultType` param; `outputType` reads it, so the actual
      -- classifier IS the pinned one (`Conv.refl`).
      · match args, params with
        | .childCons _armMotive (.childCons _armScrut (.childCons _armNil (.childCons _armCons .childNil))),
          .childCons typeParamElement (.childCons _resultType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨typeParamElement, premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)),
            premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
            Conv.refl _,
            level0, flag,
            premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩

end FX1Poly.Typed
