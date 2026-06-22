import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion

/-! # FX1Poly/Typed/HasTypeUnionMatchInversion — NATIVE-37 part d: per-head inversions for the
    two-branch-match eliminator heads (boolElim / optionMatch / eitherMatch) + their REVERSE ADEQUACY.

This file extends the inversion substrate established in `HasTypeUnionInversion` (four heads:
pathLam / lam / natElim / natSucc) to the three two-branch-match data-eliminator heads.  All three are
survivors of the SAME unified union arm — `elim` (the TYTAB-1 elim-collapse arm that subsumes the six
former eliminator arms) — pinned to their respective rows by the shipped `elimRuleOf_cases` eleven-row
inverter.

## The per-head inversion (the established recipe, replicated against the unified elim arm)

Each inversion takes a FREE subject + a `subjectShape : subject = <head-cell>` hypothesis, then
`induction`s the union derivation (safe at a free index — never at the concrete cell index).  In the
unified `elim` arm, `elimRuleOf_cases` splits into the eleven eliminator rows; exactly ONE row survives
— the row whose `memberCell` head IS this inversion's head — and surfaces the three RECURSIVE union
premises (scrutinee + both branches) by feeding `List.Mem` witnesses (`.head` / `.tail .head` /
`.tail .tail .head`) into the arm's `premisesHold` obligation discharger.  Each of the other ten rows
dies by `elimMemberCellRootGenerator` head-clash: its member-cell root generator is the row's generator,
which clashes with this head.  Every non-`elim` arm dies by one of the prior killer classes (table-none
`rfl`, `subjectIs…` head-clash, spec/row head-clash).

The row's params supply the existential type indices (`optionMatch` / `eitherMatch`'s element types) and
the result type, which the `induction` motive equates to the ambient classifier — so `Conv.refl`
discharges each reverse-adequacy reclassification leg.

## ★ Reverse adequacy (closes the boolElim / optionMatch / eitherMatch share of fold 29)

For each family, a theorem of the form: a union typing of a `<head>`-headed subject yields the surfaced
RECURSIVE union premises (the honest surplus — the union types MORE, e.g. an eliminator whose scrutinee
is a computed value), AND when those surfaced premises happen to land in the bespoke engines (scrutinee
in the data-intro engine, branches in the grown engine) the bespoke `HasTypeDesc<Family>` derivation is
RECONSTRUCTED.  The honest-surplus disjunct is precisely the gap between the union-recursive scrutinee /
branch premises and the bespoke engine-specific premises: the union admits a scrutinee typed by ANY
native family, whereas the bespoke engine demands the inlined nullary data-intro row (`dataIntroNullary`) /
`HasTypeDescOptionIntro` / `HasTypeDescEitherIntro` and grown branches.  The reverse adequacy is therefore stated in the
RELATIVIZED form: the union derivation yields the bespoke derivation GIVEN that the surfaced premises are
bespoke-shaped (the reconstruction hypotheses); without them the surfaced union premises are the surplus.

## Zero-axiom

Free-subject `induction` + the shipped eleven-row inverter `elimRuleOf_cases` + the member-cell
head-projection `elimMemberCellRootGenerator` + head-generator no-confusion + `rcases subjectShape with
⟨⟩` child drilling + `premisesHold` discharge via `List.Mem.head` / `.tail` witnesses.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditUnionMatchInversion.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (1) Inversion at the boolElim head -/

/-- **★ Inversion at the boolElim head (DEPENDENT).**  A union typing of a `boolElimCell`-headed subject is
EXACTLY a dependent two-branch-match typing at the `gen_boolElim` row: the scrutinee is union-typed at
`Bool`, the then-branch at `subst0 motive boolTrueCell`, the else-branch at `subst0 motive boolFalseCell`
(the motive at the boolean VALUES), and the eliminator's natural output `subst0 motive scrutinee` is
convertible to the ambient classifier.  The branch typings are classifier-INDEPENDENT (so the `conv` arm
passes them through and only composes the output-conversion leg); the conversion leg is what the iota
subject-reduction uses to retype the reduct.  No grown disjunct: `boolElimCell` is untypable in the grown
engine (a recursive eliminator in no host root). -/
theorem HasTypeUnion.invertAtBoolElimHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = boolElimCell motive scrutinee thenBranch elseBranch) :
    HasTypeUnion profile context scrutinee boolTypeCell ∧
    HasTypeUnion profile context thenBranch (RawTerm.subst0 motive boolTrueCell) ∧
    HasTypeUnion profile context elseBranch (RawTerm.subst0 motive boolFalseCell) ∧
    Conv (RawTerm.subst0 motive scrutinee) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      -- The branch typings (at the motive at the boolean VALUES) are classifier-INDEPENDENT, so they pass
      -- through unchanged; only the output-vs-ambient conversion leg composes with this node's `converts`.
      obtain ⟨scrutineeTyped, thenBranchTyped, elseBranchTyped, outputConv⟩ := innerInversion subjectShape
      exact ⟨scrutineeTyped, thenBranchTyped, elseBranchTyped, outputConv.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.boolElimCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: no introducer row produces a `boolElim`-headed cell (boolElim is an
      -- eliminator), so every introducer row's generator clashes with `gen_boolElim`.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: pin BOTH the generator and the row.  Only the `gen_boolElim` row
      -- survives (its member cell IS the boolElim cell); the other ten eliminator heads clash with the
      -- `boolElim` subject head.
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
      -- ★ boolElim — the SURVIVOR.  Destructure the children, recover them from `subjectShape`, and
      -- surface the scrutinee + both-branch premises from `premisesHold` (obligation order:
      -- scrutinee@Bool, thenBranch@result, elseBranch@result).
      · match args, params with
        | .childCons _armMotive (.childCons _armScrut (.childCons _armThen (.childCons _armElse .childNil))),
          .childNil =>
          rcases subjectShape with ⟨⟩
          exact ⟨premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)),
            premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
            Conv.refl _⟩
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

/-! ## (1) Inversion at the optionMatch head -/

/-- **★ Inversion at the optionMatch head.**  A union typing of an `optionMatchCell`-headed subject is
EXACTLY a two-branch-match typing at the `gen_optionMatch` row: for some element type `A`, the scrutinee
is union-typed at `option(A)`, the None branch is union-typed at the result classifier, and the Some
branch is union-typed at the non-dependent handler `A → C`.  No grown disjunct (`optionMatchCell` is a
recursive eliminator, untypable in the grown engine). -/
theorem HasTypeUnion.invertAtOptionMatchHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = optionMatchCell motive noneBranch someBranch scrutinee) :
    ∃ (elementType pinnedClassifier : RawTerm scope),
      HasTypeUnion profile context scrutinee (optionTypeCell elementType) ∧
      HasTypeUnion profile context noneBranch pinnedClassifier ∧
      HasTypeUnion profile context someBranch
        (piTyCodeCell elementType (RawTerm.weaken pinnedClassifier)) ∧
      Conv pinnedClassifier classifier ∧
      (∃ (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
        HasTypeUnion profile context pinnedClassifier
          (universeCodeCell resultLevel resultFlag)) := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨elementType, pinnedClassifier, scrutineeTyped, noneTyped, someTyped, convInner,
        pinnedFormed⟩ := innerInversion subjectShape
      exact ⟨elementType, pinnedClassifier, scrutineeTyped, noneTyped, someTyped,
        convInner.trans converts, pinnedFormed⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.optionMatchCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: no introducer row produces an `optionMatch`-headed cell (optionMatch
      -- is an eliminator), so every introducer row's generator clashes with `gen_optionMatch`.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: pin BOTH the generator and the row.  Only the `gen_optionMatch` row
      -- survives (its member cell IS the optionMatch cell); the other ten eliminator heads clash with the
      -- `optionMatch` subject head.
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
      -- ★ optionMatch — the SURVIVOR.  Destructure the children, recover them from `subjectShape`, and
      -- surface the scrutinee + None-branch + Some-branch premises from `premisesHold` (obligation order:
      -- scrutinee@option(A), noneBranch@result, someBranch@(A → result)).  The element type is the
      -- row's first param; the pinned classifier is the result type (which the motive equates to the
      -- ambient classifier, so `Conv.refl` discharges the reclassification leg).
      · match args, params with
        | .childCons _armMotive (.childCons _armNone (.childCons _armSome (.childCons _armScrut .childNil))),
          .childCons typeParamA (.childCons _typeParamB (.childCons _resultType .childNil)) =>
          rcases subjectShape with ⟨⟩
          exact ⟨typeParamA, _, premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)),
            premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
            Conv.refl _,
            level0, flag,
            premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩
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

/-! ## (1) Inversion at the eitherMatch head -/

/-- **★ Inversion at the eitherMatch head.**  A union typing of an `eitherMatchCell`-headed subject is
EXACTLY a two-branch-match typing at the `gen_eitherMatch` row: for some left/right types `A`, `B`, the
scrutinee is union-typed at `either(A, B)`, the left branch is union-typed at the handler `A → C`, and
the right branch is union-typed at `B → C`.  No grown disjunct (`eitherMatchCell` is a recursive
eliminator, untypable in the grown engine). -/
theorem HasTypeUnion.invertAtEitherMatchHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = eitherMatchCell motive leftBranch rightBranch scrutinee) :
    ∃ (leftType rightType pinnedClassifier : RawTerm scope),
      HasTypeUnion profile context scrutinee (eitherTypeCell leftType rightType) ∧
      HasTypeUnion profile context leftBranch
        (piTyCodeCell leftType (RawTerm.weaken pinnedClassifier)) ∧
      HasTypeUnion profile context rightBranch
        (piTyCodeCell rightType (RawTerm.weaken pinnedClassifier)) ∧
      Conv pinnedClassifier classifier ∧
      (∃ (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
        HasTypeUnion profile context pinnedClassifier
          (universeCodeCell resultLevel resultFlag)) := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨leftType, rightType, pinnedClassifier, scrutineeTyped, leftTyped, rightTyped,
        convInner, pinnedFormed⟩ := innerInversion subjectShape
      exact ⟨leftType, rightType, pinnedClassifier, scrutineeTyped, leftTyped, rightTyped,
        convInner.trans converts, pinnedFormed⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.eitherMatchCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: no introducer row produces an `eitherMatch`-headed cell (eitherMatch
      -- is an eliminator), so every introducer row's generator clashes with `gen_eitherMatch`.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: pin BOTH the generator and the row.  Only the `gen_eitherMatch` row
      -- survives (its member cell IS the eitherMatch cell); the other ten eliminator heads clash with the
      -- `eitherMatch` subject head.
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
      -- ★ eitherMatch — the SURVIVOR.  Destructure the children, recover them from `subjectShape`, and
      -- surface the scrutinee + left-branch + right-branch premises from `premisesHold` (obligation
      -- order: scrutinee@either(A, B), leftBranch@(A → result), rightBranch@(B → result)).  The left and
      -- right types are the row's first two params; the pinned classifier is the result type (which the
      -- motive equates to the ambient classifier, so `Conv.refl` discharges the reclassification leg).
      · match args, params with
        | .childCons _armMotive (.childCons _armLeft (.childCons _armRight (.childCons _armScrut .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons _resultType .childNil)) =>
          rcases subjectShape with ⟨⟩
          exact ⟨typeParamA, typeParamB, _, premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)),
            premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
            Conv.refl _,
            level0, flag,
            premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩
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

end FX1Poly.Typed
