import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnly
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable

/-! # HasTypeUnionNativeOnlyHeadInversion — value-head inversion for the OFGROWN-FREE union (TYTAB-2 RETIRE)

The native-only (`ofGrown`-free) value-introducer head-inversion masters: a `HasTypeUnionNativeOnly` typing
of a `pairCell` / `optionSomeCell` / `eitherInlCell` / `eitherInrCell` / `listConsCell`-headed subject IS the
corresponding data introduction at the matching `gen_*` row.  These are the DIRECT inductions over the 6-arm
`ofGrown`-free judgment (`var` / `universeFormation` / `formationRule` / `intro` / `elim` / `conv`) — there is
no `ofGrown` arm to refute, so the proof is the kernel inversion MINUS the host-refutation case.  The
`introRuleOf_cases` 17-row split isolates the single surviving introducer row; every other introducer / the
former arm / the eliminator arm clashes on the subject head; the `conv` arm recurses through its IH.

These are the canonical home of the value-head inversions in the `ofGrown`-free world: the kernel masters
`HasTypeUnion.invertAt*Head` DELEGATE here by reflecting their subject through `HasTypeUnion.toNativeOnly`
(then re-embedding the components with `HasTypeUnionNativeOnly.toUnion`), which retires their `ofGrown` match
arms.  So the `induction over HasTypeUnion` (with its `ofGrown` case) is replaced everywhere by an `induction
over HasTypeUnionNativeOnly` (no such case) — one of the per-master flips that shrink the `ofGrown`
match-arm surface ahead of physically deleting the arm (#1698).

## Zero-axiom

`induction` over the native-only judgment + the head-no-confusion refutations (`congrArg
RawTerm.rootGenerator` + `cases`) + the introducer-row table dispatch (`introRuleOf_cases` /
`introMemberCellRootGenerator` / `elimMemberCellRootGenerator`) + `Conv.refl` / `Conv.trans`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ Native-only pair-head inversion (direct).**  A `HasTypeUnionNativeOnly`-typed `pairCell` is a product
of native-only-typed components, the product type `Conv`-equal to the classifier. -/
theorem HasTypeUnionNativeOnly.invertAtPairHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = pairCell firstValue secondValue) :
    ∃ firstType secondType : RawTerm scope,
      HasTypeUnionNativeOnly profile context firstValue firstType ∧
      HasTypeUnionNativeOnly profile context secondValue secondType ∧
      Conv (productTypeCell firstType secondType) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨firstType, secondType, firstTyped, secondTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨firstType, secondType, firstTyped, secondTyped, convInner.trans converts⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- boolTrue
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolFalse
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- unit
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval0
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval1
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natZero
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- lam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathLam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natSucc
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listCons
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionSome
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionNone
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listNil
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherInl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherInr
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ pair — the SURVIVOR.  Destructure args (`[0, 0]`) + params (`[0, 0]`); the output type IS
      -- `product(A, B)`, so the Conv is `refl`.
      · match args, params with
        | .childCons _armFirst (.childCons _armSecond .childNil),
          .childCons _firstType (.childCons _secondType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)), Conv.refl _⟩
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_pair :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-- **★ Native-only optionSome-head inversion (direct).**  A `HasTypeUnionNativeOnly`-typed `optionSomeCell`
is a unary `gen_optionSome` introduction: the payload is native-only-typed at some `A`, the classifier
`Conv`-equal to `option(A)`. -/
theorem HasTypeUnionNativeOnly.invertAtOptionSomeHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = optionSomeCell payloadValue) :
    ∃ payloadType : RawTerm scope,
      HasTypeUnionNativeOnly profile context payloadValue payloadType ∧
      Conv (optionTypeCell payloadType) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨payloadType, payloadTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨payloadType, payloadTyped, convInner.trans converts⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- boolTrue
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolFalse
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- unit
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval0
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval1
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natZero
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- lam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathLam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natSucc
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listCons
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ optionSome — the SURVIVOR.  Destructure args (`[0]`) + params (`[0]`); the output type IS
      -- `option(A)`, so the Conv is `refl`.
      · match args, params with
        | .childCons _armValue .childNil, .childCons _payloadType .childNil =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, premisesHold _ (List.Mem.head _), Conv.refl _⟩
      -- optionNone
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listNil
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherInl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherInr
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pair
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_optionSome :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-- **★ Native-only eitherInl-head inversion (direct).**  A `HasTypeUnionNativeOnly`-typed `eitherInlCell` is
a left `gen_eitherInl` introduction: the payload is native-only-typed at the LEFT type `A`, the classifier
`Conv`-equal to `either(A, B)`. -/
theorem HasTypeUnionNativeOnly.invertAtEitherInlHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = eitherInlCell payloadValue) :
    ∃ leftType rightType : RawTerm scope,
      HasTypeUnionNativeOnly profile context payloadValue leftType ∧
      Conv (eitherTypeCell leftType rightType) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨leftType, rightType, payloadTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨leftType, rightType, payloadTyped, convInner.trans converts⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- boolTrue
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolFalse
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- unit
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval0
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval1
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natZero
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- lam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathLam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natSucc
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listCons
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionSome
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionNone
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listNil
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ eitherInl — the SURVIVOR.  Destructure args (`[0]`) + params (`[0, 0]`); the output type IS
      -- `either(A, B)` (left first), so the Conv is `refl`.
      · match args, params with
        | .childCons _armValue .childNil,
          .childCons _leftType (.childCons _rightType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, premisesHold _ (List.Mem.head _), Conv.refl _⟩
      -- eitherInr
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pair
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_eitherInl :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-- **★ Native-only eitherInr-head inversion (direct).**  A `HasTypeUnionNativeOnly`-typed `eitherInrCell` is
a right `gen_eitherInr` introduction: the payload is native-only-typed at the RIGHT type `B`, the classifier
`Conv`-equal to `either(A, B)` (free LEFT type first, value's RIGHT type second). -/
theorem HasTypeUnionNativeOnly.invertAtEitherInrHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = eitherInrCell payloadValue) :
    ∃ leftType rightType : RawTerm scope,
      HasTypeUnionNativeOnly profile context payloadValue rightType ∧
      Conv (eitherTypeCell leftType rightType) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨leftType, rightType, payloadTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨leftType, rightType, payloadTyped, convInner.trans converts⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- boolTrue
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolFalse
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- unit
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval0
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval1
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natZero
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- lam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathLam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natSucc
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listCons
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionSome
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionNone
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listNil
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherInl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ eitherInr — the SURVIVOR.  Destructure args (`[0]`) + params (`[0, 0]`); the output type IS
      -- `either(typeParam1, typeParam0)` (free LEFT first, value's RIGHT second), so the Conv is `refl`.
      · match args, params with
        | .childCons _armValue .childNil,
          .childCons _rightType (.childCons _leftType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, premisesHold _ (List.Mem.head _), Conv.refl _⟩
      -- pair
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_eitherInr :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-- **★ Native-only listCons-head inversion (direct).**  A `HasTypeUnionNativeOnly`-typed `listConsCell` is a
binary recursive `gen_listCons` introduction: the head is native-only-typed at some `A`, the tail at
`List(A)`, the classifier `Conv`-equal to `List(A)`. -/
theorem HasTypeUnionNativeOnly.invertAtListConsHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {headValue tailList : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = listConsCell headValue tailList) :
    ∃ elementType : RawTerm scope,
      HasTypeUnionNativeOnly profile context headValue elementType ∧
      HasTypeUnionNativeOnly profile context tailList (listTypeCell elementType) ∧
      Conv (listTypeCell elementType) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨elementType, headTyped, tailTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨elementType, headTyped, tailTyped, convInner.trans converts⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- boolTrue
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolFalse
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- unit
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval0
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval1
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natZero
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- lam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathLam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natSucc
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ listCons — the SURVIVOR.  Destructure args (`[0, 0]`) + params (`[0]`); the output type IS
      -- `List(A)`, so the Conv is `refl`.
      · match args, params with
        | .childCons _armHead (.childCons _armTail .childNil), .childCons _elementType .childNil =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)), Conv.refl _⟩
      -- optionSome
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionNone
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listNil
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherInl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherInr
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pair
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_listCons :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

end FX1Poly.Typed
