import FX1Poly.Typed.Engine.Union.HasTypeUnionPathProjInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionReflHeadInversion
    — inversion at the `refl` head (JMAX-1, the genuine-idJ Conv-endpoint supplier)

The `invertAtOptionSomeHead` twin for the identity-type constructor `gen_refl`.  A union typing of a
`reflCell`-headed subject IS a unary data introduction at the `gen_refl` row (`reflIntroRule`): for some
carrier type `A`, the witness is union-typed at `A` and the classifier is convertible to the REFLEXIVE
identity code `Id A witness witness` (`idTypeCell A w w`).  No grown disjunct: `reflCell` is native-only
(the grown engine has no `refl` introducer), so `ofGrown` is refuted by the generic root-exclusion
`cellHasNoTypingWhenRootGenericallyExcluded` (inline, the same one-liner the `*CellHasNoTyping` family uses).

This is the TYPING-level supplier the genuine Paulin-Mohring `idJ` subject reduction (JMAX-3) needs: when the
iota fires on `witness = refl w` at a witness ascribed `Id A left right`, composing this inversion's
`Conv (idTypeCell A w w) (Id A left right)` with `Conv.idCode_inj` yields `Conv w left` and `Conv w right` —
exactly the two legs `idJReflMotiveConv` (JMAX-2) consumes.  (The based reducibility candidate supplies the
same conversions at the reducibility level; this is its typing-level analogue, which the live union SR uses.)

## Zero-axiom
A single `HasTypeUnion` induction (`var` / `universeFormation` head-absurd, `conv` Conv-trans, `ofGrown`
generic-exclusion, `formationRule` / `elim` table-absurd, `intro` 17-way `introRuleOf_cases` with `refl` the
sole survivor).  Mirrors `invertAtOptionSomeHead` exactly.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ Inversion at the `refl` head (JMAX-1).**  A union typing of a `reflCell`-headed subject is a unary
introduction at `reflIntroRule`: for some carrier `A`, the witness is union-typed at `A` and the classifier is
`Conv`-equal to `Id A witness witness`. -/
theorem HasTypeUnion.invertAtReflHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {witnessValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = reflCell witnessValue) :
    ∃ carrierType : RawTerm scope,
      HasTypeUnion profile context witnessValue carrierType ∧
      Conv (idTypeCell carrierType witnessValue witnessValue) classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨carrierType, witnessTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨carrierType, witnessTyped, convInner.trans converts⟩
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
      -- pair
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ refl — the SURVIVOR.  args = `[witness]`, params = `[carrier]`; recover the witness from
      -- `subjectShape`, surface its premise; the output type IS `Id carrier w w`, so the Conv is `refl`.
      · match args, params with
        | .childCons _witnessArg .childNil, .childCons _carrierParam .childNil =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, (premisesHold _ (List.Mem.head _)).toUnion, Conv.refl _⟩
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_refl :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

end FX1Poly.Typed
