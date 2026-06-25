import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Cell.IdJDependentMotiveType
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility

/-! # FX1Poly/Typed/HasTypeUnionPathProjInversion — NATIVE-37 part d: per-head inversions for the
    path-induction head (idJ) and the projection heads (fst / snd).

Two more eliminator shapes from the inversion substrate of `HasTypeUnionInversion`:

  * **idJ** — the survivor is the unified `elim` arm pinned to the `gen_idJ` row (the TYTAB-1 elim-collapse
    arm).  Surfaced premises: the witness union-typed at a reflexive identity code
    `Id(typeCode, endpoint, endpoint)`, the base case union-typed at the result classifier.
  * **fst / snd** — the survivor is the unified `elim` arm pinned to the `gen_fst` / `gen_snd` row.
    Surfaced premise: the pair term union-typed at `product(firstType, secondType)`; the classifier is
    forced to the selected component (`firstType` for fst, `secondType` for snd).

Both follow the established free-subject `induction` recipe with the three killer classes; the `idJCell`,
`fstCell`, `sndCell` heads are all untypable in the grown engine (host-head-untyped lemmas shipped), so
none carries an ofGrown disjunct.

## Zero-axiom

Free-subject `induction` + the shipped eleven-row inverter `elimRuleOf_cases` + the member-cell
head-projection `elimMemberCellRootGenerator` + head no-confusion + `rcases subjectShape with ⟨⟩`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (1) Inversion at the idJ head -/

/-- **★ Inversion at the idJ head (GENUINE Paulin-Mohring).**  A union typing of an `idJCell`-headed subject
is EXACTLY a path-induction typing at the genuine `gen_idJ` row: for some carrier `A` and TWO endpoints
`left`, `right`, the witness is union-typed at the GENERAL identity code `Id(A, left, right)`, the base case
is union-typed at the diagonal motive instantiation `idJMotiveAt motive left (refl left) = C[left, refl left]`,
and the genuine dependent output `idJMotiveAt motive right witness = C[right, witness]` is `Conv`-equal to the
ambient classifier.  (The two-binder motive is stored, not premised; the right-endpoint typing premise is
likewise stored.)  Conv-modulo (like `invertAtFstHead`): the conv chain is surfaced, not applied — the
genuine-J iota SR consumer composes it with the JMAX-2 motive-instantiation transport.  No grown disjunct:
`idJCell` is untypable in the grown engine. -/
theorem HasTypeUnion.invertAtIdJHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = idJCell motive baseCase witness) :
    ∃ typeCode leftEndpoint rightEndpoint : RawTerm scope,
      HasTypeUnion profile context witness (idTypeCell typeCode leftEndpoint rightEndpoint) ∧
      HasTypeUnion profile context baseCase
        (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)) ∧
      Conv (idJMotiveAt motive rightEndpoint witness) classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨typeCode, leftEndpoint, rightEndpoint, witnessTyped, baseCaseTyped, convOutput⟩ :=
        innerInversion subjectShape
      exact ⟨typeCode, leftEndpoint, rightEndpoint, witnessTyped, baseCaseTyped,
        convOutput.trans converts⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: no introducer row produces an `idJ`-headed cell (idJ is an
      -- eliminator), so every introducer row's generator clashes with `gen_idJ`.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: only the `gen_idJ` row survives (its member cell IS the idJ cell);
      -- the other ten eliminator heads clash with the `idJ` subject head.
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
      -- ★ idJ — the SURVIVOR.  Destructure the children + params, recover the children from
      -- `subjectShape`, and surface the witness premise (obligation 1) + base-case premise (obligation 3,
      -- at the diagonal motive instantiation); the output Conv is `refl` (the elim's output IS the genuine
      -- dependent output `idJMotiveAt motive right witness`).
      · match args, params with
        | .childCons _armMotive (.childCons _armBase (.childCons _armWitness .childNil)),
          .childCons _armTypeCode (.childCons _armLeft (.childCons _armRight .childNil)) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, _, (premisesHold _ (List.Mem.head _)).toUnion,
            (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).toUnion,
            Conv.refl _⟩
      -- fst
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- snd
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

/-- **★ Inversion at the idJ head, ALL FOUR premises (incl. the right-endpoint typing + the 2-extended-context
motive).**  The `invertAtIdJHead` companion that ADDITIONALLY surfaces the right-endpoint typing obligation
(`rightEndpoint : typeCode`) and the motive obligation (the two-binder motive union-typed at a universe over the
2-extended context `(context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint)`, existential
in `level`/`flag`).  These are exactly the two premises the plain inversion drops but that rebuilding an `idJ`
cell — when one of its children steps — requires (the eliminator-congruence subject reduction, gate 2 of #1697:
the rebuilt cell's `elim` arm needs all four obligations).  Same recipe: induct the union derivation at a free
subject, refute every arm except the `gen_idJ` elim survivor, which surfaces all four obligations from
`premisesHold` (order `[witness, rightEndpoint, baseCase, motive]`); the `conv` arm threads them through and
composes its conversion onto the output leg. -/
theorem HasTypeUnion.invertAtIdJHeadAllPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = idJCell motive baseCase witness) :
    ∃ typeCode leftEndpoint rightEndpoint : RawTerm scope,
      HasTypeUnion profile context witness (idTypeCell typeCode leftEndpoint rightEndpoint) ∧
      HasTypeUnion profile context rightEndpoint typeCode ∧
      HasTypeUnion profile context baseCase
        (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)) ∧
      (∃ (motiveLevel : LevelExpr) (motiveFlag : UniverseFlag),
        HasTypeUnion profile
          ((context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint)) motive
          (universeCodeCell motiveLevel motiveFlag)) ∧
      Conv (idJMotiveAt motive rightEndpoint witness) classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨typeCode, leftEndpoint, rightEndpoint, witnessTyped, rightTyped, baseCaseTyped,
        motiveFormed, convOutput⟩ := innerInversion subjectShape
      exact ⟨typeCode, leftEndpoint, rightEndpoint, witnessTyped, rightTyped, baseCaseTyped,
        motiveFormed, convOutput.trans converts⟩
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
      -- ★ idJ — the SURVIVOR (obligation order witness / rightEndpoint / baseCase / motive).
      · match args, params with
        | .childCons _armMotive (.childCons _armBase (.childCons _armWitness .childNil)),
          .childCons _armTypeCode (.childCons _armLeft (.childCons _armRight .childNil)) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, _, (premisesHold _ (List.Mem.head _)).toUnion,
            (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion,
            (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).toUnion,
            ⟨level0, flag, (premisesHold _ (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.head _))))).toUnion⟩,
            Conv.refl _⟩
      -- fst
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- snd
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

/-! ## (1) Inversion at the fst head -/

/-- **★ Inversion at the fst head.**  A union typing of an `fstCell`-headed subject is EXACTLY a
projection typing at the `gen_fst` row: for some second-component type `B`, the pair term is union-typed
at `product(C, B)` where `C` is the classifier, and the projected type is the first component (the
classifier).  No grown disjunct: `fstCell` is untypable in the grown engine. -/
theorem HasTypeUnion.invertAtFstHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {pairTerm : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = fstCell pairTerm) :
    ∃ secondType pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context pairTerm
        (productTypeCell pinnedClassifier secondType) ∧
      Conv pinnedClassifier classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨secondType, pinnedClassifier, pairTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨secondType, pinnedClassifier, pairTyped, convInner.trans converts⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: no introducer row produces an `fst`-headed cell (fst is an
      -- eliminator), so every introducer row's generator clashes with `gen_fst`.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: only the `gen_fst` row survives (its member cell IS the fst cell);
      -- the other ten eliminator heads clash with the `fst` subject head.
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
      -- ★ fst — the SURVIVOR.  Destructure the child + params, recover the pair term from
      -- `subjectShape`, and surface the pair premise (typed at `product(firstType, secondType)`) from
      -- `premisesHold`; the projected first component IS the classifier (`outputType = firstType`).
      · match args, params with
        | .childCons _armPairTerm .childNil,
          .childCons _firstType (.childCons _secondType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, (premisesHold _ (List.Mem.head _)).toUnion, Conv.refl _⟩
      -- snd
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

/-! ## (1) Inversion at the snd head -/

/-- **★ Inversion at the snd head.**  A union typing of an `sndCell`-headed subject is EXACTLY a
projection typing at the `gen_snd` row: for some first-component type `A`, the pair term is union-typed
at `product(A, C)` where `C` is the classifier, and the projected type is the second component (the
classifier).  No grown disjunct: `sndCell` is untypable in the grown engine. -/
theorem HasTypeUnion.invertAtSndHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {pairTerm : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = sndCell pairTerm) :
    ∃ firstType pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context pairTerm
        (productTypeCell firstType pinnedClassifier) ∧
      Conv pinnedClassifier classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨firstType, pinnedClassifier, pairTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨firstType, pinnedClassifier, pairTyped, convInner.trans converts⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: no introducer row produces an `snd`-headed cell (snd is an
      -- eliminator), so every introducer row's generator clashes with `gen_snd`.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: only the `gen_snd` row survives (its member cell IS the snd cell);
      -- the other ten eliminator heads clash with the `snd` subject head.
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
      -- ★ snd — the SURVIVOR.  Destructure the child + params, recover the pair term from
      -- `subjectShape`, and surface the pair premise (typed at `product(firstType, secondType)`) from
      -- `premisesHold`; the projected second component IS the classifier (`outputType = secondType`).
      · match args, params with
        | .childCons _armPairTerm .childNil,
          .childCons _firstType (.childCons _secondType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, (premisesHold _ (List.Mem.head _)).toUnion, Conv.refl _⟩
      -- listElim
      · exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

end FX1Poly.Typed
