import FX1Poly.Typed.HasTypeNativeUnion
import FX1Poly.Typed.HasTypeDescPiDataHeadUntyped

/-! # FX1Poly/Typed/HasTypeNativeUnionInversion — NATIVE-37: the FIRST eliminations over the native union

This file performs the first-ever `cases`/`induction` over `HasTypeNativeUnion`.  The arm set stabilized at
twenty-four constructors (four engine embeddings + two recursive keystone arms + the Nat-intro embedding + the
recursive-eliminator arm + the five batch-2 scrutinee embeddings + the three batch-2 data-eliminator arms + the
seven batch-2 data-intro arms + the listElim arm), and a deliberate freeze prevented eliminations until the set
was final.  The freeze is lifted: free-subject `cases` over the union is propext-clean (verified in the audit
shard), so this file establishes THE inversion pattern that all later union metatheory (subject reduction,
substitution, reverse adequacy) replicates.

## THE PER-ARM DISCRIMINATION RECIPE (replicate this for the remaining heads)

To invert a union typing at a concrete head `H` (subject `= <H-headed cell>`), state the inversion with a FREE
subject, take `subjectShape : subject = <H-headed cell>` as a hypothesis, then `cases` the derivation (safe at a
FREE index — never `cases` at a concrete cell index, the equation-motive propext trap).  In each of the
twenty-four arms the threaded `subjectShape` discriminates:

  * **Engine-embedding arm whose engine cannot produce an `H`-head** — refute via that engine's own
    subject-head characterization.  Three flavours:
      - Table engines (`ofBaseType` / `ofDataIntro` / `ofTermIndexedFormer`): the embedded derivation pins
        `subject = .mkGen generator _ _` with `<table>Of generator = some rule`; `congrArg RawTerm.rootGenerator`
        forces `generator = H`, and `<table>Of H = none` (`rfl`) contradicts the membership.  Packaged as
        `baseTypeSubjectHeadExcluded` / `dataIntroSubjectHeadExcluded` / `termIndexedFormerSubjectHeadExcluded`.
      - Closed-form intro engines (`ofNatIntro` / `ofOptionIntro` / `ofEitherIntro` / `ofIdIntro` / `ofPairIntro`
        / `ofListIntro`): the shipped `subjectIs…Constructor` lemma names every head the engine can carry; a
        `congrArg RawTerm.rootGenerator` head clash refutes each disjunct against `H`.
      - The grown engine (`ofGrown`): refuted only for the pathLam head, by the new
        `HasTypeDescPi.pathLamCellHasNoTyping` (deliverable 2 below — `gen_pathLam` is in no host root and carries
        no formation rule).  For all other heads `ofGrown` is left as an honest disjunct.
  * **Table-driven arm whose member-cell head ≠ `H`** — invert the arm's row table (`<table>Of_cases` /
    `…_isLamOrPathLam` / the in-file `nativeRecursiveElimRuleOf_isNatElimOrNatRec`) to pin `rule` to a concrete
    row, making `rule.memberCell` a concrete cell, then refute via `congrArg RawTerm.rootGenerator subjectShape`
    head clash.
  * **Table-driven arm whose member-cell head = `H`** — the SURVIVING disjunct.  Pin the row, `injections` the
    threaded equation to recover the arm's children, and surface every premise (the graded check, the recursive
    body/branch premises) as existentials.

## What this file ships (deliverables, priority order)

  1. `HasTypeNativeUnion.invertAtPathLamHead` / `invertAtLamHead` / `invertAtNatElimHead` /
     `invertAtNatSuccHead` — the master per-head inversion instantiated for four representative heads.
  2. `HasTypeDescPi.pathLamCellHasNoTyping` — the host pathLam-head refutation (the lemma named in Rung 103,
     extending the `HasTypeDescPiDataHeadUntyped` pattern: `gen_pathLam` is in no host root and no formation
     table).
  3. `HasTypeNativeUnion.unionRejectsAffineDoubleUse` — ★ the union-wide affine rejection: the
     dimension-duplicating path abstraction `pathLam(pair(var 0, var 0))` is untypable in the UNION at EVERY
     classifier and EVERY context.  The ofGrown disjunct dies by (2); the gradedBinderIntro disjunct dies because
     the `.one` graded check fails on the double-use body (occurrence count `2`, the NATIVE-23 rejection
     machinery).
  4. The pattern note (this docstring).
  5. Coverage record + witness.

## Zero-axiom

The host refutation is the one-line `cellHasNoTypingWhenRootGenericallyExcluded` application; the inversions are
free-subject `cases` + table inversions + head-generator no-confusion + `injections`; the affine rejection routes
through `invertAtPathLamHead` (free-index inversion, never `cases` at the concrete subject) + the shipped
`doubleDimensionUseBody_occurrenceIsTwo` count fact.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditNativeUnionInversion.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (2) The host pathLam-head refutation (the Rung-103 missing lemma)

`gen_pathLam` is none of the four non-former host roots (`gen_var` / `gen_universeCode` / `gen_lam` / `gen_app`)
and carries no formation rule (`typingRuleDescOf gen_pathLam = none`), so the grown engine types no
pathLam-headed subject — the exact extension-by-addition of the `HasTypeDescPiDataHeadUntyped` corpus to the
bridge-abstraction head. -/

/-- **`pathLam`-headed cells are untyped in the grown engine.**  `gen_pathLam` is in no host root and no
formation table, so `cellHasNoTypingWhenRootGenericallyExcluded` fires — the host pathLam-head refutation the
union-wide affine rejection consumes (the ofGrown disjunct of `invertAtPathLamHead`). -/
theorem HasTypeDescPi.pathLamCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (pathLamCell body) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;>
    (first | (intro contra; cases contra) | rfl)

/-- **`natSucc`-headed cells are untyped in the grown engine.**  `gen_natSucc` is a data constructor (in no
host root, `typingRuleDescOf gen_natSucc = none`), so the grown engine types no `natSucc`-headed subject — the
companion of the shipped `HasTypeDescPi.natElimCellHasNoTyping` for the data-INTRO head, closing the ofGrown
disjunct of `invertAtNatSuccHead`. -/
theorem HasTypeDescPi.natSuccCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {child classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (natSuccCell child) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;>
    (first | (intro contra; cases contra) | rfl)

/-! ## Engine-embedding subject-head exclusions (the table-engine and closed-form-engine refutations)

For each engine embedding that cannot carry the target head, a small subject-head exclusion lemma states: if the
embedded engine types a subject whose head is excluded from its table (or differs from every closed-form head),
the subject is not that excluded head.  Each is a single free-index `cases` over the embedded engine. -/

/-- The base-type engine types no subject whose head is excluded from its formation table.  The threaded
`subjectShape` forces the arm's tabled `generator` to the excluded head; `none = some rule` is absurd. -/
theorem baseTypeSubjectHeadExcluded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {excludedHead : Generator} {payload : excludedHead.payload scope}
    {children : RawTermChildren excludedHead.binderShifts scope}
    (notInTable : baseTypeRuleDescOf excludedHead = none)
    (typed : HasTypeDescBaseType profile context subject classifier)
    (subjectShape : subject = .mkGen excludedHead payload children) :
    False := by
  cases typed with
  | baseFormation generator armPayload armChildren rule isBaseType =>
      have headEq : generator = excludedHead :=
        congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      rw [notInTable] at isBaseType
      exact absurd isBaseType (by intro hit; cases hit)

/-- The data-intro engine types no subject whose head is excluded from its nullary-constructor table. -/
theorem dataIntroSubjectHeadExcluded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {excludedHead : Generator} {payload : excludedHead.payload scope}
    {children : RawTermChildren excludedHead.binderShifts scope}
    (notInTable : dataIntroNullaryRuleDescOf excludedHead = none)
    (typed : HasTypeDescDataIntro profile context subject classifier)
    (subjectShape : subject = .mkGen excludedHead payload children) :
    False := by
  cases typed with
  | nullaryIntro generator armPayload armChildren rule isDataIntro =>
      have headEq : generator = excludedHead :=
        congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      rw [notInTable] at isDataIntro
      exact absurd isDataIntro (by intro hit; cases hit)

/-- The term-indexed former engine types no subject whose head is excluded from its former table. -/
theorem termIndexedFormerSubjectHeadExcluded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {excludedHead : Generator} {payload : excludedHead.payload scope}
    {children : RawTermChildren excludedHead.binderShifts scope}
    (notInTable : termIndexedFormerDescOf excludedHead = none)
    (typed : HasTypeDescTermIndexedFormer profile context subject classifier)
    (subjectShape : subject = .mkGen excludedHead payload children) :
    False := by
  cases typed with
  | genFormation generator armPayload armChildren carrier level flag rule isTermIndexed premises =>
      have headEq : generator = excludedHead :=
        congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      rw [notInTable] at isTermIndexed
      exact absurd isTermIndexed (by intro hit; cases hit)

/-! ## In-file row inverter for the recursive-eliminator table

The recursive-eliminator table (`nativeRecursiveElimRuleOf`) lives in `HasTypeNativeUnion.lean` and ships only
the diagonal metadata; the `…_cases` inverter (decidable case analysis over the two-row `if`-table) is supplied
here so the `recursiveElim` arm can be pinned to its concrete row. -/

/-- A recursive-eliminator table hit pins one of the two Nat rows (`gen_natElim` / `gen_natRec`).  Decidable case
analysis over the two-row `if`-table; the `none` tail refutes any other generator. -/
theorem nativeRecursiveElimRuleOf_isNatElimOrNatRec {generator : Generator}
    {rule : NativeRecursiveElimRule}
    (tableHit : nativeRecursiveElimRuleOf generator = some rule) :
    (generator = .gen_natElim ∧ rule = natElimNativeRecursiveRule) ∨
    (generator = .gen_natRec ∧ rule = natRecNativeRecursiveRule) := by
  unfold nativeRecursiveElimRuleOf at tableHit
  by_cases isNatElim : generator = .gen_natElim
  · rw [if_pos isNatElim] at tableHit
    exact Or.inl ⟨isNatElim, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isNatElim] at tableHit
    by_cases isNatRec : generator = .gen_natRec
    · rw [if_pos isNatRec] at tableHit
      exact Or.inr ⟨isNatRec, (Option.some.inj tableHit).symm⟩
    · rw [if_neg isNatRec] at tableHit
      exact absurd tableHit (by intro hit; cases hit)

/-! ## (1) The master per-head inversion — instantiated for the pathLam head

The honest disjunction of every arm that can type a pathLam-headed cell.  Only two survive: the grown engine
(left as a disjunct, refuted separately by `pathLamCellHasNoTyping`) and the graded binder-introduction arm at the
pathLam row (premises surfaced as existentials).  Every other arm is refuted in place by its engine's subject-head
characterization or its row table's head clash. -/

/-- **★ Inversion at the pathLam head.**  A union typing of a pathLam-headed subject is EITHER a grown typing of
that subject (the ofGrown disjunct — impossible by `pathLamCellHasNoTyping`, kept honest here so the inversion
does not depend on (2)) OR a graded binder-introduction at the pathLam row: the classifier is forced to the bridge
code at the body's endpoint substitutions, the affine `.one` graded check holds on the body, and the body is
union-typed at the weakened carrier under the interval-extended context. -/
theorem HasTypeNativeUnion.invertAtPathLamHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {body : RawTerm (scope + 1)}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = pathLamCell body) :
    (∃ pinnedClassifier : RawTerm scope,
        HasTypeDescPi profile context (pathLamCell body) pinnedClassifier ∧
        Conv pinnedClassifier classifier)
    ∨ (∃ (carrierCode pinnedClassifier : RawTerm scope),
        pinnedClassifier = bridgeTypeCell carrierCode
          (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell) ∧
        gradedBinderChecks UsageGrade.one body ∧
        HasTypeNativeUnion profile (context.cons intervalTypeCell) body
          (RawTerm.weaken carrierCode) ∧
        Conv pinnedClassifier classifier) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      rcases innerInversion subjectShape with ⟨pinnedClassifier, hostInner, convInner⟩ |
        ⟨carrierCode, pinnedClassifier, bridgeEq, bodyAffine, bodyTyped, convInner⟩
      · exact Or.inl ⟨pinnedClassifier, hostInner, convInner.trans converts⟩
      · exact Or.inr ⟨carrierCode, pinnedClassifier, bridgeEq, bodyAffine, bodyTyped,
          convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact Or.inl ⟨_, hostTyped, Conv.refl _⟩
  | ofBaseType baseTyped =>
      exact absurd (baseTypeSubjectHeadExcluded rfl baseTyped subjectShape) (fun contra => contra)
  | ofDataIntro dataTyped =>
      exact absurd (dataIntroSubjectHeadExcluded rfl dataTyped subjectShape) (fun contra => contra)
  | ofTermIndexedFormer formerTyped =>
      exact absurd (termIndexedFormerSubjectHeadExcluded rfl formerTyped subjectShape)
        (fun contra => contra)
  | gradedBinderIntro ctx generator rule typeParamA typeParamB armBody domainLevel codomainLevel
      flag isIntro binderGraded domainFormed classifierFormed bodyTyped =>
      rcases gradedIntroRuleOf_isLamOrPathLam isIntro with hLam | hPath
      · subst hLam
        have ruleEq : rule = lamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathLamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
        subst ruleEq
        have bodiesEqual : armBody = body := by injections
        subst bodiesEqual
        exact Or.inr ⟨typeParamA, _, rfl, binderGraded, bodyTyped, Conv.refl _⟩
  | generalElim ctx generator rule typeParamA typeParamB typeParamC typeParamD eliminated argument
      isElim eliminatedTyped argumentTyped =>
      rcases generalElimRuleOf_isAppOrPathApp isElim with hApp | hPath
      · subst hApp
        have ruleEq : rule = appGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathAppGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_pathApp)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | ofNatIntro natTyped =>
      rcases natTyped.subjectIsNatConstructor with isZero | ⟨_, isSucc⟩
      · exact absurd (subjectShape.symm.trans isZero) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isSucc) (by intro headEq; cases headEq)
  | recursiveElim ctx generator rule motive baseBranch stepBranch scrutinee resultType
      isRecursiveElim scrutineeTyped baseBranchTyped =>
      rcases nativeRecursiveElimRuleOf_isNatElimOrNatRec isRecursiveElim with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | ofOptionIntro optionTyped =>
      rcases optionTyped.subjectIsOptionConstructor with isNone | ⟨_, isSome⟩
      · exact absurd (subjectShape.symm.trans isNone) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isSome) (by intro headEq; cases headEq)
  | ofEitherIntro eitherTyped =>
      rcases eitherTyped.subjectIsEitherInjection with ⟨_, isInl⟩ | ⟨_, isInr⟩
      · exact absurd (subjectShape.symm.trans isInl) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isInr) (by intro headEq; cases headEq)
  | ofIdIntro idTyped =>
      obtain ⟨_, isRefl⟩ := idTyped.subjectIsRefl
      exact absurd (subjectShape.symm.trans isRefl) (by intro headEq; cases headEq)
  | ofPairIntro pairTyped =>
      obtain ⟨_, _, isPair⟩ := pairTyped.subjectIsPair
      exact absurd (subjectShape.symm.trans isPair) (by intro headEq; cases headEq)
  | ofListIntro listTyped =>
      rcases listTyped.subjectIsListConstructor with isNil | ⟨_, _, isCons⟩
      · exact absurd (subjectShape.symm.trans isNil) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isCons) (by intro headEq; cases headEq)
  | twoBranchMatchElim ctx generator rule motive firstBranch secondBranch scrutinee
      typeParamA typeParamB resultType isTwoBranchMatch scrutineeTyped firstBranchTyped
      secondBranchTyped =>
      rcases nativeTwoBranchMatchRuleOf_cases isTwoBranchMatch with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pathInductionElim ctx generator rule motive baseCase witness typeCode endpoint resultType
      isPathInduction witnessTyped baseCaseTyped =>
      obtain ⟨_, ruleEq⟩ := nativePathInductionRuleOf_cases isPathInduction
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | projectionElim ctx generator rule pairTerm firstType secondType isProjection pairTyped =>
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveUnaryIntro ctx generator rule child isRecursiveUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveUnaryDataIntroRuleOf_cases isRecursiveUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveBinaryIntro ctx generator rule head tail elementType isRecursiveBinary headTyped
      tailTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveBinaryDataIntroRuleOf_cases isRecursiveBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pinnedUnaryIntro ctx generator rule child elementType isPinnedUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativePinnedUnaryDataIntroRuleOf_cases isPinnedUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nullaryFreeTypeIntro ctx generator rule elementType elementLevel flag isNullaryFreeType
      elementTypeFormed =>
      obtain ⟨_, ruleEq⟩ := nativeNullaryFreeTypeDataIntroRuleOf_cases isNullaryFreeType
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | coproductIntro ctx generator rule value pinnedType freeType freeLevel flag isCoproduct valueTyped
      freeTypeFormed =>
      rcases nativeCoproductDataIntroRuleOf_cases isCoproduct with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nonDependentBinaryIntro ctx generator rule firstChild secondChild firstType secondType
      isNonDependentBinary firstTyped secondTyped =>
      obtain ⟨_, ruleEq⟩ := nativeNonDependentBinaryDataIntroRuleOf_cases isNonDependentBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | reflexiveIntro ctx generator rule witness witnessType isReflexive witnessTyped =>
      obtain ⟨_, ruleEq⟩ := nativeReflexiveDataIntroRuleOf_cases isReflexive
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | listElim ctx generator rule motive scrutinee nilBranch consBranch elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)

/-! ## (1) The master per-head inversion — instantiated for the lam head

The lam head has TWO survivors: the grown engine (a host `piIntro`-built λ typing, kept as a disjunct) and the
graded binder-introduction arm at the λ row (premises surfaced).  The pathLam row of the graded arm dies by head
clash; every other arm dies by its engine's subject-head characterization or its row's head clash. -/

/-- **★ Inversion at the lam head.**  A union typing of a `lamCell`-headed subject is EITHER a grown typing of
that λ (the ofGrown / `piIntro` disjunct) OR a graded binder-introduction at the λ row: the classifier is a Π
code over the annotated domain and some codomain, the domain is union-formed at a universe, the codomain is
union-formed under the domain, and the body is union-typed at the codomain.  (The λ row's graded check is the
unrestricted `.omega`, vacuous, so it is not surfaced.) -/
theorem HasTypeNativeUnion.invertAtLamHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = lamCell domainAnn body) :
    (∃ pinnedClassifier : RawTerm scope,
        HasTypeDescPi profile context (lamCell domainAnn body) pinnedClassifier ∧
        Conv pinnedClassifier classifier)
    ∨ (∃ (codomainCode : RawTerm (scope + 1)) (domainLevel codomainLevel : LevelExpr)
          (flag : UniverseFlag),
        Conv (piTyCodeCell domainAnn codomainCode) classifier ∧
        HasTypeNativeUnion profile context domainAnn (universeCodeCell domainLevel flag) ∧
        HasTypeNativeUnion profile (context.cons domainAnn) codomainCode
          (universeCodeCell codomainLevel flag) ∧
        HasTypeNativeUnion profile (context.cons domainAnn) body codomainCode) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      rcases innerInversion subjectShape with ⟨pinnedClassifier, hostInner, convInner⟩ |
        ⟨codomainCode, domainLevel, codomainLevel, flag, convInner, domainFormed,
          codomainFormed, bodyTyped⟩
      · exact Or.inl ⟨pinnedClassifier, hostInner, convInner.trans converts⟩
      · exact Or.inr ⟨codomainCode, domainLevel, codomainLevel, flag,
          convInner.trans converts, domainFormed, codomainFormed, bodyTyped⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact Or.inl ⟨_, hostTyped, Conv.refl _⟩
  | ofBaseType baseTyped =>
      exact absurd (baseTypeSubjectHeadExcluded rfl baseTyped subjectShape) (fun contra => contra)
  | ofDataIntro dataTyped =>
      exact absurd (dataIntroSubjectHeadExcluded rfl dataTyped subjectShape) (fun contra => contra)
  | ofTermIndexedFormer formerTyped =>
      exact absurd (termIndexedFormerSubjectHeadExcluded rfl formerTyped subjectShape)
        (fun contra => contra)
  | gradedBinderIntro ctx generator rule typeParamA typeParamB armBody domainLevel codomainLevel
      flag isIntro binderGraded domainFormed classifierFormed bodyTyped =>
      rcases gradedIntroRuleOf_isLamOrPathLam isIntro with hLam | hPath
      · subst hLam
        have ruleEq : rule = lamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
        subst ruleEq
        rcases subjectShape with ⟨⟩
        exact Or.inr ⟨typeParamB, domainLevel, codomainLevel, flag,
          Conv.refl _, domainFormed rfl, classifierFormed rfl, bodyTyped⟩
      · subst hPath
        have ruleEq : rule = pathLamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | generalElim ctx generator rule typeParamA typeParamB typeParamC typeParamD eliminated argument
      isElim eliminatedTyped argumentTyped =>
      rcases generalElimRuleOf_isAppOrPathApp isElim with hApp | hPath
      · subst hApp
        have ruleEq : rule = appGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathAppGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_pathApp)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | ofNatIntro natTyped =>
      rcases natTyped.subjectIsNatConstructor with isZero | ⟨_, isSucc⟩
      · exact absurd (subjectShape.symm.trans isZero) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isSucc) (by intro headEq; cases headEq)
  | recursiveElim ctx generator rule motive baseBranch stepBranch scrutinee resultType
      isRecursiveElim scrutineeTyped baseBranchTyped =>
      rcases nativeRecursiveElimRuleOf_isNatElimOrNatRec isRecursiveElim with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | ofOptionIntro optionTyped =>
      rcases optionTyped.subjectIsOptionConstructor with isNone | ⟨_, isSome⟩
      · exact absurd (subjectShape.symm.trans isNone) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isSome) (by intro headEq; cases headEq)
  | ofEitherIntro eitherTyped =>
      rcases eitherTyped.subjectIsEitherInjection with ⟨_, isInl⟩ | ⟨_, isInr⟩
      · exact absurd (subjectShape.symm.trans isInl) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isInr) (by intro headEq; cases headEq)
  | ofIdIntro idTyped =>
      obtain ⟨_, isRefl⟩ := idTyped.subjectIsRefl
      exact absurd (subjectShape.symm.trans isRefl) (by intro headEq; cases headEq)
  | ofPairIntro pairTyped =>
      obtain ⟨_, _, isPair⟩ := pairTyped.subjectIsPair
      exact absurd (subjectShape.symm.trans isPair) (by intro headEq; cases headEq)
  | ofListIntro listTyped =>
      rcases listTyped.subjectIsListConstructor with isNil | ⟨_, _, isCons⟩
      · exact absurd (subjectShape.symm.trans isNil) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isCons) (by intro headEq; cases headEq)
  | twoBranchMatchElim ctx generator rule motive firstBranch secondBranch scrutinee
      typeParamA typeParamB resultType isTwoBranchMatch scrutineeTyped firstBranchTyped
      secondBranchTyped =>
      rcases nativeTwoBranchMatchRuleOf_cases isTwoBranchMatch with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pathInductionElim ctx generator rule motive baseCase witness typeCode endpoint resultType
      isPathInduction witnessTyped baseCaseTyped =>
      obtain ⟨_, ruleEq⟩ := nativePathInductionRuleOf_cases isPathInduction
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | projectionElim ctx generator rule pairTerm firstType secondType isProjection pairTyped =>
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveUnaryIntro ctx generator rule child isRecursiveUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveUnaryDataIntroRuleOf_cases isRecursiveUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveBinaryIntro ctx generator rule head tail elementType isRecursiveBinary headTyped
      tailTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveBinaryDataIntroRuleOf_cases isRecursiveBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pinnedUnaryIntro ctx generator rule child elementType isPinnedUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativePinnedUnaryDataIntroRuleOf_cases isPinnedUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nullaryFreeTypeIntro ctx generator rule elementType elementLevel flag isNullaryFreeType
      elementTypeFormed =>
      obtain ⟨_, ruleEq⟩ := nativeNullaryFreeTypeDataIntroRuleOf_cases isNullaryFreeType
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | coproductIntro ctx generator rule value pinnedType freeType freeLevel flag isCoproduct valueTyped
      freeTypeFormed =>
      rcases nativeCoproductDataIntroRuleOf_cases isCoproduct with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nonDependentBinaryIntro ctx generator rule firstChild secondChild firstType secondType
      isNonDependentBinary firstTyped secondTyped =>
      obtain ⟨_, ruleEq⟩ := nativeNonDependentBinaryDataIntroRuleOf_cases isNonDependentBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | reflexiveIntro ctx generator rule witness witnessType isReflexive witnessTyped =>
      obtain ⟨_, ruleEq⟩ := nativeReflexiveDataIntroRuleOf_cases isReflexive
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | listElim ctx generator rule motive scrutinee nilBranch consBranch elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)

/-! ## (1) The master per-head inversion — instantiated for the natElim head

The natElim head has ONE survivor: the recursive-eliminator arm at the `gen_natElim` row.  The grown engine is
refuted in place by the shipped `HasTypeDescPi.natElimCellHasNoTyping` (natElim is a recursive eliminator, in no
host root, `typingRuleDescOf gen_natElim = none`), so there is no ofGrown disjunct — a clean single survivor.  The
recursive-eliminator natRec row dies by head clash; every other arm dies likewise. -/

/-- **★ Inversion at the natElim head.**  A union typing of a `natElimCell`-headed subject is EXACTLY a
recursive-eliminator typing at the `gen_natElim` row: the scrutinee is union-typed at `Nat` and the base (zero)
branch is union-typed at the classifier.  (The motive and the step branch are stored, not premised — premise
parity with `HasTypeDescNatElim`; they are not surfaced.)  No grown disjunct: `natElimCell` is untypable in the
grown engine. -/
theorem HasTypeNativeUnion.invertAtNatElimHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = natElimCell motive zeroBranch stepBranch scrutinee) :
    HasTypeNativeUnion profile context scrutinee natTypeCell ∧
    HasTypeNativeUnion profile context zeroBranch classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨scrutineeTyped, zeroBranchTyped⟩ := innerInversion subjectShape
      exact ⟨scrutineeTyped,
        HasTypeNativeUnion.conv levelExpr flag zeroBranchTyped converts reclassifierTyped⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.natElimCellHasNoTyping (fun contra => contra)
  | ofBaseType baseTyped =>
      exact absurd (baseTypeSubjectHeadExcluded rfl baseTyped subjectShape) (fun contra => contra)
  | ofDataIntro dataTyped =>
      exact absurd (dataIntroSubjectHeadExcluded rfl dataTyped subjectShape) (fun contra => contra)
  | ofTermIndexedFormer formerTyped =>
      exact absurd (termIndexedFormerSubjectHeadExcluded rfl formerTyped subjectShape)
        (fun contra => contra)
  | gradedBinderIntro ctx generator rule typeParamA typeParamB armBody domainLevel codomainLevel
      flag isIntro binderGraded domainFormed classifierFormed bodyTyped =>
      rcases gradedIntroRuleOf_isLamOrPathLam isIntro with hLam | hPath
      · subst hLam
        have ruleEq : rule = lamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathLamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | generalElim ctx generator rule typeParamA typeParamB typeParamC typeParamD eliminated argument
      isElim eliminatedTyped argumentTyped =>
      rcases generalElimRuleOf_isAppOrPathApp isElim with hApp | hPath
      · subst hApp
        have ruleEq : rule = appGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathAppGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_pathApp)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | ofNatIntro natTyped =>
      rcases natTyped.subjectIsNatConstructor with isZero | ⟨_, isSucc⟩
      · exact absurd (subjectShape.symm.trans isZero) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isSucc) (by intro headEq; cases headEq)
  | recursiveElim ctx generator rule armMotive armBase armStep armScrut resultType
      isRecursiveElim scrutineeTyped baseBranchTyped =>
      rcases nativeRecursiveElimRuleOf_isNatElimOrNatRec isRecursiveElim with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      · subst ruleEq
        rcases subjectShape with ⟨⟩
        exact ⟨scrutineeTyped, baseBranchTyped⟩
      · subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | ofOptionIntro optionTyped =>
      rcases optionTyped.subjectIsOptionConstructor with isNone | ⟨_, isSome⟩
      · exact absurd (subjectShape.symm.trans isNone) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isSome) (by intro headEq; cases headEq)
  | ofEitherIntro eitherTyped =>
      rcases eitherTyped.subjectIsEitherInjection with ⟨_, isInl⟩ | ⟨_, isInr⟩
      · exact absurd (subjectShape.symm.trans isInl) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isInr) (by intro headEq; cases headEq)
  | ofIdIntro idTyped =>
      obtain ⟨_, isRefl⟩ := idTyped.subjectIsRefl
      exact absurd (subjectShape.symm.trans isRefl) (by intro headEq; cases headEq)
  | ofPairIntro pairTyped =>
      obtain ⟨_, _, isPair⟩ := pairTyped.subjectIsPair
      exact absurd (subjectShape.symm.trans isPair) (by intro headEq; cases headEq)
  | ofListIntro listTyped =>
      rcases listTyped.subjectIsListConstructor with isNil | ⟨_, _, isCons⟩
      · exact absurd (subjectShape.symm.trans isNil) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isCons) (by intro headEq; cases headEq)
  | twoBranchMatchElim ctx generator rule motive firstBranch secondBranch scrutinee
      typeParamA typeParamB resultType isTwoBranchMatch scrutineeTyped firstBranchTyped
      secondBranchTyped =>
      rcases nativeTwoBranchMatchRuleOf_cases isTwoBranchMatch with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pathInductionElim ctx generator rule motive baseCase witness typeCode endpoint resultType
      isPathInduction witnessTyped baseCaseTyped =>
      obtain ⟨_, ruleEq⟩ := nativePathInductionRuleOf_cases isPathInduction
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | projectionElim ctx generator rule pairTerm firstType secondType isProjection pairTyped =>
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveUnaryIntro ctx generator rule child isRecursiveUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveUnaryDataIntroRuleOf_cases isRecursiveUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveBinaryIntro ctx generator rule head tail elementType isRecursiveBinary headTyped
      tailTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveBinaryDataIntroRuleOf_cases isRecursiveBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pinnedUnaryIntro ctx generator rule child elementType isPinnedUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativePinnedUnaryDataIntroRuleOf_cases isPinnedUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nullaryFreeTypeIntro ctx generator rule elementType elementLevel flag isNullaryFreeType
      elementTypeFormed =>
      obtain ⟨_, ruleEq⟩ := nativeNullaryFreeTypeDataIntroRuleOf_cases isNullaryFreeType
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | coproductIntro ctx generator rule value pinnedType freeType freeLevel flag isCoproduct valueTyped
      freeTypeFormed =>
      rcases nativeCoproductDataIntroRuleOf_cases isCoproduct with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nonDependentBinaryIntro ctx generator rule firstChild secondChild firstType secondType
      isNonDependentBinary firstTyped secondTyped =>
      obtain ⟨_, ruleEq⟩ := nativeNonDependentBinaryDataIntroRuleOf_cases isNonDependentBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | reflexiveIntro ctx generator rule witness witnessType isReflexive witnessTyped =>
      obtain ⟨_, ruleEq⟩ := nativeReflexiveDataIntroRuleOf_cases isReflexive
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | listElim ctx generator rule motive scrutinee nilBranch consBranch elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)

/-! ## (1) The master per-head inversion — instantiated for the natSucc head

The natSucc head has TWO survivors (the two-path fact from batch 2): the recursive-unary data-intro arm at the
`gen_natSucc` row (native path) AND the `ofNatIntro` embedding (a `HasTypeDescNatIntro` derivation whose subject
is a `natSucc`).  The grown engine is refuted in place by `HasTypeDescPi.natSuccCellHasNoTyping` (natSucc is a
data constructor), so there is no ofGrown disjunct. -/

/-- **★ Inversion at the natSucc head.**  A union typing of a `natSuccCell`-headed subject is EITHER a recursive
unary data-introduction at the `gen_natSucc` row (the classifier is `Nat` and the predecessor child is
union-typed at `Nat` — the native path) OR an `ofNatIntro` embedding (the subject is typed by the standalone Nat
constructor engine — the embedding path; its predecessor premise lives inside the surfaced derivation).  The
two-path disjunction documents the batch-2 fact that the numeral tower composes both natively and through the
embedding.  No grown disjunct: `natSuccCell` is untypable in the grown engine. -/
theorem HasTypeNativeUnion.invertAtNatSuccHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {child : RawTerm scope}
    (derivation : HasTypeNativeUnion profile context subject classifier)
    (subjectShape : subject = natSuccCell child) :
    (Conv natTypeCell classifier ∧ HasTypeNativeUnion profile context child natTypeCell)
    ∨ (∃ pinnedClassifier : RawTerm scope,
        HasTypeDescNatIntro profile context (natSuccCell child) pinnedClassifier ∧
        Conv pinnedClassifier classifier) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      rcases innerInversion subjectShape with ⟨convInner, childTyped⟩ |
        ⟨pinnedClassifier, natTyped, convInner⟩
      · exact Or.inl ⟨convInner.trans converts, childTyped⟩
      · exact Or.inr ⟨pinnedClassifier, natTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.natSuccCellHasNoTyping (fun contra => contra)
  | ofBaseType baseTyped =>
      exact absurd (baseTypeSubjectHeadExcluded rfl baseTyped subjectShape) (fun contra => contra)
  | ofDataIntro dataTyped =>
      exact absurd (dataIntroSubjectHeadExcluded rfl dataTyped subjectShape) (fun contra => contra)
  | ofTermIndexedFormer formerTyped =>
      exact absurd (termIndexedFormerSubjectHeadExcluded rfl formerTyped subjectShape)
        (fun contra => contra)
  | gradedBinderIntro ctx generator rule typeParamA typeParamB armBody domainLevel codomainLevel
      flag isIntro binderGraded domainFormed classifierFormed bodyTyped =>
      rcases gradedIntroRuleOf_isLamOrPathLam isIntro with hLam | hPath
      · subst hLam
        have ruleEq : rule = lamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathLamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | generalElim ctx generator rule typeParamA typeParamB typeParamC typeParamD eliminated argument
      isElim eliminatedTyped argumentTyped =>
      rcases generalElimRuleOf_isAppOrPathApp isElim with hApp | hPath
      · subst hApp
        have ruleEq : rule = appGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
      · subst hPath
        have ruleEq : rule = pathAppGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_pathApp)
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | ofNatIntro natTyped =>
      rw [subjectShape] at natTyped
      exact Or.inr ⟨_, natTyped, Conv.refl _⟩
  | recursiveElim ctx generator rule motive baseBranch stepBranch scrutinee resultType
      isRecursiveElim scrutineeTyped baseBranchTyped =>
      rcases nativeRecursiveElimRuleOf_isNatElimOrNatRec isRecursiveElim with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | ofOptionIntro optionTyped =>
      rcases optionTyped.subjectIsOptionConstructor with isNone | ⟨_, isSome⟩
      · exact absurd (subjectShape.symm.trans isNone) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isSome) (by intro headEq; cases headEq)
  | ofEitherIntro eitherTyped =>
      rcases eitherTyped.subjectIsEitherInjection with ⟨_, isInl⟩ | ⟨_, isInr⟩
      · exact absurd (subjectShape.symm.trans isInl) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isInr) (by intro headEq; cases headEq)
  | ofIdIntro idTyped =>
      obtain ⟨_, isRefl⟩ := idTyped.subjectIsRefl
      exact absurd (subjectShape.symm.trans isRefl) (by intro headEq; cases headEq)
  | ofPairIntro pairTyped =>
      obtain ⟨_, _, isPair⟩ := pairTyped.subjectIsPair
      exact absurd (subjectShape.symm.trans isPair) (by intro headEq; cases headEq)
  | ofListIntro listTyped =>
      rcases listTyped.subjectIsListConstructor with isNil | ⟨_, _, isCons⟩
      · exact absurd (subjectShape.symm.trans isNil) (by intro headEq; cases headEq)
      · exact absurd (subjectShape.symm.trans isCons) (by intro headEq; cases headEq)
  | twoBranchMatchElim ctx generator rule motive firstBranch secondBranch scrutinee
      typeParamA typeParamB resultType isTwoBranchMatch scrutineeTyped firstBranchTyped
      secondBranchTyped =>
      rcases nativeTwoBranchMatchRuleOf_cases isTwoBranchMatch with
        ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pathInductionElim ctx generator rule motive baseCase witness typeCode endpoint resultType
      isPathInduction witnessTyped baseCaseTyped =>
      obtain ⟨_, ruleEq⟩ := nativePathInductionRuleOf_cases isPathInduction
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | projectionElim ctx generator rule pairTerm firstType secondType isProjection pairTyped =>
      rcases nativeProjectionRuleOf_cases isProjection with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | recursiveUnaryIntro ctx generator rule armChild isRecursiveUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveUnaryDataIntroRuleOf_cases isRecursiveUnary
      subst ruleEq
      rcases subjectShape with ⟨⟩
      exact Or.inl ⟨Conv.refl natTypeCell, childTyped⟩
  | recursiveBinaryIntro ctx generator rule head tail elementType isRecursiveBinary headTyped
      tailTyped =>
      obtain ⟨_, ruleEq⟩ := nativeRecursiveBinaryDataIntroRuleOf_cases isRecursiveBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | pinnedUnaryIntro ctx generator rule child elementType isPinnedUnary childTyped =>
      obtain ⟨_, ruleEq⟩ := nativePinnedUnaryDataIntroRuleOf_cases isPinnedUnary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nullaryFreeTypeIntro ctx generator rule elementType elementLevel flag isNullaryFreeType
      elementTypeFormed =>
      obtain ⟨_, ruleEq⟩ := nativeNullaryFreeTypeDataIntroRuleOf_cases isNullaryFreeType
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | coproductIntro ctx generator rule value pinnedType freeType freeLevel flag isCoproduct valueTyped
      freeTypeFormed =>
      rcases nativeCoproductDataIntroRuleOf_cases isCoproduct with ⟨_, ruleEq⟩ | ⟨_, ruleEq⟩
      all_goals
        subst ruleEq
        exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | nonDependentBinaryIntro ctx generator rule firstChild secondChild firstType secondType
      isNonDependentBinary firstTyped secondTyped =>
      obtain ⟨_, ruleEq⟩ := nativeNonDependentBinaryDataIntroRuleOf_cases isNonDependentBinary
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | reflexiveIntro ctx generator rule witness witnessType isReflexive witnessTyped =>
      obtain ⟨_, ruleEq⟩ := nativeReflexiveDataIntroRuleOf_cases isReflexive
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | listElim ctx generator rule motive scrutinee nilBranch consBranch elementType resultType
      isListElim scrutineeTyped nilBranchTyped consBranchTyped =>
      obtain ⟨_, ruleEq⟩ := listElimNativeRuleOf_cases isListElim
      subst ruleEq
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)

/-! ## (3) ★ The union-wide affine rejection (the Rung-103 headline)

The dimension-duplicating path abstraction `pathLam(pair(var 0, var 0))` — whose body uses the freshest
(dimension) binder TWICE — is untypable in the WHOLE native union, at EVERY classifier and EVERY context.  This is
the union-level form of the NATIVE-23 graded-engine rejection (`gradedIntroEngine_rejectsDoubleDimensionUse`), the
pin the seed-union docstring marked as wave work.  The proof routes through `invertAtPathLamHead` (free-index
inversion — never `cases` at the concrete subject) and kills BOTH surviving disjuncts: the grown disjunct by
`pathLamCellHasNoTyping` (deliverable 2), the graded disjunct because the `.one` affine check demands occurrence
`≤ 1` while the double-use body occurs `2` times (`doubleDimensionUseBody_occurrenceIsTwo`).  The body is the
shipped `doubleDimensionUseBody scope` (at scope `scope`, the body lives at `scope + 1`, exactly the pathLam
binder depth). -/

/-- **★ The union rejects the affine double-use path abstraction.**  `pathLam(pair(var 0, var 0))` is untypable
in `HasTypeNativeUnion` at EVERY classifier and EVERY context: the union-wide form of the affine-grade rejection.
The first kernel theorem where a typing is refused by a usage grade read from a table row across the ENTIRE
unified judgment — every arm that could carry a pathLam head is either head-untyped (the grown disjunct) or
constrained by the affine binder check (the graded disjunct), and the double-use body violates the latter. -/
theorem HasTypeNativeUnion.unionRejectsAffineDoubleUse {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) :
    ¬ HasTypeNativeUnion profile context
        (pathLamCell (doubleDimensionUseBody scope)) classifier := by
  intro derivation
  rcases derivation.invertAtPathLamHead rfl with ⟨_, hostTyped, _⟩ |
    ⟨carrierCode, _, _, bodyAffine, _, _⟩
  · exact hostTyped.pathLamCellHasNoTyping
  · -- `bodyAffine : gradedBinderChecks .one body` defeq `occurrenceCountAt body 0 ≤ 1`; the body occurs twice.
    have occurrenceBound :
        RawTerm.occurrenceCountAt (doubleDimensionUseBody scope) ⟨0, Nat.succ_pos scope⟩ ≤ 1 :=
      bodyAffine
    rw [doubleDimensionUseBody_occurrenceIsTwo] at occurrenceBound
    exact absurd occurrenceBound (Nat.not_succ_le_self 1)

/-! ## (5) Coverage record + witness -/

/-- **The NATIVE-37 inversion coverage record.**  Each field is a distinct live property of the first
eliminations over the native union: the host pathLam-head refutation, the four per-head inversions, and the
union-wide affine rejection.  An inhabitant certifies the inversion substrate is exercised (constructed, not just
declared). -/
structure NativeUnionInversionCoverage (profile : PolyProfile) : Prop where
  /-- The grown engine types no pathLam-headed subject. -/
  grownRejectsPathLamHead : ∀ {scope : Nat} {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {classifier : RawTerm scope},
    HasTypeDescPi profile context (pathLamCell body) classifier → False
  /-- The pathLam-head inversion holds (grown disjunct ∨ graded pathLam-row premises), each
  Conv-modulo: the conv arm reclassifies, so the pinned classifier is convertible to the actual one. -/
  pathLamInversion : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {body : RawTerm (scope + 1)},
    HasTypeNativeUnion profile context subject classifier →
    subject = pathLamCell body →
    (∃ pinnedClassifier : RawTerm scope,
        HasTypeDescPi profile context (pathLamCell body) pinnedClassifier ∧
        Conv pinnedClassifier classifier)
    ∨ (∃ (carrierCode pinnedClassifier : RawTerm scope),
        pinnedClassifier = bridgeTypeCell carrierCode
          (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell) ∧
        gradedBinderChecks UsageGrade.one body ∧
        HasTypeNativeUnion profile (context.cons intervalTypeCell) body
          (RawTerm.weaken carrierCode) ∧
        Conv pinnedClassifier classifier)
  /-- The natElim-head inversion holds (the single recursive-eliminator survivor). -/
  natElimInversion : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {motive : RawTerm (scope + 1)}
    {zeroBranch : RawTerm scope} {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope},
    HasTypeNativeUnion profile context subject classifier →
    subject = natElimCell motive zeroBranch stepBranch scrutinee →
    HasTypeNativeUnion profile context scrutinee natTypeCell ∧
    HasTypeNativeUnion profile context zeroBranch classifier
  /-- The natSucc-head inversion holds (the two-path survivors), Conv-modulo: the conv arm
  reclassifies, so the pinned `Nat`/NatIntro classifier is convertible to the actual one. -/
  natSuccInversion : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {child : RawTerm scope},
    HasTypeNativeUnion profile context subject classifier →
    subject = natSuccCell child →
    (Conv natTypeCell classifier ∧ HasTypeNativeUnion profile context child natTypeCell)
    ∨ (∃ pinnedClassifier : RawTerm scope,
        HasTypeDescNatIntro profile context (natSuccCell child) pinnedClassifier ∧
        Conv pinnedClassifier classifier)
  /-- The union rejects the affine double-use path abstraction at every classifier and context. -/
  affineDoubleUseRejected : ∀ {scope : Nat} (context : TypingContext profile scope)
    (classifier : RawTerm scope),
    ¬ HasTypeNativeUnion profile context
        (pathLamCell (doubleDimensionUseBody scope)) classifier

/-- **★ The NATIVE-37 inversion coverage gate** — inhabited by the shipped declarations, so the exercised
inversion-substrate property set can NOT silently shrink. -/
theorem nativeUnionInversionCoverageWitness {profile : PolyProfile} :
    NativeUnionInversionCoverage profile where
  grownRejectsPathLamHead := fun typed => typed.pathLamCellHasNoTyping
  pathLamInversion := fun derivation subjectShape => derivation.invertAtPathLamHead subjectShape
  natElimInversion := fun derivation subjectShape => derivation.invertAtNatElimHead subjectShape
  natSuccInversion := fun derivation subjectShape => derivation.invertAtNatSuccHead subjectShape
  affineDoubleUseRejected := fun context classifier =>
    HasTypeNativeUnion.unionRejectsAffineDoubleUse context classifier

end FX1Poly.Typed
