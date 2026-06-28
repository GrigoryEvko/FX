import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiDataHeadUntyped
import FX1Poly.Typed.Cell.NatElimDependentSuccType
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility
import FX1Poly.Typed.Engine.Union.HasTypeUnionMemberCellRootGenerator
import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericElimInversion
import FX1Poly.Typed.Dimensions.Graded.AppScaledSubstMetatheory

/-! # FX1Poly/Typed/HasTypeUnionInversion — NATIVE-37: the FIRST eliminations over the native union

This file performs the first-ever `cases`/`induction` over `HasTypeUnion`.  After the TYTAB-1 arm collapse the
arm set is five constructors (`ofGrown · formationRule · intro · elim · conv`): one grown-engine embedding, the
unified table-driven `formationRule` arm (base-type / flat / term-indexed formation in one), the unified
table-driven `intro` arm (all introducer families in one), the unified table-driven `elim` arm (all eliminator
families in one), and the conversion arm.  Free-subject `cases` over the union is propext-clean (verified in the
audit shard), so this file establishes THE inversion pattern that all later union metatheory (subject reduction,
substitution, reverse adequacy) replicates.

## THE PER-ARM DISCRIMINATION RECIPE (replicate this for the remaining heads)

To invert a union typing at a concrete head `H` (subject `= <H-headed cell>`), state the inversion with a FREE
subject, take `subjectShape : subject = <H-headed cell>` as a hypothesis, then `cases` the derivation (safe at a
FREE index — never `cases` at a concrete cell index, the equation-motive propext trap).  In each of the five
arms the threaded `subjectShape` discriminates:

  * **The unified `formationRule` arm whose table cannot produce an `H`-head** — refute via the arm's
    table membership: the arm pins `subject = .mkGen generator _ _` with `formationRuleOf generator = some rule`;
    `congrArg RawTerm.rootGenerator` forces `generator = H`, and `formationRuleOf H = none` (`rfl`) contradicts the
    membership (the unified `formationRule` arm covers the base-type / flat / term-indexed families, reading
    `baseTypeRuleDescOf` / `flatTypingRuleDescOf` / `termIndexedFormerDescOf` per family).
  * **The grown engine (`ofGrown`)** — refuted only for the pathLam head, by the new
    `HasTypeDescPi.pathLamCellHasNoTyping` (deliverable 2 below — `gen_pathLam` is in no host root and carries
    no formation rule).  For all other heads `ofGrown` is left as an honest disjunct.
  * **Table-driven arm whose member-cell head ≠ `H`** — invert the arm's row table (`<table>Of_cases`; for the
    unified `intro` / `elim` arms, `introRuleOf_cases` / `elimRuleOf_cases` with the `introMemberCellRootGenerator`
    / `elimMemberCellRootGenerator` head-projections) to pin `rule` to a concrete row, making `rule.memberCell` a
    concrete cell, then refute via `congrArg RawTerm.rootGenerator subjectShape` head clash.
  * **Table-driven arm whose member-cell head = `H`** — the SURVIVING disjunct.  Pin the row, `injections` the
    threaded equation to recover the arm's children, and surface every premise (the graded check, the recursive
    body/branch premises) as existentials.

## What this file ships (deliverables, priority order)

  1. `HasTypeUnion.invertAtPathLamHead` / `invertAtLamHead` / `invertAtNatElimHead` /
     `invertAtNatSuccHead` — the master per-head inversion instantiated for four representative heads.
  2. `HasTypeDescPi.pathLamCellHasNoTyping` — the host pathLam-head refutation (the lemma named in Rung 103,
     extending the `HasTypeDescPiDataHeadUntyped` pattern: `gen_pathLam` is in no host root and no formation
     table).
  3. `HasTypeUnion.unionRejectsAffineDoubleUse` — ★ the union-wide affine rejection: the
     dimension-duplicating path abstraction `pathLam(pair(var 0, var 0))` is untypable in the UNION at EVERY
     classifier and EVERY context.  The ofGrown disjunct dies by (2); the gradedBinderIntro disjunct dies because
     the `.one` graded check fails on the double-use body (occurrence count `2`, the NATIVE-23 rejection
     machinery).
  3b. `HasTypeUnion.pathLamSubjectIsAffine` — ★ the affine-honesty pin, union-side: every union-typed
     pathLam body uses the dimension binder AT MOST ONCE (`occurrenceCountAt body 0 ≤ 1`).  The FORCED-grade
     successor of the retired `HasTypeDescBridge.pathLamSubjectIsAffine`: the grown disjunct dies by (2), the
     graded disjunct surfaces the row's affine binder check directly.
  4. The pattern note (this docstring).
  5. Coverage record + witness.

## Zero-axiom

The host refutation is the one-line `cellHasNoTypingWhenRootGenericallyExcluded` application; the inversions are
free-subject `cases` + table inversions + head-generator no-confusion + `injections`; the affine rejection routes
through `invertAtPathLamHead` (free-index inversion, never `cases` at the concrete subject) + the shipped
`doubleDimensionUseBody_occurrenceIsTwo` count fact.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditUnionInversion.lean`. -/

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

/-- **`pathApp`-headed cells are untyped in the grown engine.**  `gen_pathApp` is a data eliminator (in no
host root, `typingRuleDescOf gen_pathApp = none`), so the grown engine types no `pathApp`-headed subject —
the path-elimination twin of `HasTypeDescPi.natElimCellHasNoTyping`, closing the ofGrown disjunct of
`invertAtPathAppHead`. -/
theorem HasTypeDescPi.pathAppCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {path argument classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (pathAppCell path argument) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;>
    (first | (intro contra; cases contra) | rfl)

/-! The member-cell root-generator projections (`elimMemberCellRootGenerator` /
`introMemberCellRootGenerator`) now live UPSTREAM in `HasTypeUnionMemberCellRootGenerator` so the
table-driven generic inversion can sit above every per-head inversion it subsumes; they are re-exported
here transitively for the `lam` / `pathLam` / `natSucc` inversions below. -/

/-! ## (1) The master per-head inversion — instantiated for the pathLam head

Inverts over the ofGrown-free `HasTypeUnionNativeOnly` reflection (`pathLamCellHasNoTyping` already shows the
grown engine types no pathLam, so the host embedding contributes nothing), surfacing the graded
binder-introduction premises of the pathLam row DIRECTLY with no grown disjunct.  Every other arm is refuted in
place by its engine's subject-head characterization or its row table's head clash. -/

/-- **★ Inversion at the pathLam head.**  A union typing of a pathLam-headed subject is a graded
binder-introduction at the pathLam row: the classifier is forced to the bridge code at the body's endpoint
substitutions, the affine `.one` graded check holds on the body, and the body is union-typed at the weakened
carrier under the interval-extended context.  (Native-only: the former grown disjunct is dropped — `gen_pathLam`
heads no grown-typed cell, so it was always vacuous.) -/
theorem HasTypeUnion.invertAtPathLamHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {body : RawTerm (scope + 1)}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = pathLamCell body) :
    ∃ (carrierCode pinnedClassifier : RawTerm scope),
      pinnedClassifier = bridgeTypeCell carrierCode
        (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell) ∧
      gradedBinderChecks UsageGrade.one body ∧
      HasTypeUnion profile (context.lockCons intervalTypeCell) body
        (RawTerm.weaken carrierCode) ∧
      Conv pinnedClassifier classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨carrierCode, pinnedClassifier, bridgeEq, bodyAffine, bodyTyped, convInner⟩ :=
        innerInversion subjectShape
      exact ⟨carrierCode, pinnedClassifier, bridgeEq, bodyAffine, bodyTyped,
        convInner.trans converts⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: only the `gen_pathLam` row produces a `pathLam`-headed cell; the
      -- other sixteen introducer heads clash with the `pathLam` subject head.
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
      -- ★ pathLam — the SURVIVOR.  Destructure args (`[1]`) + params (`[0]`), recover the body from
      -- `subjectShape`, and surface the affine check (`sideHolds`) + the body premise (`premisesHold`).
      · match args, params with
        | .childCons _armBody .childNil, .childCons _carrierCode .childNil =>
          rcases subjectShape with ⟨⟩
          -- The swapped side condition surfaces the BETA-STABLE App-scaled affine grade
          -- (`appScaled body 0 ≤ one`); the inversion's count-shaped affine conclusion
          -- (`gradedBinderChecks .one body` defeq `occ body 0 ≤ 1`) follows because the App-scaled grade
          -- DOMINATES the raw count (`appScaledAffine_impliesCountAffine`), so downstream consumers of the
          -- inversion's `bodyAffine` keep their count interface unchanged.
          exact ⟨_, _, rfl, RawTerm.appScaledAffine_impliesCountAffine _ _ sideHolds,
            (premisesHold _ (List.Mem.head _)).toUnion, Conv.refl _⟩
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
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: no eliminator row produces a `pathLam`-headed cell, so the row's
      -- generator clashes with `gen_pathLam` (which is in no eliminator row, `elimRuleOf gen_pathLam = none`).
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_pathLam :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-! ## (1) The master per-head inversion — instantiated for the lam head

The lam head inverts over the ofGrown-free `HasTypeUnionNativeOnly` reflection (`iff_nativeOnly` proves the
host embedding redundant — every grown-typed λ also types natively at the λ row), so the inversion surfaces the
graded binder-introduction premises DIRECTLY with no grown disjunct.  The pathLam row of the graded arm dies by
head clash; every other arm dies by its engine's subject-head characterization or its row's head clash. -/

/-- **★ Inversion at the lam head.**  A union typing of a `lamCell`-headed subject is a graded
binder-introduction at the λ row: the classifier is a Π code over the annotated domain and some codomain, the
domain is union-formed at a universe, the codomain is union-formed under the domain, and the body is
union-typed at the codomain.  (The λ row's graded check is the unrestricted `.omega`, vacuous, so it is not
surfaced.  Native-only: the former grown disjunct is dropped — redundant by `iff_nativeOnly`.) -/
theorem HasTypeUnion.invertAtLamHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = lamCell domainAnn body) :
    ∃ (codomainCode : RawTerm (scope + 1)) (domainLevel codomainLevel : LevelExpr)
        (flag : UniverseFlag),
      Conv (piTyCodeCell domainAnn codomainCode) classifier ∧
      HasTypeUnion profile context domainAnn (universeCodeCell domainLevel flag) ∧
      HasTypeUnion profile (context.cons domainAnn) codomainCode
        (universeCodeCell codomainLevel flag) ∧
      HasTypeUnion profile (context.cons domainAnn) body codomainCode := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨codomainCode, domainLevel, codomainLevel, flag, convInner, domainFormed,
          codomainFormed, bodyTyped⟩ := innerInversion subjectShape
      exact ⟨codomainCode, domainLevel, codomainLevel, flag,
        convInner.trans converts, domainFormed, codomainFormed, bodyTyped⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: only the `gen_lam` row produces a `lam`-headed cell; the other
      -- sixteen introducer heads clash with the `lam` subject head.
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
      -- ★ lam — the SURVIVOR.  Destructure args (`[0, 1]`) + params (`[1]`), recover the domain
      -- annotation + body from `subjectShape`, and surface the three formation/body premises.
      · match args, params with
        | .childCons _domainCode (.childCons _armBody .childNil), .childCons _codomainCode .childNil =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, level0, level1, flag, Conv.refl _,
            (premisesHold _ (List.Mem.head _)).toUnion,
            (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion,
            (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))).toUnion⟩
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
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: no eliminator row produces a `lam`-headed cell, so the row's
      -- generator clashes with `gen_lam` (which is in no eliminator row, `elimRuleOf gen_lam = none`).
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_lam :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-! ## (1) The master per-head inversion — instantiated for the natElim head

The natElim head has ONE survivor: the recursive-eliminator arm at the `gen_natElim` row.  The grown engine is
refuted in place by the shipped `HasTypeDescPi.natElimCellHasNoTyping` (natElim is a recursive eliminator, in no
host root, `typingRuleDescOf gen_natElim = none`), so there is no ofGrown disjunct — a clean single survivor.  The
recursive-eliminator natRec row dies by head clash; every other arm dies likewise. -/

/-- **★ Inversion at the natElim head (DEPENDENT).**  A union typing of a `natElimCell`-headed subject is
EXACTLY a recursive-eliminator typing at the `gen_natElim` row: the scrutinee is union-typed at `Nat`, the
base (zero) branch is union-typed at its DEPENDENT zero type `subst0 motive natZeroCell` (= the eliminator's
output when the scrutinee is `natZero`), and the dependent output `subst0 motive scrutinee` is `Conv`-related
to the ambient classifier.  (The motive and the step branch are stored, not surfaced by this light inversion —
the succ branch needs the two-binder `invertAtNatElimHeadAllPremises`.)  No grown disjunct: `natElimCell` is
untypable in the grown engine.  The recursive-eliminator twin of `invertAtBoolElimHead`. -/
theorem HasTypeUnion.invertAtNatElimHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = natElimCell motive zeroBranch stepBranch scrutinee) :
    HasTypeUnion profile context scrutinee natTypeCell ∧
    HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
    Conv (RawTerm.subst0 motive scrutinee) classifier := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `natElim` row (no type params, `params =
  -- childNil`; obligation order `[scrutinee, baseBranch, stepBranch, motive]`; `outputType = subst0 motive
  -- scrutinee`).  The recursive-eliminator twin of the `natRec` wrapper.
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := natElimRule)
      (show elimRuleOf Generator.gen_natElim = some natElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argBase (.childCons _argStep (.childCons _argScrut .childNil))),
    .childNil, subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      outputConv⟩

/-- **★ Full inversion at the natElim head — all four DEPENDENT `natElimRule` premises surfaced.**  The richer
twin of `invertAtNatElimHead`: a union typing of a `natElimCell`-headed subject surfaces the scrutinee at
`Nat`, the base branch at its dependent zero type `subst0 motive natZeroCell`, the step branch at the
two-binder dependent succ type `natElimDependentSuccBranchType motive` in the two-cell-extended context
`(context.cons natTypeCell).cons motive`, the motive's universe formedness over `context.cons natTypeCell`,
and the `Conv` of the dependent output `subst0 motive scrutinee` to the ambient classifier.  The exact premise
set the unconditional natElim-succ subject reduction needs (the four dependent `natElimRule.obligations` plus
the `outputType = subst0 motive scrutinee` identification).  No grown disjunct (`natElimCellHasNoTyping`). -/
theorem HasTypeUnion.invertAtNatElimHeadAllPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = natElimCell motive zeroBranch stepBranch scrutinee) :
    ∃ (resultLevel : FX1Poly.Universe.LevelExpr)
      (resultFlag : FX1Poly.Universe.UniverseFlag),
      HasTypeUnion profile context scrutinee natTypeCell ∧
      HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
      HasTypeUnion profile ((context.cons natTypeCell).cons motive)
        stepBranch (natElimDependentSuccBranchType motive) ∧
      HasTypeUnion profile (context.cons natTypeCell) motive
        (universeCodeCell resultLevel resultFlag) ∧
      Conv (RawTerm.subst0 motive scrutinee) classifier := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `natElim` row surfacing ALL four obligations;
  -- the motive obligation's universe levels are the row's existential `level0`/`flag` (here OUTERMOST).
  obtain ⟨args, params, level0, _level1, flag, subjectIsMember, obligationsHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := natElimRule)
      (show elimRuleOf Generator.gen_natElim = some natElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argBase (.childCons _argStep (.childCons _argScrut .childNil))),
    .childNil, subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨level0, flag,
      obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
      outputConv⟩

/-! ## (1) The master per-head inversion — instantiated for the natSucc head

The natSucc head has ONE survivor since the NATIVE-42 embedding-arm deletion: the unified `intro` arm at
the `gen_natSucc` row.  (The `ofNatIntro` embedding was the second survivor; its arm is GONE, so the
inversion is now exact — no disjunction.)  The grown engine is refuted in place by
`HasTypeDescPi.natSuccCellHasNoTyping` (natSucc is a data constructor), so there is no ofGrown
disjunct either. -/

/-- **★ Inversion at the natSucc head (EXACT since NATIVE-42).**  A union typing of a `natSuccCell`-headed
subject IS a recursive unary data-introduction at the `gen_natSucc` row: the classifier is convertible to
`Nat` and the predecessor child is union-typed at `Nat`.  The pre-NATIVE-42 statement carried a second
`ofNatIntro`-embedding disjunct; with that arm deleted the inversion strengthened to the exact row shape —
this is the predecessor-recursion door the DEEP numeral extraction
(`HasTypeUnion.closedNormalNatNumeral`) walks through. -/
theorem HasTypeUnion.invertAtNatSuccHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {child : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = natSuccCell child) :
    Conv natTypeCell classifier ∧ HasTypeUnion profile context child natTypeCell := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨convInner, childTyped⟩ := innerInversion subjectShape
      exact ⟨convInner.trans converts, childTyped⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: only the `gen_natSucc` row produces a `natSucc`-headed cell; the
      -- other sixteen introducer heads clash with the `natSucc` subject head.
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
      -- ★ natSucc — the SURVIVOR.  Destructure args (`[0]`), recover the predecessor from
      -- `subjectShape`, surface its `Nat` premise; the output type is `Nat`, so the Conv is `refl`.
      · match args with
        | .childCons _armChild .childNil =>
          rcases subjectShape with ⟨⟩
          exact ⟨Conv.refl natTypeCell, (premisesHold _ (List.Mem.head _)).toUnion⟩
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
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: no eliminator row produces a `natSucc`-headed cell (natSucc is a
      -- recursive data constructor), so the row's generator clashes with `gen_natSucc`
      -- (`elimRuleOf gen_natSucc = none`).
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_natSucc :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

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
in `HasTypeUnion` at EVERY classifier and EVERY context: the union-wide form of the affine-grade rejection.
The first kernel theorem where a typing is refused by a usage grade read from a table row across the ENTIRE
unified judgment — every arm that could carry a pathLam head is either head-untyped (the grown disjunct) or
constrained by the affine binder check (the graded disjunct), and the double-use body violates the latter. -/
theorem HasTypeUnion.unionRejectsAffineDoubleUse {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) :
    ¬ HasTypeUnion profile context
        (pathLamCell (doubleDimensionUseBody scope)) classifier := by
  intro derivation
  obtain ⟨carrierCode, _, _, bodyAffine, _, _⟩ := derivation.invertAtPathLamHead rfl
  -- `bodyAffine : gradedBinderChecks .one body` defeq `occurrenceCountAt body 0 ≤ 1`; the body occurs twice.
  have occurrenceBound :
      RawTerm.occurrenceCountAt (doubleDimensionUseBody scope) ⟨0, Nat.succ_pos scope⟩ ≤ 1 :=
    bodyAffine
  rw [doubleDimensionUseBody_occurrenceIsTwo] at occurrenceBound
  exact absurd occurrenceBound (Nat.not_succ_le_self 1)

/-! ## (3b) ★ The affine-honesty pin, union-side (the retired `HasTypeDescBridge.pathLamSubjectIsAffine`)

The retired bespoke bridge engine carried `pathLamSubjectIsAffine`: every typed pathLam body uses the
dimension binder AT MOST ONCE — the grade is FORCED by the engine, not merely permitted.  With the bridge
retired into the union, this positive pin must hold UNION-side.  It does, unconditionally: a union typing of
ANY pathLam-headed subject inverts (free-index, via `invertAtPathLamHead`) into the grown disjunct — impossible
by `pathLamCellHasNoTyping` (`gen_pathLam` heads no grown-typed cell) — or the graded pathLam-row disjunct,
which surfaces exactly the row's affine binder check `gradedBinderChecks UsageGrade.one body` (defeq
`occurrenceCountAt body 0 ≤ 1`).  So the only surviving image forces the affine bound: the union never types a
pathLam whose body uses the dimension binder twice. -/

/-- **★ Affine honesty pin, union-side.**  Every pathLam body that the union types uses the dimension binder
AT MOST ONCE: `occurrenceCountAt body 0 ≤ 1`.  The grade is FORCED by the pathLam row's `UsageGrade.one` binder
check, not merely permitted — the union-side successor of the retired `HasTypeDescBridge.pathLamSubjectIsAffine`.
The grown disjunct of the inversion is impossible (`pathLamCellHasNoTyping`), leaving the graded disjunct, whose
`bodyAffine` premise IS the bound. -/
theorem HasTypeUnion.pathLamSubjectIsAffine {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (derivation : HasTypeUnion profile context (pathLamCell body) classifier) :
    RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1 := by
  obtain ⟨_, _, _, bodyAffine, _, _⟩ := derivation.invertAtPathLamHead rfl
  -- `bodyAffine : gradedBinderChecks .one body` is defeq `occurrenceCountAt body 0 ≤ 1`.
  exact bodyAffine

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
  /-- The pathLam-head inversion holds (native-only: the graded pathLam-row premises directly — the former
  grown disjunct is dropped, redundant by `iff_nativeOnly`), Conv-modulo: the conv arm reclassifies, so the
  pinned classifier is convertible to the actual one. -/
  pathLamInversion : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {body : RawTerm (scope + 1)},
    HasTypeUnion profile context subject classifier →
    subject = pathLamCell body →
    ∃ (carrierCode pinnedClassifier : RawTerm scope),
      pinnedClassifier = bridgeTypeCell carrierCode
        (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell) ∧
      gradedBinderChecks UsageGrade.one body ∧
      HasTypeUnion profile (context.lockCons intervalTypeCell) body
        (RawTerm.weaken carrierCode) ∧
      Conv pinnedClassifier classifier
  /-- The natElim-head inversion holds (the single recursive-eliminator survivor). -/
  natElimInversion : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {motive : RawTerm (scope + 1)}
    {zeroBranch : RawTerm scope} {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope},
    HasTypeUnion profile context subject classifier →
    subject = natElimCell motive zeroBranch stepBranch scrutinee →
    HasTypeUnion profile context scrutinee natTypeCell ∧
    HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
    Conv (RawTerm.subst0 motive scrutinee) classifier
  /-- The natSucc-head inversion holds (EXACT since the NATIVE-42 embedding-arm deletion),
  Conv-modulo: the conv arm reclassifies, so the pinned `Nat` classifier is convertible to the
  actual one. -/
  natSuccInversion : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {child : RawTerm scope},
    HasTypeUnion profile context subject classifier →
    subject = natSuccCell child →
    Conv natTypeCell classifier ∧ HasTypeUnion profile context child natTypeCell
  /-- The union rejects the affine double-use path abstraction at every classifier and context. -/
  affineDoubleUseRejected : ∀ {scope : Nat} (context : TypingContext profile scope)
    (classifier : RawTerm scope),
    ¬ HasTypeUnion profile context
        (pathLamCell (doubleDimensionUseBody scope)) classifier
  /-- Every union-typed pathLam body uses the dimension binder at most once (the affine-honesty pin,
  union-side — the FORCED grade, successor of the retired `HasTypeDescBridge.pathLamSubjectIsAffine`). -/
  pathLamBodyAffine : ∀ {scope : Nat} {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {classifier : RawTerm scope},
    HasTypeUnion profile context (pathLamCell body) classifier →
    RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1

/-- **★ The NATIVE-37 inversion coverage gate** — inhabited by the shipped declarations, so the exercised
inversion-substrate property set can NOT silently shrink. -/
theorem nativeUnionInversionCoverageWitness {profile : PolyProfile} :
    NativeUnionInversionCoverage profile where
  grownRejectsPathLamHead := fun typed => typed.pathLamCellHasNoTyping
  pathLamInversion := fun derivation subjectShape => derivation.invertAtPathLamHead subjectShape
  natElimInversion := fun derivation subjectShape => derivation.invertAtNatElimHead subjectShape
  natSuccInversion := fun derivation subjectShape => derivation.invertAtNatSuccHead subjectShape
  affineDoubleUseRejected := fun context classifier =>
    HasTypeUnion.unionRejectsAffineDoubleUse context classifier
  pathLamBodyAffine := fun derivation => derivation.pathLamSubjectIsAffine

end FX1Poly.Typed
