import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionFormationHeadInversion
import FX1Poly.Typed.Metatheory.Universe.NativeUniverseClassificationUnique

/-! # FX1Poly/Typed/Metatheory/Validity/HasTypeUnionFormerConvKeepingInversion
    — the NATIVE code-inverters retiring the grown former inverters (TYTAB-2-RETIRE Tier D)

The grown engine ships three former inverters the Tier-D consumers reach for:

  * `HasTypeDescPi.invertPiTyCode` — Conv-KEEPING Π-code inversion (domain + codomain component typings
    AND a classifier `Conv` to the former's output universe code);
  * `HasTypeDescPi.inversionUniverseCode` — universe-code inversion (`Conv classifier
    (universeCodeCell level.lsucc flag)`);
  * `HasTypeDescPi.inversionPiCodeComponents` — Conv-DROPPING Π-code inversion (the two component typings
    only, for output validity).

Their native `HasTypeUnion` mirrors are shipped here (returning the premises in `HasTypeUnion` form):

  * `HasTypeUnion.inversionPiCodeComponentsUnion` — a thin corollary of the already-shipped
    `HasTypeUnion.invertAtPiCodeHeadComponents` (Conv-dropping) with the concrete `piTyCodeCell` subject.
  * `HasTypeUnion.inversionUniverseCodeUnion` — a thin corollary of the already-shipped
    `HasTypeUnion.invertAtUniverseCodeHeadGeneric`, specialised to a concrete `universeCodeCell` subject
    (universe-code injectivity collapses the surfaced subject shape, exposing the successor `Conv`).
  * `HasTypeUnion.invertPiTyCodeUnion` — the ONE genuinely-new native inverter: the Conv-KEEPING Π-code
    inversion.  Same bespoke six-arm `toNativeOnly` induction as `invertAtPiCodeHeadComponents`, but the
    surviving `formationRule` arm's classifier is DEFINITIONALLY the row output
    `universeFormerOutput scope levels flag = universeCodeCell (lmaxAll levels) flag`, so the base `Conv`
    is `Conv.refl`, and the `conv` arm re-threads by `converts.sym.trans` (mirroring the shipped
    `invertAtUniverseCodeHeadGeneric` conv arm).  The Conv target is the ROW-NATIVE output level
    (`lmaxAll levels`, existentially quantified as `outputLevel`), NOT the grown two-level
    reconstruction `lmaxAll [domainLevel, codomainLevel]` — the two are NOT defeq under `lmax`
    lzero-absorption / surplus-`levels`, and the SR former-reassembly `cong` arm re-derives its output
    from the same obligations, so the row-native target suffices (see the level-reconciliation note in
    `NativeUniverseClassificationUnique`).

## Zero-axiom

The `toNativeOnly` six-arm induction with `introRuleOf_cases` / `elimRuleOf_cases` head-clash refutations
(inherited verbatim from `invertAtPiCodeHeadComponents`), the `formationRuleOf`-pin + `List.Mem` premise
reads, and `Conv.refl` / `Conv.sym` / `Conv.trans` + `Conv.universeCode_injective`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/Typed/Metatheory/Validity/HasTypeUnionFormerConvKeepingInversion.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-- **★ Native Conv-DROPPING Π-code component inversion** (mirrors grown `inversionPiCodeComponents`).
A union typing of a `piTyCodeCell domainCode codomainCode` subject surfaces BOTH the domain validity and
the codomain-under-binder validity at a common flag — a thin corollary of `invertAtPiCodeHeadComponents`
with the concrete subject shape. -/
theorem HasTypeUnion.inversionPiCodeComponentsUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (typed : HasTypeUnion profile context (piTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeUnion profile context domainCode (universeCodeCell domainLevel flag) ∧
      HasTypeUnion profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag) :=
  HasTypeUnion.invertAtPiCodeHeadComponents typed rfl

/-- **★ Native universe-code inversion** (mirrors grown `inversionUniverseCode`).  A union typing of a
`universeCodeCell subjectLevel subjectFlag` subject forces the classifier `Conv`-equal to the strict
predicative successor `universeCodeCell subjectLevel.lsucc subjectFlag`.  The generic head inversion
`invertAtUniverseCodeHeadGeneric` surfaces the subject's own (level, flag) as an existential; universe-code
injectivity collapses that back to the known `subjectLevel` / `subjectFlag`, exposing the successor `Conv`. -/
theorem HasTypeUnion.inversionUniverseCodeUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {subjectLevel : LevelExpr} {subjectFlag : UniverseFlag}
    (typed : HasTypeUnion profile context (universeCodeCell subjectLevel subjectFlag) classifier) :
    Conv (universeCodeCell subjectLevel.lsucc subjectFlag) classifier := by
  obtain ⟨surfacedLevel, surfacedFlag, subjectShape, successorConv⟩ :=
    HasTypeUnion.invertAtUniverseCodeHeadGeneric typed rfl
  have subjectConv : Conv (universeCodeCell subjectLevel subjectFlag : RawTerm scope)
      (universeCodeCell surfacedLevel surfacedFlag) :=
    subjectShape ▸ Conv.refl (universeCodeCell subjectLevel subjectFlag)
  obtain ⟨levelEq, flagEq⟩ := Conv.universeCode_injective subjectConv
  rw [levelEq, flagEq]
  exact successorConv

/-- **★ Native Conv-KEEPING Π-code former inversion** (the native retirement of grown
`HasTypeDescPi.invertPiTyCode`).  A union typing of a `piTyCodeCell domainCode codomainCode` subject at
`classifier` surfaces the domain validity, the codomain-under-binder validity (both at a common `flag`),
AND `Conv classifier (universeCodeCell outputLevel flag)` at the ROW-NATIVE output level `outputLevel`.
Same bespoke six-arm `toNativeOnly` induction as `invertAtPiCodeHeadComponents`: var / universe refute by
root-generator clash, intro / elim by `introRuleOf_cases` / `elimRuleOf_cases` head clash, the surviving
`formationRule` arm hands back both obligations plus `Conv.refl` at its own row output, and the `conv` arm
re-threads the classifier `Conv` by `converts.sym.trans`. -/
theorem HasTypeUnion.invertPiTyCodeUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (derivation : HasTypeUnion profile context (piTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel outputLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeUnion profile context domainCode (universeCodeCell domainLevel flag) ∧
      HasTypeUnion profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag) ∧
      Conv classifier (universeCodeCell outputLevel flag) := by
  generalize subjectShapeEq : piTyCodeCell domainCode codomainCode = subject at derivation
  have subjectShape : subject = piTyCodeCell domainCode codomainCode := subjectShapeEq.symm
  clear subjectShapeEq
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨domainLevel, codomainLevel, outputLevel, resultFlag, domainTyped, codomainTyped,
          classifierConv⟩ := innerInversion subjectShape
      exact ⟨domainLevel, codomainLevel, outputLevel, resultFlag, domainTyped, codomainTyped,
        converts.sym.trans classifierConv⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold =>
      have headEq : generator = Generator.gen_piTyCode :=
        congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      obtain rfl : rule = FormationRule.cumulative { outputType := universeFormerOutput } :=
        Option.some.inj isFormationRule.symm
      match children, subjectShape with
      | .childCons childDomain (.childCons childCodomain .childNil), subjectShape =>
          rcases subjectShape with ⟨⟩
          cases levels with
          | nil =>
              exact ⟨LevelExpr.lzero, LevelExpr.lzero, lmaxAll ([] : List LevelExpr), flag,
                (premisesHold _ (List.Mem.head _)).toUnion,
                (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion, Conv.refl _⟩
          | cons domainLevel restLevels =>
              cases restLevels with
              | nil =>
                  exact ⟨LevelExpr.lzero, LevelExpr.lzero, lmaxAll [domainLevel], flag,
                    (premisesHold _ (List.Mem.head _)).toUnion,
                    (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion, Conv.refl _⟩
              | cons codomainLevel restLevels2 =>
                  exact ⟨domainLevel, codomainLevel,
                    lmaxAll (domainLevel :: codomainLevel :: restLevels2), flag,
                    (premisesHold _ (List.Mem.head _)).toUnion,
                    (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion, Conv.refl _⟩
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
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

end FX1Poly.Typed
