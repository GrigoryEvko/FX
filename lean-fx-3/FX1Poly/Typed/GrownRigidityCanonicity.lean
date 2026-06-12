import FX1Poly.Typed.GrownClosedNormalClassifierShape
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.WeakNormalization
import FX1Poly.Typed.ConvBoolCodeRigidity

/-! # FX1Poly/Typed/GrownRigidityCanonicity
    — the GENERIC arbitrary-subject grown-vacuity engine: every data canonicity is now a per-type one-liner

Last firing closed bool canonicity by the syntactic route (SN + SR-U4 + closed-normal forms), but its grown
vacuity `HasTypeDescPi.noClosedGrownTermAtBoolType` was bool-SPECIFIC, and the generic
`dataCanonicityFromSyntacticRoute` took the grown vacuity as a HYPOTHESIS.  The reusable lemma behind every
data-classifier rule-out is already generic at the NORMAL level — `noClosedNormalTermAtDataClassifier` (#1065):
a classifier `Conv` neither a Π-code nor a universe code has no closed-NORMAL grown inhabitant.  This file lifts
it to ARBITRARY subjects (the missing generic bridge) and packages canonicity so callers supply only two shipped
non-convertibilities:

  * **`HasTypeDescPi.noClosedGrownTermAtDataClassifier` (★)** — the GENERIC arbitrary-subject grown vacuity.  A
    closed term grown-typed at a classifier `Conv` neither a Π-code nor a universe code is impossible: grown SN
    (`stronglyNormalizingOfWfContextDesc`) reaches a normal form, SR-U4 (`subjectReductionStar`) preserves the
    classifier EXACTLY, and `noClosedNormalTermAtDataClassifier` settles the normal form.  Subsumes last firing's
    `noClosedGrownTermAtBoolType` (= this at the bool non-convertibilities).

  * **`dataCanonicityFromGrownRigidity` (★)** — the generic canonicity packaging.  An abstract standalone-value
    predicate (its canonicity) + the two grown non-convertibilities ⟹ combined standalone-plus-grown canonicity,
    with the grown disjunct DERIVED here (not assumed).  The upgrade over `dataCanonicityFromSyntacticRoute`:
    callers stop having to prove the grown vacuity themselves — they supply the two shipped rigidities
    (`Conv.<dataCode>_not_piTyCode` / `_not_universeCode`).

  * **`boolCanonicityViaGrownRigidity`** — bool through the generic packaging (non-vacuity witness, = the direct
    `closedBoolCanonicalForms`), and **`HasTypeDescPi.noClosedGrownTermAtSigmaType`** — the Σ grown vacuity at an
    arbitrary subject (the grown half of future Σ-canonicity; the arbitrary-subject twin of #1065's normal-only
    `noClosedNormalTermAtSigmaType`).  Two type families — a nullary data classifier and a binary type former —
    demonstrate the engine is genuinely generic, not a bool refactor.

So SN-049 (closed data canonicity: List/Option/Either/Pair/Sum/Unit) is now a per-type one-liner: instantiate
`dataCanonicityFromGrownRigidity` with the type's standalone closed-canonical-forms + its two shipped
`Conv`-rigidities.  The eliminator engine (`HasTypeDescDataElim`, the 4th engine, #1138) remains the follow-on for
fully-non-vacuous eliminator-computing canonicity.

## Zero-axiom verification

The generic vacuity is grown SN + `exists_normalForm_of_isStronglyNormalizing` + SR-U4 + the shipped #1065
rule-out; the packaging is a two-way `rcases`; the instances supply shipped `Conv`-rigidities
(`Conv.boolTypeCell_not_piTyCode` / `_not_universeCode`, `Conv.piTyCode_not_sigmaTyCode` /
`Conv.sigmaTyCode_not_universeCode`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The generic arbitrary-subject grown vacuity.**  A closed term grown-typed at a classifier `Conv` neither
a Π-code nor a universe code is impossible.  Grown SN reaches a normal form, SR-U4 `subjectReductionStar`
preserves the classifier, and `noClosedNormalTermAtDataClassifier` (#1065) settles it.  The reusable engine behind
every data-classifier grown rule-out: supply the two non-convertibilities, get the rule-out for an arbitrary
subject (not just normal).  Subsumes the bool-specific `noClosedGrownTermAtBoolType`. -/
theorem HasTypeDescPi.noClosedGrownTermAtDataClassifier {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier)
    (notFunction : ∀ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
      ¬ Conv classifier (piTyCodeCell domainCode codomainCode))
    (notType : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv classifier (universeCodeCell levelExpr flag)) :
    False := by
  have terminates :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed
  obtain ⟨normalForm, reachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing terminates
  exact HasTypeDescPi.noClosedNormalTermAtDataClassifier
    (HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed typed reachesNormalForm)
    normalFormIsNormal notFunction notType

/-- **★ Generic canonicity packaging — the grown vacuity DERIVED, not assumed.**  An abstract standalone-value
predicate `StandaloneTyped` carrying its canonicity, plus the two grown non-convertibilities of `dataTypeCode`,
gives combined standalone-plus-grown canonicity: a closed term satisfying the standalone layer OR grown-typed at
`dataTypeCode` reduces to an `isValue`.  The standalone arm is the premise; the grown arm is
`noClosedGrownTermAtDataClassifier`.  Strengthens
`dataCanonicityFromSyntacticRoute` (which took the grown vacuity as a hypothesis) — callers now supply the two
shipped `Conv`-rigidities instead. -/
theorem dataCanonicityFromGrownRigidity {profile : PolyProfile} {isValue : RawTerm 0 → Prop}
    {dataTypeCode : RawTerm 0} {StandaloneTyped : RawTerm 0 → Prop}
    (standaloneCanonicity : ∀ subject : RawTerm 0, StandaloneTyped subject →
      ∃ value : RawTerm 0, StepStar subject value ∧ isValue value)
    (notFunction : ∀ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
      ¬ Conv dataTypeCode (piTyCodeCell domainCode codomainCode))
    (notType : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv dataTypeCode (universeCodeCell levelExpr flag))
    (subject : RawTerm 0)
    (typed : StandaloneTyped subject ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode) :
    ∃ value : RawTerm 0, StepStar subject value ∧ isValue value := by
  rcases typed with standaloneTyped | grownTyped
  · exact standaloneCanonicity subject standaloneTyped
  · exact (HasTypeDescPi.noClosedGrownTermAtDataClassifier grownTyped notFunction notType).elim

/-- The union-layer standalone predicate for a closed cell at `boolTypeCell`: the subject is a
`dataIntroNullary` row OR a `baseTypeFormation` row whose output is `boolTypeCell`. -/
def boolStandaloneRowTypedGrown (subject : RawTerm 0) : Prop :=
  (∃ (generator : Generator) (payload : generator.payload 0)
      (children : RawTermChildren generator.binderShifts 0) (rule : DataIntroNullaryRuleDesc),
      subject = RawTerm.mkGen generator payload children ∧
      dataIntroNullaryRuleDescOf generator = some rule ∧
      rule.outputTypeCode 0 = boolTypeCell)
  ∨ (∃ (generator : Generator) (payload : generator.payload 0)
      (children : RawTermChildren generator.binderShifts 0) (rule : BaseTypeRuleDesc),
      subject = RawTerm.mkGen generator payload children ∧
      baseTypeRuleDescOf generator = some rule ∧
      rule.outputUniverse 0 = boolTypeCell)

/-- **Bool canonicity through the generic packaging** — non-vacuity witness; the same statement as the direct
`closedBoolCanonicalForms`, now factored through `dataCanonicityFromGrownRigidity` with the shipped bool
rigidities (`Conv.boolTypeCell_not_piTyCode` / `_not_universeCode`) and `standaloneBoolCanonicalForms`, the
standalone disjuncts taken over the union `dataIntroNullary` / `baseTypeFormation` rows. -/
theorem boolCanonicityViaGrownRigidity {profile : PolyProfile} {subject : RawTerm 0}
    (typed : boolStandaloneRowTypedGrown subject ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) := by
  refine dataCanonicityFromGrownRigidity
    (profile := profile)
    (isValue := fun value => value = boolTrueCell ∨ value = boolFalseCell)
    (StandaloneTyped := boolStandaloneRowTypedGrown)
    (fun _standaloneSubject standaloneTyped => by
      rcases standaloneTyped with
          ⟨generator, payload, children, rule, subjectEq, isDataIntro, classifierEq⟩
        | ⟨generator, payload, children, rule, subjectEq, isBaseType, classifierEq⟩
      · subst subjectEq
        rcases standaloneBoolCanonicalForms (generator := generator) (payload := payload)
            (children := children) (Or.inl ⟨rule, isDataIntro, classifierEq⟩) with valueEq | valueEq
        · rw [valueEq]; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
        · rw [valueEq]; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
      · subst subjectEq
        rcases standaloneBoolCanonicalForms (generator := generator) (payload := payload)
            (children := children) (Or.inr ⟨rule, isBaseType, classifierEq⟩) with valueEq | valueEq
        · rw [valueEq]; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
        · rw [valueEq]; exact ⟨_, StepStar.refl _, Or.inr rfl⟩)
    (fun _domainCode _codomainCode convToPiCode => Conv.boolTypeCell_not_piTyCode convToPiCode)
    (fun _levelExpr _flag convToUniverseCode => Conv.boolTypeCell_not_universeCode convToUniverseCode)
    subject typed

/-- **The grown engine has no closed inhabitant of a Σ-type (arbitrary subject)** — second instantiation of the
generic vacuity, the arbitrary-subject twin of #1065's normal-only `noClosedNormalTermAtSigmaType`.  `sigmaTyCode`
is `Conv` neither a Π-code (`Conv.piTyCode_not_sigmaTyCode`) nor a universe code
(`Conv.sigmaTyCode_not_universeCode`).  The grown half of future Σ-canonicity. -/
theorem HasTypeDescPi.noClosedGrownTermAtSigmaType {profile : PolyProfile} {subject : RawTerm 0}
    {sigmaDomain : RawTerm 0} {sigmaCodomain : RawTerm 1}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (sigmaTyCodeCell sigmaDomain sigmaCodomain)) :
    False :=
  HasTypeDescPi.noClosedGrownTermAtDataClassifier typed
    (fun _domainCode _codomainCode convToPiCode => Conv.piTyCode_not_sigmaTyCode convToPiCode.sym)
    (fun _levelExpr _flag convToUniverseCode => Conv.sigmaTyCode_not_universeCode convToUniverseCode)

end FX1Poly.Typed
