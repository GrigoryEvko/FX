import FX1Poly.Typed.HasTypeClosedForms
import FX1Poly.Typed.HasTypeDescStronglyNormalizing
import FX1Poly.Typed.WfContextDescUniqueness

/-! # FX1Poly/Typed/HasTypeDescClosedForms
    — closed-form consequences for the description formation engine

The description formation engine `HasTypeDesc` types only type FORMERS (Π / Σ via `genFormation`), universe
CODES (`universeFormation`), variables (`var`), and conversions thereof (`conv`).  This file packages the
closed-context (empty-scope) consequences downstream metatheory consumes:

* a closed description-typed subject is an intrinsic `IsTypeDesc`;
* syntactically, a closed description-typed subject is a universe / Pi / Sigma type former; and
* its classifier is convertible to a universe code.

The scope is exactly the description formation engine.  These are not claims about the grown
`HasTypeDescPi` engine with lambda/application.

## HasType-free status (HT-A3)

Two of the three are now proved WITHOUT the `HasTypeDesc.toHasType` soundness bridge or the bespoke
`HasType` closed-form oracle, on the native formation-engine recursion alone (part of the phased `HasType`
removal):

* `closedSubjectIsTypeDesc` recurses on the description engine directly (`var` killed by `Fin 0`, `conv`
  recurses, `universeFormation` is a universe code, `genFormation` reads its output type off the
  `typingRuleDescOf` table) — the scope is generalised to a free variable with a `scope = 0` equation so the
  `conv` recursion is structural;
* `closedClassifierConvUniverseCode` consumes the native `closedSubjectIsTypeDesc` and the native uniqueness
  `HasTypeDesc.uniquenessNative` (over `WfContextDesc.emptyIsWellFormed`) — no `HasType` oracle.

The remaining `closedSubjectIsTypeFormer` (the STRUCTURAL shape, with the domain/codomain existentials) still
routes through the bespoke `HasType.closedSubjectIsTypeFormer` via `HasTypeDesc.toHasType`: the native shape is
available at the HEAD-generator granularity (`HasTypeDesc.closedSubjectHeadIsFormerOrUniverse`,
`FormationCanonicalForms.lean`), but lifting it to the full structural form requires reconstructing the
former's children from the head generator — a separable sub-brick (the `childCons` dependent-index drilling).

## Zero-axiom verification

The native proofs use the propext-free formation recursion + `typingRuleDescOf_outputIsUniverseFormer` +
the native uniqueness (`HasTypeDesc.uniquenessNative`).  The one remaining transport proof uses the
already-gated equivalence map `HasTypeDesc.toHasType` plus the native closed-form lemma.  No `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Convert a native type witness into the corresponding intrinsic description-engine type witness. -/
theorem IsType.toIsTypeDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsType profile context classifier) :
    IsTypeDesc profile context classifier := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact ⟨levelExpr, flag, HasType.toHasTypeDesc typed⟩

/-- **Scope-generalised workhorse for the closed subject-regularity fact.**  A description-typed subject at
scope `0` (threaded as the free `scope` with a `scope = 0` equation, so the `conv` recursion is structural over
a variable index) is itself a description-engine type.  The `var` arm is impossible (`Fin 0`); `conv` recurses;
`universeFormation` is a universe code; `genFormation` reads its output type off the `typingRuleDescOf` table. -/
theorem HasTypeDesc.closedSubjectIsTypeDescGeneral {profile : PolyProfile} {scope : Nat}
    (scopeZero : scope = 0)
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    IsTypeDesc profile context subject :=
  match typed with
  | .var _context index => by
      subst scopeZero
      exact absurd index.isLt (Nat.not_lt_zero index.val)
  | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
      HasTypeDesc.closedSubjectIsTypeDescGeneral scopeZero typedPremise
  | .universeFormation context levelExpr flag =>
      ⟨levelExpr.lsucc, flag, HasTypeDesc.universeFormation context levelExpr flag⟩
  | .genFormation context generator payload children levels flag rule isFormation premises => by
      refine ⟨lmaxAll levels, flag, ?_⟩
      have rebuilt := HasTypeDesc.genFormation context generator payload children levels flag rule
        isFormation premises
      rwa [typingRuleDescOf_outputIsUniverseFormer isFormation] at rebuilt

/-- Closed description-engine subjects in the formation engine are themselves description-engine types.
HasType-free: the native formation recursion via `closedSubjectIsTypeDescGeneral`. -/
theorem HasTypeDesc.closedSubjectIsTypeDesc {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    IsTypeDesc profile TypingContext.empty subject :=
  HasTypeDesc.closedSubjectIsTypeDescGeneral rfl typed

/-- Closed-form shape for the description formation engine: a closed description-typed subject is a
universe, Pi-code, or Sigma-code cell.

RESIDUAL (HT-A3): this STRUCTURAL form still routes through the bespoke `HasType.closedSubjectIsTypeFormer`
via `HasTypeDesc.toHasType`.  The native HEAD-generator form is `closedSubjectHeadIsFormerOrUniverse`
(`FormationCanonicalForms.lean`); lifting it to the full structural existentials needs the head-to-children
reconstruction (a separable sub-brick). -/
theorem HasTypeDesc.closedSubjectIsTypeFormer {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    (∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
        subject = universeCodeCell levelExpr flag) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = piTyCodeCell domainCode codomainCode) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = sigmaTyCodeCell domainCode codomainCode) :=
  HasType.closedSubjectIsTypeFormer (HasTypeDesc.toHasType typed)

/-- Consistency-facing classifier shape for the description formation engine: every closed
description-typed subject has a classifier convertible to a universe code.  HasType-free: the native
`closedSubjectIsTypeDesc` supplies the subject's universe typing, and the native uniqueness
`HasTypeDesc.uniquenessNative` (over `WfContextDesc.emptyIsWellFormed`) reconciles it with the actual
classifier. -/
theorem HasTypeDesc.closedClassifierConvUniverseCode {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      Conv classifier (universeCodeCell levelExpr flag) := by
  obtain ⟨levelExpr, flag, subjectTypedAtUniverse⟩ := HasTypeDesc.closedSubjectIsTypeDesc typed
  exact ⟨levelExpr, flag,
    HasTypeDesc.uniquenessNative typed WfContextDesc.emptyIsWellFormed subjectTypedAtUniverse⟩

end FX1Poly.Typed
