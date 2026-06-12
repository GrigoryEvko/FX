import FX1Poly.Typed.HasTypeDescStronglyNormalizing
import FX1Poly.Typed.WfContextDescUniqueness
import FX1Poly.Typed.FormationCanonicalForms
import FX1Poly.Typed.OptionCodeShape
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.SigmaCodeShape
import FX1Poly.Typed.ListCodeShape

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

## How the consequences are proved

All THREE closed-form consequences are proved on the native formation-engine recursion:

* `closedSubjectIsTypeDesc` recurses on the description engine directly (`var` killed by `Fin 0`, `conv`
  recurses, `universeFormation` is a universe code, `genFormation` reads its output type off the
  `typingRuleDescOf` table) — the scope is generalised to a free variable with a `scope = 0` equation so the
  `conv` recursion is structural;
* `closedSubjectIsTypeFormer` (the STRUCTURAL shape, with the domain/codomain existentials) composes the
  HEAD-generator form `closedSubjectHeadIsFormerOrUniverse` (`FormationCanonicalForms.lean`) with the
  head-to-children reconstructions `eq_{piTyCodeCell,sigmaTyCodeCell,universeCodeCell}_of_headGenerator`
  (`UniverseCodeShape.lean` / `SigmaCodeShape.lean`, the `childCons` dependent-index drilling);
* `closedClassifierConvUniverseCode` consumes `closedSubjectIsTypeDesc` and the uniqueness
  `HasTypeDesc.uniqueness` (over `WfContextDesc.emptyIsWellFormed`).

## Zero-axiom verification

The native proofs use the propext-free formation recursion + `typingRuleDescOf_output_isUniverseCode` + the
native uniqueness (`HasTypeDesc.uniqueness`) + the native head-canonical-forms + the `eq_*_of_headGenerator`
reconstructions.  No `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

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
      obtain ⟨outputLevel, outputFlag, hOutput⟩ :=
        typingRuleDescOf_output_isUniverseCode isFormation _ levels flag
      refine ⟨outputLevel, outputFlag, ?_⟩
      have rebuilt := HasTypeDesc.genFormation context generator payload children levels flag rule
        isFormation premises
      rwa [hOutput] at rebuilt

/-- Closed description-engine subjects in the formation engine are themselves description-engine types.
The native formation recursion via `closedSubjectIsTypeDescGeneral`. -/
theorem HasTypeDesc.closedSubjectIsTypeDesc {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    IsTypeDesc profile TypingContext.empty subject :=
  HasTypeDesc.closedSubjectIsTypeDescGeneral rfl typed

/-- Closed-form shape for the description formation engine: a closed description-typed subject is a
universe, Pi-code, Sigma-code, list-code, option-code, or unit-code cell.

The HEAD-generator form `closedSubjectHeadIsFormerOrUniverse`
(`FormationCanonicalForms.lean`) pins the head to `gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode` /
`gen_listCode` / `gen_optionCode` / `gen_unitCode`, and the head-to-children reconstructions
(`eq_piTyCodeCell_of_headGenerator` / `eq_sigmaTyCodeCell_of_headGenerator` /
`eq_universeCodeCell_of_headGenerator` / `eq_listCodeCell_of_headGenerator` /
`eq_optionCodeCell_of_headGenerator` / `eq_unitCodeCell_of_headGenerator`, the `childCons` dependent-index
drilling — collapsing to the empty `childNil` spine in the nullary unit case) lift each head to its full
structural existential (the unit case has no child, so its shape is the bare `gen_unitCode` cell). -/
theorem HasTypeDesc.closedSubjectIsTypeFormer {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    (∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
        subject = universeCodeCell levelExpr flag) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = piTyCodeCell domainCode codomainCode) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = sigmaTyCodeCell domainCode codomainCode) ∨
      (∃ element : RawTerm 0,
        subject = .mkGen .gen_listCode () (.childCons element .childNil)) ∨
      (∃ element : RawTerm 0,
        subject = .mkGen .gen_optionCode () (.childCons element .childNil)) ∨
      subject = .mkGen .gen_unitCode () .childNil := by
  rcases HasTypeDesc.closedSubjectHeadIsFormerOrUniverse typed with
    headPi | headSigma | headUniverse | headList | headOption | headUnit
  · exact Or.inr (Or.inl (eq_piTyCodeCell_of_headGenerator headPi))
  · exact Or.inr (Or.inr (Or.inl (eq_sigmaTyCodeCell_of_headGenerator headSigma)))
  · exact Or.inl (eq_universeCodeCell_of_headGenerator headUniverse)
  · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_listCodeCell_of_headGenerator headList))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_optionCodeCell_of_headGenerator headOption)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_unitCodeCell_of_headGenerator headUnit)))))

/-- Consistency-facing classifier shape for the description formation engine: every closed
description-typed subject has a classifier convertible to a universe code.  `closedSubjectIsTypeDesc`
supplies the subject's universe typing, and the uniqueness `HasTypeDesc.uniqueness` (over
`WfContextDesc.emptyIsWellFormed`) reconciles it with the actual classifier. -/
theorem HasTypeDesc.closedClassifierConvUniverseCode {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      Conv classifier (universeCodeCell levelExpr flag) := by
  obtain ⟨levelExpr, flag, subjectTypedAtUniverse⟩ := HasTypeDesc.closedSubjectIsTypeDesc typed
  exact ⟨levelExpr, flag,
    HasTypeDesc.uniqueness typed WfContextDesc.emptyIsWellFormed subjectTypedAtUniverse⟩

end FX1Poly.Typed
