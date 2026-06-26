import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric
import FX1Poly.Typed.Cell.OptionMatchDependentSomeBranchType
import FX1Poly.Typed.Cell.EitherMatchDependentBranchType
import FX1Poly.Typed.Cell.ListElimDependentConsType
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/DataEliminatorBranchTypeFormedUnderMotiveStep
    — `piTyCode`-wrapped data-eliminator branch types stay formed when the motive steps (SR-DSL-2 type-SR content)

The eliminator-congruence subject reduction (gate 2, the `elim` arm of `UnionCongruenceCloser`) has one
genuinely hard child position — the MOTIVE.  When the motive steps `motive ⟶ motiveAfter`, every dependent
BRANCH classifier built from the motive drifts, and re-typing a branch at its drifted classifier needs that
classifier to be a WELL-FORMED TYPE — the type-SR `templateTypeStepPreservesUniverse` content, per macro-arm.

`DependentBranchTypeFormedFromMotive` ships the `natElim` / `natRec` succ-branch arm (the two-binder re-based
motive, whose head is NOT a former, so its formedness needs the substitution master).  This file ships the
`option` / `either` arms — and the GENERIC keystone they share.

## Why the `piTyCode`-wrapped branches are EASIER than `natElim`'s

`optionMatch`'s some branch, `eitherMatch`'s inl / inr branches are each `piTyCodeCell domain (codomain motive)`
— a Π CODE, a FORMATION VALUE with a `gen_piTyCode` head, regardless of the motive.  So their formedness under a
motive step is just FORMATION subject reduction at the `piTyCode` head: the codomain child steps (the motive's
step lifts through the codomain's defining substitution via `Step.subst`), and the Π code re-forms.

The keystone `HasTypeUnion.piCodeFormedUnderCodomainStep` does this with NO universe-flag uniqueness and NO
descriptor flag-hardening: `invertAtPiCodeHeadComponents` recovers the domain and the (pre-step) codomain at a
COMMON flag, the single-step-SR self-reference re-types the stepped codomain back at that same universe code, and
`piFormed_atCommonFlag` re-forms the Π code.  The common flag the original branch type already carried is reused
verbatim — the flag-coherence "frontier" never appears.

(`listElim`'s cons branch nests THREE `piTyCode`s with the motive occurring TWICE — at `motive tail` and at
`motive (cons head tail)` — so a single `Step.subst` does not lift it; that multi-occurrence arm follows the
`natElim` substitution-master shape and is shipped separately.)

## Zero-axiom verification

`HasTypeUnion.invertAtPiCodeHeadComponents` + `UnionClassifierIsType.piFormed_atCommonFlag` +
`HasTypeUnion.reclassifyToType` over `universeFormation` (universe rigidity) + `Step.subst` (the term-axis
substitution-stability of one-step reduction).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **★ A Π code stays a well-formed type when its codomain steps.**  Given `piTyCodeCell domain codomain` is a
union type and the codomain steps `codomain ⟶ codomainAfter`, `piTyCodeCell domain codomainAfter` is a union
type — using the single-step-SR self-reference to re-type the stepped codomain.  The domain and the pre-step
codomain come at a COMMON flag from `invertAtPiCodeHeadComponents`; the stepped codomain re-types at that same
universe code (`reclassifyToType` over universe rigidity); `piFormed_atCommonFlag` re-forms the Π code at the
inherited flag — no universe-flag uniqueness, no descriptor flag-hardening.  This is the FORMATION subject
reduction every `piTyCode`-wrapped dependent branch classifier reclassifies its branch through when the motive
steps. -/
theorem HasTypeUnion.piCodeFormedUnderCodomainStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {domain : RawTerm scope}
    {codomain codomainAfter : RawTerm (scope + 1)}
    (formed : UnionClassifierIsType profile context (piTyCodeCell domain codomain))
    (codomainStep : Step codomain codomainAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionClassifierIsType profile context (piTyCodeCell domain codomainAfter) := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := formed
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩ :=
    HasTypeUnion.invertAtPiCodeHeadComponents piTyped rfl
  obtain ⟨codomainAfterType, codomainAfterTyped, codomainConv⟩ :=
    childSubjectReduction codomainTyped codomainStep
  refine UnionClassifierIsType.piFormed_atCommonFlag context domain codomainAfter
    domainLevel codomainLevel flag domainTyped ?_
  exact HasTypeUnion.reclassifyToType codomainAfterTyped codomainConv.sym
    ⟨_, _, HasTypeUnion.universeFormation (context.cons domain) codomainLevel flag⟩

/-- **The `optionMatch` some-branch type stays formed when the motive steps.**  The some-branch classifier
`piTyCodeCell valueType (optionMatchDependentSomeBranchCodomain motive)` — the codomain being `motive` re-based
at `some (var 0)` — re-forms when `motive ⟶ motiveAfter`: the motive's step lifts to a codomain step through the
re-basing substitution (`Step.subst`), and `piCodeFormedUnderCodomainStep` re-forms the Π code. -/
theorem optionMatchDependentSomeBranchType_formedUnderMotiveStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {valueType : RawTerm scope}
    {motive motiveAfter : RawTerm (scope + 1)}
    (formed : UnionClassifierIsType profile context
      (optionMatchDependentSomeBranchType motive valueType))
    (motiveStep : Step motive motiveAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionClassifierIsType profile context
      (optionMatchDependentSomeBranchType motiveAfter valueType) := by
  unfold optionMatchDependentSomeBranchType at formed ⊢
  refine HasTypeUnion.piCodeFormedUnderCodomainStep formed ?_ childSubjectReduction
  unfold optionMatchDependentSomeBranchCodomain
  exact Step.subst _ motiveStep

/-- **The `eitherMatch` inl-branch type stays formed when the motive steps.**  The inl-branch classifier
`piTyCodeCell leftType (eitherMatchDependentInlBranchCodomain motive)` re-forms when `motive ⟶ motiveAfter` —
the `option` keystone at the inl re-basing. -/
theorem eitherMatchDependentInlBranchType_formedUnderMotiveStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftType : RawTerm scope}
    {motive motiveAfter : RawTerm (scope + 1)}
    (formed : UnionClassifierIsType profile context
      (eitherMatchDependentInlBranchType motive leftType))
    (motiveStep : Step motive motiveAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionClassifierIsType profile context
      (eitherMatchDependentInlBranchType motiveAfter leftType) := by
  unfold eitherMatchDependentInlBranchType at formed ⊢
  refine HasTypeUnion.piCodeFormedUnderCodomainStep formed ?_ childSubjectReduction
  unfold eitherMatchDependentInlBranchCodomain
  exact Step.subst _ motiveStep

/-- **The `eitherMatch` inr-branch type stays formed when the motive steps** — the inr twin of
`eitherMatchDependentInlBranchType_formedUnderMotiveStep`. -/
theorem eitherMatchDependentInrBranchType_formedUnderMotiveStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {rightType : RawTerm scope}
    {motive motiveAfter : RawTerm (scope + 1)}
    (formed : UnionClassifierIsType profile context
      (eitherMatchDependentInrBranchType motive rightType))
    (motiveStep : Step motive motiveAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionClassifierIsType profile context
      (eitherMatchDependentInrBranchType motiveAfter rightType) := by
  unfold eitherMatchDependentInrBranchType at formed ⊢
  refine HasTypeUnion.piCodeFormedUnderCodomainStep formed ?_ childSubjectReduction
  unfold eitherMatchDependentInrBranchCodomain
  exact Step.subst _ motiveStep

/-- **The `listElim` cons-branch type stays formed when the motive steps.**  Unlike `option` / `either`, the cons
branch `piTyCodeCell elementType (piTyCodeCell (listTypeCell (weaken elementType)) (piTyCodeCell
(listElimDependentRecBinderType motive) (listElimDependentConsBranchCodomain motive)))` mentions the motive TWICE
— in the recursive-binder type (the inner Π DOMAIN, `motive tail`) and the cons codomain (the inner Π CODOMAIN,
`motive (cons head tail)`).  So a single `Step.subst` does NOT relate the whole branch type across the motive
step.  Instead the OUTER Π codomain `BIG` takes TWO single congruence steps — one per occurrence, each lifted
through the two Π layers by `Step.cong` over a `StepChildren.here`/`.there` spine — and `piCodeFormedUnder-
CodomainStep` re-forms the outer Π ONCE PER STEP.  Every flag stays the outer Π's inverted flag; no universe-flag
uniqueness, no `substRespectingContext` re-basing. -/
theorem listElimDependentConsBranchType_formedUnderMotiveStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {elementType : RawTerm scope}
    {motive motiveAfter : RawTerm (scope + 1)}
    (formed : UnionClassifierIsType profile context
      (listElimDependentConsBranchType motive elementType))
    (motiveStep : Step motive motiveAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionClassifierIsType profile context
      (listElimDependentConsBranchType motiveAfter elementType) := by
  -- The recursive-binder type and the cons codomain are each a single substitution of the motive, so each steps
  -- singly when the motive steps.
  have recBinderStep : Step (listElimDependentRecBinderType motive)
      (listElimDependentRecBinderType motiveAfter) := by
    unfold listElimDependentRecBinderType; exact Step.subst _ motiveStep
  have consCodomainStep : Step (listElimDependentConsBranchCodomain motive)
      (listElimDependentConsBranchCodomain motiveAfter) := by
    unfold listElimDependentConsBranchCodomain; exact Step.subst _ motiveStep
  -- Step 1: the recursive-binder occurrence (the inner Π's DOMAIN), lifted through both Π layers.
  have outerStepAtRecBinder : Step
      (piTyCodeCell (listTypeCell (RawTerm.weaken elementType))
        (piTyCodeCell (listElimDependentRecBinderType motive)
          (listElimDependentConsBranchCodomain motive)))
      (piTyCodeCell (listTypeCell (RawTerm.weaken elementType))
        (piTyCodeCell (listElimDependentRecBinderType motiveAfter)
          (listElimDependentConsBranchCodomain motive))) :=
    Step.cong .gen_piTyCode () (.there _ (.here _ (Step.cong .gen_piTyCode () (.here _ recBinderStep))))
  -- Step 2: the cons-codomain occurrence (the inner Π's CODOMAIN), lifted through both Π layers.
  have outerStepAtConsCodomain : Step
      (piTyCodeCell (listTypeCell (RawTerm.weaken elementType))
        (piTyCodeCell (listElimDependentRecBinderType motiveAfter)
          (listElimDependentConsBranchCodomain motive)))
      (piTyCodeCell (listTypeCell (RawTerm.weaken elementType))
        (piTyCodeCell (listElimDependentRecBinderType motiveAfter)
          (listElimDependentConsBranchCodomain motiveAfter))) :=
    Step.cong .gen_piTyCode () (.there _ (.here _ (Step.cong .gen_piTyCode () (.there _ (.here _ consCodomainStep)))))
  unfold listElimDependentConsBranchType at formed ⊢
  exact HasTypeUnion.piCodeFormedUnderCodomainStep
    (HasTypeUnion.piCodeFormedUnderCodomainStep formed outerStepAtRecBinder childSubjectReduction)
    outerStepAtConsCodomain childSubjectReduction

end FX1Poly.Typed
