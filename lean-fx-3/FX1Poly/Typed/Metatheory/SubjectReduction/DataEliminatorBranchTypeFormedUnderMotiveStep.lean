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

## The generic keystone: type-formedness preserved under a step

The branch-classifier drift is, at bottom, ONE fact: a well-formed type that steps stays a well-formed type
(type-level subject reduction at the universe).  `UnionClassifierIsType.preservedUnderStep` proves it directly —
the formedness witness IS a `classifier : universeCode level flag` derivation, the single-step-SR self-reference
re-types the stepped classifier, and universe rigidity reclassifies it back to the same universe code.  No
inversion, no flag coordination — the per-eliminator arms below only have to BUILD the step relating the pre- and
post-motive branch classifiers and hand it to this keystone.

`optionMatch`'s some branch and `eitherMatch`'s inl / inr branches are each `piTyCodeCell domain (codomain motive)`
with the motive in the codomain, so the step is `Step.cong gen_piTyCode` over the codomain's `Step.subst`; the thin
`HasTypeUnion.piCodeFormedUnderCodomainStep` corollary packages that lift.  `listElim`'s cons branch nests THREE
`piTyCode`s with the motive occurring TWICE — at `motive tail` and at `motive (cons head tail)` — so its whole-cell
step is TWO `Step.cong`-lifted occurrences and `preservedUnderStep` re-forms once per step.  An idJ-diagonal
classifier `idJMotiveAt motive endpoint witness` is a bare motive substitution (no `piTyCode` wrapper), so its step
is a single `Step.subst` handed straight to `preservedUnderStep`.

## Zero-axiom verification

`HasTypeUnion.reclassifyToType` over `universeFormation` (universe rigidity) + `Step.cong` / `Step.subst` (the
term-axis congruence / substitution-stability of one-step reduction).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-- **★ Type-formedness is preserved under one reduction step (type-level subject reduction at the universe).**
A well-formed union type `classifier` that steps `classifier ⟶ classifierAfter` stays a well-formed type.  The
formedness witness IS a union-typed derivation `classifier : universeCode level flag`, so the single-step-SR
self-reference re-types the stepped `classifierAfter` at a `Conv`-equal classifier, which universe rigidity
(`reclassifyToType` over `universeFormation`) reclassifies back to the SAME `universeCode level flag`.  This is the
ONE keystone every dependent-eliminator branch classifier reclassifies its branch through when the motive (hence
the branch classifier) steps — `piTyCode`-wrapped or not, single- or multi-occurrence, idJ-diagonal or not.  No
inversion, no flag coordination, no universe-flag uniqueness, no descriptor flag-hardening. -/
theorem UnionClassifierIsType.preservedUnderStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier classifierAfter : RawTerm scope}
    (formed : UnionClassifierIsType profile context classifier)
    (step : Step classifier classifierAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionClassifierIsType profile context classifierAfter := by
  obtain ⟨level, flag, classifierTyped⟩ := formed
  obtain ⟨classifierAfterType, classifierAfterTyped, classifierConv⟩ :=
    childSubjectReduction classifierTyped step
  exact ⟨level, flag, HasTypeUnion.reclassifyToType classifierAfterTyped classifierConv.sym
    ⟨_, _, HasTypeUnion.universeFormation context level flag⟩⟩

/-- **Type-formedness is preserved along a whole reduction CHAIN.**  Iterating `preservedUnderStep` along a
`StepStar classifier classifierAfter`: each head step transfers formedness one term forward, the tail chain
carries the rest.  This is the multi-step lifter the multi-occurrence branch classifiers need — when one motive
step induces several reduction steps in a branch type (each motive occurrence steps once), the chain re-forms the
classifier across all of them in one call. -/
theorem UnionClassifierIsType.preservedUnderStepStar {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier classifierAfter : RawTerm scope}
    (formed : UnionClassifierIsType profile context classifier)
    (steps : StepStar classifier classifierAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionClassifierIsType profile context classifierAfter := by
  revert formed
  induction steps with
  | refl _ => exact id
  | trans headStep _ tailPreserves =>
      exact fun formedFirst =>
        tailPreserves (UnionClassifierIsType.preservedUnderStep formedFirst headStep childSubjectReduction)

/-- **A Π code stays a well-formed type when its codomain steps.**  The codomain step lifts to a whole-cell step
through the `gen_piTyCode` children spine (`Step.cong` over a `there`/`here` walk to the codomain position), and
`preservedUnderStep` re-forms the Π code.  The `piTyCode`-wrapped dependent branch classifiers
(`optionMatch` / `eitherMatch` / `listElim` branches) reclassify their branch through this when the motive
steps. -/
theorem HasTypeUnion.piCodeFormedUnderCodomainStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {domain : RawTerm scope}
    {codomain codomainAfter : RawTerm (scope + 1)}
    (formed : UnionClassifierIsType profile context (piTyCodeCell domain codomain))
    (codomainStep : Step codomain codomainAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionClassifierIsType profile context (piTyCodeCell domain codomainAfter) :=
  UnionClassifierIsType.preservedUnderStep formed
    (Step.cong .gen_piTyCode () (.there _ (.here _ codomainStep))) childSubjectReduction

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
