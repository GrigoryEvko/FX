import LeanFX2.Reduction.StepStar

/-! # Reduction/Conv — definitional conversion as ∃-StepStar.

`Conv source target` holds iff there's a common reduct `tMid`
reachable from both via `StepStar`.  This characterization is the
content of the Church-Rosser corollary; defining `Conv` this way
(rather than as inductive with 13 cong rules) collapses the
trans/sym/refl/cong story into a few existential operations and
`StepStar.mapStep` invocations.

## Two-Ty + two-RawTerm

Inherited from `Step` / `StepStar`: source and target Term values
may have different Ty / raw indices.  `Conv` allows them, and the
common reduct's `(tyMid, rawMid)` is also free.

## What lives here

* `Conv` definition (Σ-of-Σ packaged as Prop existential)
* `Conv.refl`, `Conv.sym`
* `Conv.fromStepStar` (single chain ⇒ Conv via target-as-reduct)
* `Conv.fromStep` (single step ⇒ Conv)

## Deferred to Layer 3 (Confluence)

* `Conv.trans` — needs Church-Rosser to merge two triangles into one
* `Conv.canonical_form` — both endpoints reach a shared canonical
  representative (this IS the Church-Rosser corollary applied)

## Cong corollaries via mapStep

For each Term constructor `c`, a cong rule
`Conv.<c>_cong : Conv inputA inputB → Conv (c inputA) (c inputB)`
is a 3-line proof:

```lean
theorem Conv.appLeft_cong (...) (h : Conv funA funB) :
    Conv (Term.app funA arg) (Term.app funB arg) := by
  obtain ⟨_, _, midTerm, chainA, chainB⟩ := h
  exact ⟨_, _, Term.app midTerm arg,
         StepStar.mapStep _ Step.appLeft chainA,
         StepStar.mapStep _ Step.appLeft chainB⟩
```

Layer 3 expands the cong family.  At Phase 3.C, we ship the
core: definition + refl/sym + lift-from-StepStar.
-/

namespace LeanFX2

/-- Definitional conversion: `source` and `target` are convertible
iff they reach a common reduct `midTerm`.  Two-Ty + two-RawTerm
indices on src/tgt + free middle indices match `Step`'s relaxed
shape. -/
def Conv {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw)
    (targetTerm : Term context targetType targetRaw) : Prop :=
  ∃ (midType : Ty level scope) (midRaw : RawTerm scope)
    (midTerm : Term context midType midRaw),
      StepStar sourceTerm midTerm ∧ StepStar targetTerm midTerm

/-- Every Term is convertible to itself: refl. -/
theorem Conv.refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    Conv someTerm someTerm :=
  ⟨someType, someRaw, someTerm, StepStar.refl someTerm, StepStar.refl someTerm⟩

/-- Conv is symmetric: just swap the two convergence chains. -/
theorem Conv.sym
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    Conv targetTerm sourceTerm := by
  obtain ⟨midType, midRaw, midTerm, chainSource, chainTarget⟩ := convertibility
  exact ⟨midType, midRaw, midTerm, chainTarget, chainSource⟩

/-- A `StepStar` chain witnesses convertibility: take the target as
the common reduct.  `targetTerm` is its own reduct (zero steps)
plus we already have a chain from `sourceTerm`. -/
theorem Conv.fromStepStar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    Conv sourceTerm targetTerm :=
  ⟨targetType, targetRaw, targetTerm, chain, StepStar.refl targetTerm⟩

/-- A single `Step` witnesses convertibility. -/
theorem Conv.fromStep
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    Conv sourceTerm targetTerm :=
  Conv.fromStepStar (StepStar.fromStep singleStep)

/-! ## Cast helpers — propositional transport for indices. -/

/-- Replace the source Ty by a propositionally equal Ty. -/
theorem Conv.castSourceType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceTypeOriginal sourceTypeReplacement targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : sourceTypeOriginal = sourceTypeReplacement)
    {sourceTerm : Term context sourceTypeOriginal sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    Conv (typeEquality ▸ sourceTerm) targetTerm := by
  cases typeEquality
  exact convertibility

/-- Replace the target Ty by a propositionally equal Ty. -/
theorem Conv.castTargetType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetTypeOriginal targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    Conv sourceTerm (typeEquality ▸ targetTerm) := by
  cases typeEquality
  exact convertibility

/-- Replace the source Term by a propositionally equal Term. -/
theorem Conv.castSourceTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceOriginal sourceReplacement : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (sourceEquality : sourceOriginal = sourceReplacement)
    (convertibility : Conv sourceOriginal targetTerm) :
    Conv sourceReplacement targetTerm := by
  cases sourceEquality
  exact convertibility

/-- Replace the target Term by a propositionally equal Term. -/
theorem Conv.castTargetTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal targetReplacement : Term context targetType targetRaw}
    (targetEquality : targetOriginal = targetReplacement)
    (convertibility : Conv sourceTerm targetOriginal) :
    Conv sourceTerm targetReplacement := by
  cases targetEquality
  exact convertibility

end LeanFX2
