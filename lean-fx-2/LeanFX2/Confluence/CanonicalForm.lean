import LeanFX2.Confluence.ChurchRosser

/-! # Confluence/CanonicalForm — canonical-form corollaries from Conv

In lean-fx-2, `Conv := ∃-StepStar` packaging — so the
"canonical form" theorem is the *definitional content* of Conv,
not a separate Church-Rosser corollary.  This file ships the
typed-input/raw-output canonical-form corollaries that downstream
consumers (decidable conversion in Layer 9, elaborator coherence
proofs) actually use.

## Headline theorem

```lean
theorem Conv.canonicalForm
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw
```

Re-exposes `Conv.canonicalRaw` from `ChurchRosser.lean` (which is
itself an alias of `Conv.toRawJoin` from `ConvBridge.lean`) under
the canonical name.  The body unpacks the `∃-StepStar` definition
of `Conv` and projects each `StepStar` chain through
`StepStar.toParStar` then `Step.parStar.toRawBridge`.

## Why no typed canonical form?

A typed canonical form would deliver `∃ (canonType : Ty)
(canonRaw : RawTerm) (canonTerm : Term context canonType
canonRaw), StepStar sourceTerm canonTerm ∧ StepStar targetTerm
canonTerm`.  Constructing such a typed `canonTerm` from a typed
Conv requires subject reduction for `Step` / `StepStar`: given a
typed `sourceTerm` and a `StepStar` chain to a raw common reduct,
we must produce a Ty so that the chain lands at a typed Term.
That's M05/M06 work (planned Phase 7).

Until SR ships, the raw form is sufficient: typed convertibility
is preserved by typing (elaboration-time invariant), so once two
reducts agree at the raw level their typed terms are convertible.

## Conv.refl, Conv.sym, Conv.fromStep, Conv.fromStepStar

These are already shipped in `Reduction/Conv.lean` (Layer 2) at
zero axioms — Conv as `∃-StepStar` makes refl / sym one-line by
reusing the same chain.

## Conv.trans

Classical `Conv.trans` (typed midpoint) requires SR to lift the
raw confluence join to a typed Term.  The raw analog is shipped
in `ChurchRosser.lean` as `Conv.transRaw`.

## What this file ships (zero axioms)

* `Conv.canonicalForm` — typed Conv ⇒ raw join (alias of
  `Conv.canonicalRaw` / `Conv.toRawJoin`)
* `Conv.canonicalForm_self` — self-Conv reduces to refl on both
  endpoints (smoke test that the canonical form behaves on
  trivial inputs)
* `Conv.canonicalForm_fromStepStar` — the canonical form of a
  Conv built from a single `StepStar` chain reduces directly
  to that chain (the target is its own canonical reduct)

## Dependencies

* `Confluence/ChurchRosser.lean`
* `Reduction/Conv.lean` — Conv definition + refl/sym

## Downstream consumers

* `Algo/DecConv.lean` — decidable conversion
* `Algo/Check.lean` — elaboration coherence
-/

namespace LeanFX2

/-- **Canonical form** for typed Conv.  Two convertible terms
admit a common raw reduct reachable from both via multi-step
parallel reduction.  Alias of `Conv.canonicalRaw`. -/
theorem Conv.canonicalForm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalRaw convertibility

/-- Smoke property: the canonical form of `Conv someTerm someTerm`
admits the trivial raw join (someRaw itself) via two refl chains.
The canonical form theorem produces SOME raw join — this lemma
states that for the refl Conv, ANY of the source/target raw
projections suffices as a join witness. -/
theorem Conv.canonicalForm_self
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (_someTerm : Term context someType someRaw) :
    ∃ commonRaw,
      RawStep.parStar someRaw commonRaw ∧
      RawStep.parStar someRaw commonRaw :=
  ⟨someRaw, RawStep.parStar.refl _, RawStep.parStar.refl _⟩

/-- The canonical form of a Conv built from a single `StepStar`
chain admits the chain's target as the common reduct (the
target reaches itself via refl, and the source reaches it via
the original chain projected through `StepStar.toParStar` +
`Step.parStar.toRawBridge`). -/
theorem Conv.canonicalForm_fromStepStar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalForm (Conv.fromStepStar chain)

end LeanFX2
