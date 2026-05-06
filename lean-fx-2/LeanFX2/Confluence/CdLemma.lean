import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.RawDiamond

/-! # Confluence/CdLemma — every parallel reduct lands in cd t (raw projection)

The headline raw lemma `RawStep.par.cd_lemma` already ships fully
zero-axiom in `Confluence/RawCdLemma.lean`:

```lean
RawStep.par.cd_lemma : RawStep.par t t' → RawStep.par t' (RawTerm.cd t)
```

This file lifts the cd-lemma to the typed level in the only way
the architecture admits without subject reduction: as a statement
about the raw projections of typed terms.

## Why no `Step.par.cd_lemma : Step.par t t' → Step.par t' (Term.cd t)`?

The classical typed cd-lemma needs a typed `Term.cd` with type
`Term ctx tipe raw → Term ctx tipe' raw'`.  As `Cd.lean`'s
docstring explains, defining such a function requires subject
reduction for `Step.par` (β/ι rules change the type along the
reduction; the typed Term.cd would need to absorb the casts).
Subject reduction is M05/M06 work — Phase 7.

Until SR ships, the strongest typed cd-lemma is the raw-output
form below: any typed parallel reduction projects (via
`Step.par.toRawBridge`) to a raw parallel reduction whose target
parallel-reduces to `RawTerm.cd source.toRaw` via the raw cd-lemma.

## What this file ships (zero axioms)

* `Step.par.cdLemmaRaw` — given typed `Step.par sourceTerm
  targetTerm`, the target's raw projection parallel-reduces (in
  one raw step) to `RawTerm.cd sourceRaw`.

* `Step.par.cdDominatesRaw` — typed `Step.par.refl sourceTerm`
  parallel-reduces to `RawTerm.cd sourceRaw` (the cd-domination
  property at the typed level via raw projection).

## Diff from lean-fx

In lean-fx, the typed cd-lemma was W8.3 — the "cd_monotone
aggregator" — proved across 13 sub-tasks (W8.3a through W8.3i)
totaling ~3000 lines using paired-predicate machinery
(`parStarWithBi`).  The mechanism existed because lean-fx's Term
projected to RawTerm via a recursive function and substitutions
needed HEq cascade lemmas (`subst0_term_subst_HEq` and friends).

lean-fx-2's raw-aware Term collapses those HEq cascades to `rfl`,
making the **raw-output** typed cd-lemma a one-liner.  The
**typed-output** version is delayed until subject reduction
(Phase 7); it doesn't need the paired-predicate workaround
either, so when SR lands the typed cd-lemma will also collapse
to a small proof.

## Dependencies

* `Confluence/Cd.lean`
* `Confluence/RawCdLemma.lean` — `RawStep.par.cd_lemma`
* `Bridge.lean` — `Step.par.toRawBridge`

## Downstream consumers

* `Confluence/Diamond.lean` — diamond at typed inputs
* `Confluence/ChurchRosser.lean` — multi-step confluence
-/

namespace LeanFX2

/-- **Typed-input, raw-output cd-lemma.**  Given a typed parallel
reduction step `Step.par sourceTerm targetTerm`, the target's raw
projection parallel-reduces (in one raw step) to
`RawTerm.cd sourceRaw`.

Composition: typed step → raw step (via `Step.par.toRawBridge`) →
raw cd-lemma applied to the raw step. -/
theorem Step.par.cdLemmaRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    RawStep.par targetRaw (RawTerm.cd sourceRaw) :=
  RawStep.par.cd_lemma (Step.par.toRawBridge parallelStep)

/-- **cd-domination at typed inputs.**  Every typed Term's raw
projection parallel-reduces to its complete development.
Specialization of `Step.par.cdLemmaRaw` to the refl case:
`Step.par.refl someTerm` projects to `RawStep.par someRaw someRaw`,
which then steps to `RawTerm.cd someRaw` via the cd-lemma. -/
theorem Step.par.cdDominatesRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    RawStep.par someRaw (RawTerm.cd someRaw) :=
  Step.par.cdLemmaRaw (Step.par.refl someTerm)

/-- **Diamond witness at the typed level via raw projection.**
For any typed Term, both refl-self-reductions land at the same
raw common reduct (namely `RawTerm.cd someRaw`).  This is the
trivial form of diamond — Step.par.refl is closed under cd. -/
theorem Step.par.cdLemmaRaw_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    RawStep.par someRaw (RawTerm.cd someRaw) ∧
    RawStep.par someRaw (RawTerm.cd someRaw) :=
  ⟨Step.par.cdDominatesRaw someTerm, Step.par.cdDominatesRaw someTerm⟩

/-- **Multi-step cd-domination at typed inputs via raw projection.**
A typed `Step.parStar` chain has its target's raw projection
multi-step parallel-reducing to a `RawTerm.cd` cascade applied
to the source.  This is the multi-step lift of `cdDominatesRaw`,
useful for normalization-strategy proofs at Layer 9. -/
theorem Step.parStar.cdDominatesRawSingle
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    RawStep.parStar someRaw (RawTerm.cd someRaw) :=
  RawStep.par.toStar (Step.par.cdDominatesRaw someTerm)

end LeanFX2
