import LeanFX2.Confluence.ConvBridge

/-! # Confluence/ChurchRosser — multi-step Church-Rosser corollaries

Multi-step confluence at the raw level (`RawStep.parStar.confluence`,
shipped in `Confluence/RawDiamond.lean`) lifts to typed corollaries
via the typed→raw bridge `Step.parStar.toRawBridge`.

## Typed-input, raw-output Church-Rosser

```lean
theorem Step.parStar.churchRosserRaw
    {sourceTerm leftTarget rightTarget : ...}
    (leftChain : Step.parStar sourceTerm leftTarget)
    (rightChain : Step.parStar sourceTerm rightTarget) :
    ∃ commonRaw,
      RawStep.parStar leftRaw commonRaw ∧
      RawStep.parStar rightRaw commonRaw
```

The proof projects each typed chain to a raw chain via
`Step.parStar.toRawBridge`, then applies
`RawStep.parStar.confluence`.  This headline corollary already
ships in `ParStarBridge.lean` as `Step.parStar.toRawConfluence` —
this file re-exposes it under the canonical Church-Rosser name and
adds a `StepStar` variant that goes through `StepStar.toParStar`.

## StepStar variant

`StepStar` is the RT closure of single-step `Step`; `Step.parStar`
is the RT closure of `Step.par`.  Every `Step` is a `Step.par`
(via `Step.toPar`), so `StepStar` chains lift to `Step.parStar`
chains via `StepStar.toParStar`.  Multi-step confluence on
`StepStar` is therefore a one-line corollary of
`Step.parStar.churchRosserRaw`.

## Why not a typed-output Church-Rosser?

Same reason as `Diamond.lean`: lifting the raw common reduct back
to a typed `Term context commonType commonRaw` requires subject
reduction for `Step.par` (and hence for `StepStar` via the
embedding).  Subject reduction is M05/M06 work (Phase 7).  Until
then, the raw form is the strongest typed-input join shippable.

`Algo/DecConv.lean` and the elaborator's coherence proofs consume
the raw join: typed convertibility is preserved by typing
(elaboration-time invariant), so once two reducts agree at the
raw level, their typed terms are convertible by construction.

## What this file ships (zero axioms)

* `Step.parStar.churchRosserRaw` — typed inputs, raw common reduct,
  multi-step parallel reduction (alias of
  `Step.parStar.toRawConfluence` from `ParStarBridge.lean`)
* `StepStar.churchRosserRaw` — typed inputs, raw common reduct,
  multi-step `Step` via `StepStar.toParStar` lift
* `Conv.canonicalRaw` — definitional content of `Conv` as raw
  join (alias of `Conv.toRawJoin` from `ConvBridge.lean`)
* `Conv.transRaw` — typed Conv composition expressed at raw level

## Conv.trans — partial ship; full version blocks on strong SR

The classical `Conv.trans` requires a typed common reduct from
two typed convergence triangles: given `Conv s t` and `Conv t u`,
need a typed midpoint reachable from both `s` and `u`.  This
needs subject reduction to lift the raw confluence join back to
a typed Term.

* **Chain-composition fragment** (`Conv.transChains` /
  `Conv.trans_via_chains`, see `Confluence/ConvTrans.lean`) is
  shipped at zero axioms — covers the case where both Conv
  witnesses arrive as explicit `StepStar` chains.
* **Full unrestricted version** (where each Conv brings its own
  midpoint) remains blocked on strong subject reduction (term
  construction via raw-step inversion at typed sources).  M06/M07
  ship the type-EQUALITY part of SR but not term construction.

For the elaborator's decidable conversion needs, the raw analog
`Conv.transRaw` (in this file) is sufficient: typed convertibility
is preserved by typing (elaboration-time invariant), so once two
reducts agree at the raw level their typed terms are convertible.

## Dependencies

* `Confluence/ParStarBridge.lean` — `Step.parStar.toRawConfluence`
* `Confluence/ConvBridge.lean` — `Conv.toRawJoin`
* `Reduction/StepStarToPar.lean` — `StepStar.toParStar`

## Downstream consumers

* `Confluence/CanonicalForm.lean` — canonical form via Conv
* `Algo/DecConv.lean` — decidable conversion
-/

namespace LeanFX2

/-- **Typed-input, raw-output Church-Rosser** for parallel reduction.
Two typed multi-step parallel chains from a common source produce
raw projections that converge to a common raw reduct.

Alias of `Step.parStar.toRawConfluence` (which lives in
`ParStarBridge.lean`).  Re-exported here under the canonical
Church-Rosser name so downstream consumers reach for it through
the confluence module hierarchy.

Lifting the raw common reduct to a typed Term requires subject
reduction (Phase 7); see file docstring. -/
theorem Step.parStar.churchRosserRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType leftType rightType : Ty level scope}
    {sourceRaw leftRaw rightRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {leftTarget : Term context leftType leftRaw}
    {rightTarget : Term context rightType rightRaw}
    (leftChain : Step.parStar sourceTerm leftTarget)
    (rightChain : Step.parStar sourceTerm rightTarget) :
    ∃ commonRaw,
      RawStep.parStar leftRaw commonRaw ∧
      RawStep.parStar rightRaw commonRaw :=
  Step.parStar.toRawConfluence leftChain rightChain

/-- **Typed-input, raw-output Church-Rosser** for `StepStar` (RT
closure of single-step `Step`).  Lifts each `StepStar` chain to a
`Step.parStar` chain via `StepStar.toParStar`, then applies
`Step.parStar.churchRosserRaw`. -/
theorem StepStar.churchRosserRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType leftType rightType : Ty level scope}
    {sourceRaw leftRaw rightRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {leftTarget : Term context leftType leftRaw}
    {rightTarget : Term context rightType rightRaw}
    (leftChain : StepStar sourceTerm leftTarget)
    (rightChain : StepStar sourceTerm rightTarget) :
    ∃ commonRaw,
      RawStep.parStar leftRaw commonRaw ∧
      RawStep.parStar rightRaw commonRaw :=
  Step.parStar.churchRosserRaw leftChain.toParStar rightChain.toParStar

/-- **Typed Conv as raw join** — alias of `Conv.toRawJoin`.

A typed convertibility witness IS a raw join (definitionally),
since `Conv := ∃-StepStar` and the typed midpoint's raw projection
is reachable from both endpoints' raw projections via
`StepStar.toParStar` + `Step.parStar.toRawBridge`.  This is the
content of "canonical form" in lean-fx-2's design: Conv unpacks
to a raw join. -/
theorem Conv.canonicalRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.toRawJoin convertibility

/-- Raw join from `Conv.refl`.  Both chains are reflexive `parStar`.

Pure delegation through `Conv.canonicalRaw ∘ Conv.refl`.  Useful when
downstream consumers want an explicit raw join witness without first
constructing a `Conv` value at the call site. -/
theorem Conv.reflRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ∃ commonRaw,
      RawStep.parStar someRaw commonRaw ∧
      RawStep.parStar someRaw commonRaw :=
  Conv.canonicalRaw (Conv.refl someTerm)

/-- Raw join with source/target chains swapped — raw projection of
`Conv.sym`.

Pure delegation through `Conv.canonicalRaw ∘ Conv.sym`.  Useful when
the downstream consumer expects the target-side `parStar` chain first
(e.g., backward-chaining proof strategies, NbE bridges that read off
the target endpoint). -/
theorem Conv.symRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar targetRaw commonRaw ∧
      RawStep.parStar sourceRaw commonRaw :=
  Conv.canonicalRaw (Conv.sym convertibility)

/-- **Raw-level transitivity** for typed Conv.  Given two typed
Conv triangles meeting at `middleTerm`, produce a raw common
reduct reachable from both `sourceRaw` and `farRaw`.

Pipeline:
1. Project each Conv to a raw join via `Conv.canonicalRaw`.
2. The middle endpoint's raw projection is the common point of
   the two raw joins.
3. Apply `RawStep.parStar.confluence` at the middle to combine
   the two raw triangles into a single raw join over
   `sourceRaw`/`farRaw`.

A typed `Conv.trans` would lift this raw join to a typed common
reduct via subject reduction; that step deferred to Phase 7. -/
theorem Conv.transRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType farType : Ty level scope}
    {sourceRaw middleRaw farRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (firstConvertibility : Conv sourceTerm middleTerm)
    (secondConvertibility : Conv middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar farRaw commonRaw := by
  obtain ⟨firstJoinRaw, sourceToFirstJoin, middleToFirstJoin⟩ :=
    Conv.canonicalRaw firstConvertibility
  obtain ⟨secondJoinRaw, middleToSecondJoin, farToSecondJoin⟩ :=
    Conv.canonicalRaw secondConvertibility
  obtain ⟨commonReduct, firstJoinToCommon, secondJoinToCommon⟩ :=
    RawStep.parStar.confluence middleToFirstJoin middleToSecondJoin
  exact ⟨commonReduct,
    RawStep.parStar.append sourceToFirstJoin firstJoinToCommon,
    RawStep.parStar.append farToSecondJoin secondJoinToCommon⟩

/-- **Raw-level rename equivariance** for typed Conv (T6 forward direction,
raw output flavor).

Given a typed `Conv sourceTerm targetTerm` and a raw renaming `rho`, the raw
projections of source and target — under `rho` — still admit a common raw
reduct.  Pipeline:

1. Project the typed Conv to a raw join via `Conv.canonicalRaw`.
2. Apply `RawStep.parStar.rename_compatible` to each chain so both sides land
   at `joinRaw.rename rho`.
3. Package the result as the new raw join.

This is the analog of `Conv.transRaw` but for renaming instead of
transitivity.  A full typed `Conv (Term.rename ...) (Term.rename ...)` lift
requires either:

* context-changing `StepStar.mapStep` infrastructure (single-step typed Step
  rename equivariance per ctor, ~75 cases), or
* subject reduction to lift the raw join back to a typed common reduct.

Both are Phase 7 work.  Until then, the raw form is what consumers actually
need: typed convertibility under renaming is preserved by typing
(elaboration-time invariant), so once renamed source and target raws agree
at the raw level their typed renamings are convertible by construction. -/
theorem Conv.renameRaw
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  exact ⟨joinRaw.rename rawRenaming,
    RawStep.parStar.rename_compatible rawRenaming sourceToJoin,
    RawStep.parStar.rename_compatible rawRenaming targetToJoin⟩

/-- Canonical-weaken specialization of `Conv.renameRaw`.

A typed Conv lifts to a raw join at the weaken image of source / target.
The result matches the surface form `sourceRaw.weaken` / `targetRaw.weaken`
that downstream β-redex consumers (Phase G β-η critical pair, K13 NbE
under canonical-weaken) reach for most often.

`RawTerm.weaken` definitionally unfolds to `RawTerm.rename RawRenaming.weaken`
so the proof is a direct call to `Conv.renameRaw`. -/
theorem Conv.weakenRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.renameRaw RawRenaming.weaken convertibility

/-- Subst-axis analog of `Conv.renameRaw`: typed Conv lifts to a raw
join at the substitution image of source / target.

Composes `Conv.canonicalRaw` (typed Conv → raw join) with
`RawStep.parStar.subst_compatible_same` (raw multi-step subst
preservation, shipped in `RawParWeakenInv/ParStar.lean`).  The join
midpoint is the same raw term substituted by `rawSubst`. -/
theorem Conv.substRaw
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  exact ⟨joinRaw.subst rawSubst,
    RawStep.parStar.subst_compatible_same rawSubst sourceToJoin,
    RawStep.parStar.subst_compatible_same rawSubst targetToJoin⟩

/-- Singleton-substitution specialization of `Conv.substRaw`.

A typed Conv lifts to a raw join at the singleton-β-substitution image
of source / target.  Surface form `sourceRaw.subst0 argRaw` is what
β-redex consumers (Phase G β-η critical pair, K12.28 Geuvers 1992
lift) reach for at call sites.  `RawTerm.subst0 body arg` is
`@[reducible]` defined as `body.subst (RawTermSubst.singleton arg)`
(`Foundation/RawSubst/SubstDefs.lean:200`), so the proof is a direct
call to `Conv.substRaw`. -/
theorem Conv.subst0Raw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.substRaw (RawTermSubst.singleton argRaw) convertibility

/-! ## Trans-plus-action composition lifters

The four `Conv.transRaw_*` corollaries below compose `Conv.transRaw`
with each of the four canonical raw actions (rename / weaken / subst /
subst0) in a single ship.  Each is the natural shape downstream K12.28
β-η critical pair and K13 NbE β step consumers reach for: a chain of
two typed Convs (t1 ~ t2, t2 ~ t3) lifted to a raw join under an
action.

Pipeline: pull the raw join out of `Conv.transRaw` (which extracts
two raw joins via `canonicalRaw`, then patches them via raw
confluence), then propagate both arms through the action via the
matching raw multi-step compatibility theorem
(`rename_compatible` / `subst_compatible_same`). -/

/-- Combine `Conv.transRaw` with a raw renaming in one ship.  Useful
when chaining two typed Convs and then needing the raw join at a
renamed surface form (e.g. lifting a Conv chain through a renaming
inside a cd cascade arm). -/
theorem Conv.transRaw_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstConvertibility : Conv sourceTerm middleTerm)
    (secondConvertibility : Conv middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (farRaw.rename rawRenaming) commonRaw := by
  obtain ⟨joinRaw, sourceToJoin, farToJoin⟩ :=
    Conv.transRaw firstConvertibility secondConvertibility
  exact ⟨joinRaw.rename rawRenaming,
    RawStep.parStar.rename_compatible rawRenaming sourceToJoin,
    RawStep.parStar.rename_compatible rawRenaming farToJoin⟩

/-- Canonical-weaken specialization of `Conv.transRaw_renamed`. -/
theorem Conv.transRaw_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType middleType farType : Ty level scope}
    {sourceRaw middleRaw farRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (firstConvertibility : Conv sourceTerm middleTerm)
    (secondConvertibility : Conv middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar farRaw.weaken commonRaw :=
  Conv.transRaw_renamed RawRenaming.weaken
    firstConvertibility secondConvertibility

/-- Combine `Conv.transRaw` with a raw substitution in one ship. -/
theorem Conv.transRaw_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (firstConvertibility : Conv sourceTerm middleTerm)
    (secondConvertibility : Conv middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (farRaw.subst rawSubst) commonRaw := by
  obtain ⟨joinRaw, sourceToJoin, farToJoin⟩ :=
    Conv.transRaw firstConvertibility secondConvertibility
  exact ⟨joinRaw.subst rawSubst,
    RawStep.parStar.subst_compatible_same rawSubst sourceToJoin,
    RawStep.parStar.subst_compatible_same rawSubst farToJoin⟩

/-- Singleton-substitution specialization of `Conv.transRaw_substituted`.
Matches the β-redex surface form `body.subst0 arg` that K12.28
Geuvers 1992 β-η critical pair joinability consumers reach for. -/
theorem Conv.transRaw_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType middleType farType : Ty level (scope + 1)}
    {sourceRaw middleRaw farRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (argRaw : RawTerm scope)
    (firstConvertibility : Conv sourceTerm middleTerm)
    (secondConvertibility : Conv middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (farRaw.subst0 argRaw) commonRaw :=
  Conv.transRaw_substituted (RawTermSubst.singleton argRaw)
    firstConvertibility secondConvertibility

/-- Multi-position parallel-substitution sibling of
`Conv.transRaw_substituted`.

Combines two-Conv transitivity with the heterogeneous parallel-subst
lift `RawStep.parStar.subst_par`: given two raw substitutions
`firstSubst` / `secondSubst` related single-step pointwise, the
trans-composed Conv lifts to a raw join at differently-substituted
endpoints `sourceRaw.subst firstSubst` and `farRaw.subst secondSubst`.

Strategy:
1. Compose the two Convs via `Conv.transRaw` to a common joinRaw.
2. Source half: `RawStep.parStar.subst_par` lifts source-chain through
   the pointwise-related substs; lands at `joinRaw.subst secondSubst`.
3. Far half: `RawStep.parStar.subst_compatible_same secondSubst` pins
   far-chain at secondSubst; also lands at `joinRaw.subst secondSubst`.

Mirrors the family pattern of `transRaw_<action>` (renamed / weakened
/ substituted / subst0) with the new parallel-subst action.  K12.28
Geuvers β-η critical-pair joinability and K13 NbE β-step under
parallel substitution chains reach for this shape when a chain of
typed Convs must fuse with substitution-evolution. -/
theorem Conv.transRaw_subst_par
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    (firstConvertibility : Conv sourceTerm middleTerm)
    (secondConvertibility : Conv middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst firstSubst) commonRaw ∧
      RawStep.parStar (farRaw.subst secondSubst) commonRaw := by
  obtain ⟨joinRaw, sourceToJoin, farToJoin⟩ :=
    Conv.transRaw firstConvertibility secondConvertibility
  exact ⟨joinRaw.subst secondSubst,
    RawStep.parStar.subst_par substsRelated sourceToJoin,
    RawStep.parStar.subst_compatible_same secondSubst farToJoin⟩

/-! ## StepStar-chain-plus-action lifters

When a downstream consumer has a typed one-sided `StepStar` chain
instead of a two-sided `Conv`, the four corollaries below skip the
explicit `Conv.fromStepStar` wrapping step.  Composes
`Conv.fromStepStar` (chain → Conv, target as common reduct) with
each of the four single-action raw lifters (renameRaw / weakenRaw /
substRaw / subst0Raw).

Pipeline: `Conv.<action>Raw <action-arg> (Conv.fromStepStar chain)`.
The midpoint of the resulting raw join is the target endpoint of
the chain, transported through the action.  Useful for Phase 7 SR
chain consumers and K13 NbE β-step consumers that have a single
typed reduction direction. -/

/-- Combine a typed StepStar chain with a raw renaming in one ship. -/
theorem Conv.fromStepStar_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (chain : StepStar sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.fromStepStar chain)

/-- Canonical-weaken specialization of `Conv.fromStepStar_renamed`. -/
theorem Conv.fromStepStar_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.fromStepStar chain)

/-- Combine a typed StepStar chain with a raw substitution in one ship. -/
theorem Conv.fromStepStar_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (chain : StepStar sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.fromStepStar chain)

/-- Singleton-substitution specialization of
`Conv.fromStepStar_substituted`. -/
theorem Conv.fromStepStar_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (chain : StepStar sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.fromStepStar chain)

/-- Multi-position parallel-substitution sibling of
`Conv.fromStepStar_substituted`.

Combines a typed `StepStar` chain with the heterogeneous parallel-subst
action `Conv.rawSubst_par_toRawJoin`: given two raw substitutions
`firstSubst` / `secondSubst` related single-step pointwise, the typed
chain (wrapped as a Conv) lifts to a raw join at differently-substituted
endpoints `sourceRaw.subst firstSubst` and `targetRaw.subst secondSubst`.

Pure delegation: `Conv.rawSubst_par_toRawJoin` after `Conv.fromStepStar`.
Mirrors the `_renamed / _weakened / _substituted / _subst0` family
pattern for parallel-subst chain consumers. -/
theorem Conv.fromStepStar_subst_par
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    (chain : StepStar sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst firstSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst secondSubst) commonRaw :=
  Conv.rawSubst_par_toRawJoin substsRelated (Conv.fromStepStar chain)

/-! ## Single-Step-plus-action lifters

When a downstream consumer has just a single typed `Step t1 t2`
(not yet a chain or a Conv), the four corollaries below skip the
`Conv.fromStep` wrapping step.  Composes `Conv.fromStep` (Step →
Conv via StepStar.fromStep) with each of the four single-action raw
lifters.

These are the natural shape for K12.28 Geuvers 1992 β-η critical
pair consumers when a single β step or η step is the input and the
result must be lifted through an action.  Completes the symmetric
4×4 lift table (single-Conv, trans-Conv, chain-StepStar,
single-Step rows × four actions). -/

/-- Combine a single typed Step with a raw renaming in one ship. -/
theorem Conv.fromStep_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (singleStep : Step sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.fromStep singleStep)

/-- Canonical-weaken specialization of `Conv.fromStep_renamed`. -/
theorem Conv.fromStep_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.fromStep singleStep)

/-- Combine a single typed Step with a raw substitution in one ship. -/
theorem Conv.fromStep_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (singleStep : Step sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.fromStep singleStep)

/-- Singleton-substitution specialization of `Conv.fromStep_substituted`.
Matches the β-redex surface form `body.subst0 arg` consumers reach
for in K12.28 (β-η critical pair joinability) and K13 NbE β step. -/
theorem Conv.fromStep_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (singleStep : Step sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.fromStep singleStep)

/-- Multi-position parallel-substitution sibling of
`Conv.fromStep_substituted`.

Combines a single typed `Step` with the parallel-subst action
`Conv.rawSubst_par_toRawJoin` via `Conv.fromStep`.  Same family
pattern as the `fromStepStar_subst_par` sibling but at single-step
granularity.  Useful when a single β-step or η-step plus a pointwise-
related substitution pair is the input shape.  -/
theorem Conv.fromStep_subst_par
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    (singleStep : Step sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst firstSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst secondSubst) commonRaw :=
  Conv.rawSubst_par_toRawJoin substsRelated (Conv.fromStep singleStep)

/-! ## Reverse-direction chain / step lifters

`Conv.fromStepStar` builds `Conv source target` from a forward chain
`source →* target`.  Downstream consumers sometimes have the chain
in the *reverse* direction (`target →* source`) — e.g., when a typed
reduction was discovered from a normal form back to a redex.  The
canonical fix is `Conv.sym ∘ Conv.fromStepStar`.

These five reverse-direction wrappers ship that composition under the
canonical name `Conv.fromStepStarReverse`, plus the matching raw-action
variants.  Each is one line, no induction, no confluence. -/

/-- A *reverse* `StepStar` chain `target →* source` witnesses
convertibility of `source` and `target`.  Just `Conv.sym` of
`Conv.fromStepStar` applied to the reverse chain. -/
theorem Conv.fromStepStarReverse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (reverseChain : StepStar targetTerm sourceTerm) :
    Conv sourceTerm targetTerm :=
  Conv.sym (Conv.fromStepStar reverseChain)

/-- Raw-rename projection of `Conv.fromStepStarReverse`. -/
theorem Conv.fromStepStarReverse_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (reverseChain : StepStar targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.fromStepStarReverse reverseChain)

/-- Canonical-weaken specialization of `Conv.fromStepStarReverse_renamed`. -/
theorem Conv.fromStepStarReverse_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (reverseChain : StepStar targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.fromStepStarReverse reverseChain)

/-- Raw-subst projection of `Conv.fromStepStarReverse`. -/
theorem Conv.fromStepStarReverse_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (reverseChain : StepStar targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.fromStepStarReverse reverseChain)

/-- Singleton-substitution specialization of
`Conv.fromStepStarReverse_substituted`. -/
theorem Conv.fromStepStarReverse_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (reverseChain : StepStar targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.fromStepStarReverse reverseChain)

/-- Multi-position parallel-substitution sibling of
`Conv.fromStepStarReverse_substituted`.

A reverse `StepStar` chain plus pointwise-related substitutions lifts
to a raw join at the differently-substituted endpoints.  Pure
delegation: `Conv.rawSubst_par_toRawJoin` after `Conv.fromStepStarReverse`. -/
theorem Conv.fromStepStarReverse_subst_par
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    (reverseChain : StepStar targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst firstSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst secondSubst) commonRaw :=
  Conv.rawSubst_par_toRawJoin substsRelated
    (Conv.fromStepStarReverse reverseChain)

/-- Single-step reverse variant: a `Step target source` witnesses
convertibility of `source` and `target`. -/
theorem Conv.fromStepReverse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (reverseStep : Step targetTerm sourceTerm) :
    Conv sourceTerm targetTerm :=
  Conv.fromStepStarReverse (StepStar.fromStep reverseStep)

/-- Raw-rename projection of `Conv.fromStepReverse`. -/
theorem Conv.fromStepReverse_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (reverseStep : Step targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.fromStepReverse reverseStep)

/-- Canonical-weaken specialization of `Conv.fromStepReverse_renamed`. -/
theorem Conv.fromStepReverse_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (reverseStep : Step targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.fromStepReverse reverseStep)

/-- Raw-subst projection of `Conv.fromStepReverse`. -/
theorem Conv.fromStepReverse_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (reverseStep : Step targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.fromStepReverse reverseStep)

/-- Singleton-substitution specialization of
`Conv.fromStepReverse_substituted`. -/
theorem Conv.fromStepReverse_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (reverseStep : Step targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.fromStepReverse reverseStep)

/-- Multi-position parallel-substitution sibling of
`Conv.fromStepReverse_substituted`.

A single typed reverse Step plus pointwise-related substitutions
lifts to a raw join at the differently-substituted endpoints.  Pure
delegation: `Conv.rawSubst_par_toRawJoin` after `Conv.fromStepReverse`. -/
theorem Conv.fromStepReverse_subst_par
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    (reverseStep : Step targetTerm sourceTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst firstSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst secondSubst) commonRaw :=
  Conv.rawSubst_par_toRawJoin substsRelated
    (Conv.fromStepReverse reverseStep)

/-! ## refl × action raw lifters

`Conv.reflRaw` is the canonical no-reduction witness: `parStar.refl`
on both sides.  Lifting it through each action collapses to
`⟨someRaw.<action>, parStar.refl, parStar.refl⟩` via the unified
`Conv.<action>Raw` pipeline — useful as the canonical "trivial" raw
join under an action when a consumer needs an identity element. -/

/-- Raw-rename projection of `Conv.refl`.  Both chains are
reflexive `parStar` on `someRaw.rename rho`. -/
theorem Conv.reflRaw_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {someType : Ty level sourceScope} {someRaw : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (someTerm : Term context someType someRaw) :
    ∃ commonRaw,
      RawStep.parStar (someRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (someRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.refl someTerm)

/-- Canonical-weaken specialization of `Conv.reflRaw_renamed`. -/
theorem Conv.reflRaw_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ∃ commonRaw,
      RawStep.parStar someRaw.weaken commonRaw ∧
      RawStep.parStar someRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.refl someTerm)

/-- Raw-subst projection of `Conv.refl`. -/
theorem Conv.reflRaw_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {someType : Ty level sourceScope} {someRaw : RawTerm sourceScope}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (someTerm : Term context someType someRaw) :
    ∃ commonRaw,
      RawStep.parStar (someRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (someRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.refl someTerm)

/-- Singleton-substitution specialization of
`Conv.reflRaw_substituted`. -/
theorem Conv.reflRaw_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {someType : Ty level (scope + 1)} {someRaw : RawTerm (scope + 1)}
    (argRaw : RawTerm scope)
    (someTerm : Term context someType someRaw) :
    ∃ commonRaw,
      RawStep.parStar (someRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (someRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.refl someTerm)

/-! ## sym × action raw lifters

`Conv.symRaw` swaps the source/target raw-projection slots.  Each
action variant applies the swap *after* lifting through the action,
giving the consumer a target-side-first raw join under any of the
four canonical actions.  Useful for backward-chaining strategies and
NbE bridges that expect the target endpoint first. -/

/-- Raw-rename projection of `Conv.sym`. -/
theorem Conv.symRaw_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.sym convertibility)

/-- Canonical-weaken specialization of `Conv.symRaw_renamed`. -/
theorem Conv.symRaw_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar targetRaw.weaken commonRaw ∧
      RawStep.parStar sourceRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.sym convertibility)

/-- Raw-subst projection of `Conv.sym`. -/
theorem Conv.symRaw_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.sym convertibility)

/-- Singleton-substitution specialization of
`Conv.symRaw_substituted`. -/
theorem Conv.symRaw_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.sym convertibility)

/-! ## Two-chain-plus-action lifters

When a consumer has two consecutive typed `StepStar` chains
(t1 → t2 → t3, both monotonic) the four corollaries below
chain-compose them via `Conv.transChains` and lift the result
through each canonical action.  Useful when reduction sequences are
the natural input form (e.g. compiler optimization passes that
record their work as a sequence of reduction steps). -/

/-! ## Two-Step-plus-action lifters

When a consumer has two consecutive typed single `Step`s (not chains)
the four corollaries below skip the manual `StepStar.fromStep` lift
step.  Compose `Conv.transChains` with each canonical raw action,
applied through the existing `Conv.<action>Raw` projection.

Pipeline: `Conv.<action>Raw <action-arg>
  (Conv.transChains (StepStar.fromStep firstStep)
                    (StepStar.fromStep secondStep))`.

Useful when reduction sequences arrive as a list of `Step` witnesses
(e.g. a compiler optimization pass that emits one `Step` per
rewrite) — saves the per-call site `StepStar.fromStep` wrapping. -/

/-- Combine two typed single Steps with a raw renaming.  Same shape
as `Conv.transChains_renamed` but takes `Step` instead of `StepStar`
on each leg, lifting each via `StepStar.fromStep`. -/
theorem Conv.transRaw_twoSteps_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstStep : Step sourceTerm middleTerm)
    (secondStep : Step middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (farRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming
    (Conv.transChains (StepStar.fromStep firstStep)
                      (StepStar.fromStep secondStep))

/-- Canonical-weaken specialization of `Conv.transRaw_twoSteps_renamed`. -/
theorem Conv.transRaw_twoSteps_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType middleType farType : Ty level scope}
    {sourceRaw middleRaw farRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (firstStep : Step sourceTerm middleTerm)
    (secondStep : Step middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar farRaw.weaken commonRaw :=
  Conv.weakenRaw
    (Conv.transChains (StepStar.fromStep firstStep)
                      (StepStar.fromStep secondStep))

/-- Combine two typed single Steps with a raw substitution. -/
theorem Conv.transRaw_twoSteps_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (firstStep : Step sourceTerm middleTerm)
    (secondStep : Step middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (farRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst
    (Conv.transChains (StepStar.fromStep firstStep)
                      (StepStar.fromStep secondStep))

/-- Singleton-substitution specialization of
`Conv.transRaw_twoSteps_substituted`.  This is the natural
β-redex-after-two-rewrites shape downstream Geuvers 1992 β-η critical
pair (K12.28) consumers reach for when both sides of the pair are
single-Step reductions inside a binder. -/
theorem Conv.transRaw_twoSteps_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType middleType farType : Ty level (scope + 1)}
    {sourceRaw middleRaw farRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (argRaw : RawTerm scope)
    (firstStep : Step sourceTerm middleTerm)
    (secondStep : Step middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (farRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw
    (Conv.transChains (StepStar.fromStep firstStep)
                      (StepStar.fromStep secondStep))

/-! ## Chain-then-Step-plus-action lifters

When the first leg is a `StepStar` chain and the second leg is a
single `Step`, these compose into a Conv (via `transChains` after
lifting the Step) and project to raw under each canonical action.

Pipeline: `Conv.<action>Raw <action-arg>
  (Conv.transChains firstChain (StepStar.fromStep secondStep))`.

Saves the per-call site `StepStar.fromStep` wrap when only the
second leg is a single Step.  Mirror of the `stepChain` family (first
leg single Step, second leg chain) — together they cover the
asymmetric chain/step composition shapes downstream consumers reach
for at boundary cong-rule arms. -/

/-- Combine a chain + single Step with a raw renaming. -/
theorem Conv.transRaw_chainStep_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstChain : StepStar sourceTerm middleTerm)
    (secondStep : Step middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (farRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming
    (Conv.transChains firstChain (StepStar.fromStep secondStep))

/-- Canonical-weaken specialization of `Conv.transRaw_chainStep_renamed`. -/
theorem Conv.transRaw_chainStep_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType middleType farType : Ty level scope}
    {sourceRaw middleRaw farRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (firstChain : StepStar sourceTerm middleTerm)
    (secondStep : Step middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar farRaw.weaken commonRaw :=
  Conv.weakenRaw
    (Conv.transChains firstChain (StepStar.fromStep secondStep))

/-- Combine a chain + single Step with a raw substitution. -/
theorem Conv.transRaw_chainStep_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (firstChain : StepStar sourceTerm middleTerm)
    (secondStep : Step middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (farRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst
    (Conv.transChains firstChain (StepStar.fromStep secondStep))

/-- Singleton-substitution specialization of
`Conv.transRaw_chainStep_substituted`. -/
theorem Conv.transRaw_chainStep_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType middleType farType : Ty level (scope + 1)}
    {sourceRaw middleRaw farRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (argRaw : RawTerm scope)
    (firstChain : StepStar sourceTerm middleTerm)
    (secondStep : Step middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (farRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw
    (Conv.transChains firstChain (StepStar.fromStep secondStep))

/-! ## Step-then-Chain-plus-action lifters

Mirror of the `chainStep` family: first leg is a single `Step`,
second leg is a `StepStar` chain.  Composes via `transChains` after
lifting the first Step. -/

/-- Combine a single Step + chain with a raw renaming. -/
theorem Conv.transRaw_stepChain_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstStep : Step sourceTerm middleTerm)
    (secondChain : StepStar middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (farRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming
    (Conv.transChains (StepStar.fromStep firstStep) secondChain)

/-- Canonical-weaken specialization of `Conv.transRaw_stepChain_renamed`. -/
theorem Conv.transRaw_stepChain_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType middleType farType : Ty level scope}
    {sourceRaw middleRaw farRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (firstStep : Step sourceTerm middleTerm)
    (secondChain : StepStar middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar farRaw.weaken commonRaw :=
  Conv.weakenRaw
    (Conv.transChains (StepStar.fromStep firstStep) secondChain)

/-- Combine a single Step + chain with a raw substitution. -/
theorem Conv.transRaw_stepChain_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (firstStep : Step sourceTerm middleTerm)
    (secondChain : StepStar middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (farRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst
    (Conv.transChains (StepStar.fromStep firstStep) secondChain)

/-- Singleton-substitution specialization of
`Conv.transRaw_stepChain_substituted`. -/
theorem Conv.transRaw_stepChain_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType middleType farType : Ty level (scope + 1)}
    {sourceRaw middleRaw farRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (argRaw : RawTerm scope)
    (firstStep : Step sourceTerm middleTerm)
    (secondChain : StepStar middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (farRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw
    (Conv.transChains (StepStar.fromStep firstStep) secondChain)

/-- Combine two typed StepStar chains with a raw renaming. -/
theorem Conv.transChains_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstChain : StepStar sourceTerm middleTerm)
    (secondChain : StepStar middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (farRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.transChains firstChain secondChain)

/-- Canonical-weaken specialization of `Conv.transChains_renamed`. -/
theorem Conv.transChains_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType middleType farType : Ty level scope}
    {sourceRaw middleRaw farRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (firstChain : StepStar sourceTerm middleTerm)
    (secondChain : StepStar middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar farRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.transChains firstChain secondChain)

/-- Combine two typed StepStar chains with a raw substitution. -/
theorem Conv.transChains_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType farType : Ty level sourceScope}
    {sourceRaw middleRaw farRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (firstChain : StepStar sourceTerm middleTerm)
    (secondChain : StepStar middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (farRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.transChains firstChain secondChain)

/-- Singleton-substitution specialization of
`Conv.transChains_substituted`. -/
theorem Conv.transChains_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType middleType farType : Ty level (scope + 1)}
    {sourceRaw middleRaw farRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (argRaw : RawTerm scope)
    (firstChain : StepStar sourceTerm middleTerm)
    (secondChain : StepStar middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (farRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.transChains firstChain secondChain)

end LeanFX2
