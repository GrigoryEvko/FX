import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.RawParStarCong

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
raw confluence join to a typed Term.  Two flavors exist:

* `Conv.transChains` / `Conv.trans_via_chains` — chain-composition
  flavor, zero-axiom (lives in `Reduction/Conv.lean` /
  `Confluence/ConvTrans.lean`).  Covers the case where both Conv
  witnesses arrive as explicit `StepStar` chains.
* Full unrestricted `Conv.trans` — still blocked on strong subject
  reduction (term construction, not just type equality).  See
  `Confluence/ConvTrans.lean` docstring.

The raw analog `Conv.transRaw` is shipped in `ChurchRosser.lean`.

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

/-! ## Canonical-head target-reduction corollaries

When the source of a typed `Conv` has a closed canonical-head raw
form (e.g., `RawTerm.unit`, `RawTerm.boolTrue`), the raw common
reduct is forced to be the same canonical head (by the
`RawStep.parStar.<head>_inv` family in `Confluence/RawParStarCong.lean`).
Substituting this into the target-side chain gives:

  `RawStep.parStar targetRaw RawTerm.<head>`

i.e. the target reduces to the same canonical head at the raw
level.  This is the **forward** direction of "canonical form
propagation" — the REVERSE (forcing target.toRaw = <head>) is
false in general; cf. β-counterexample `(λx. unit) arg →β unit`
where the source is the β-redex, not `unit` itself.

These eight corollaries collapse the pattern
`Conv.canonicalRaw cv → RawStep.parStar.<head>_inv → substitute`
into a single named call.  Useful for NbE bridges (K13) when
the target must be shown to compute to the same canonical head as
the source, and for K12 fundamental-theorem closed-head closure
clauses. -/

/-- `Conv sourceTerm targetTerm` where source has raw `unit`
forces the target's raw projection to reduce to `unit`. -/
theorem Conv.targetReaches_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar targetRaw RawTerm.unit := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  exact joinEqUnit ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw `boolTrue`
forces the target's raw projection to reduce to `boolTrue`. -/
theorem Conv.targetReaches_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar targetRaw RawTerm.boolTrue := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  exact joinEqTrue ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw `boolFalse`
forces the target's raw projection to reduce to `boolFalse`. -/
theorem Conv.targetReaches_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar targetRaw RawTerm.boolFalse := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  exact joinEqFalse ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw `natZero`
forces the target's raw projection to reduce to `natZero`. -/
theorem Conv.targetReaches_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar targetRaw RawTerm.natZero := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  exact joinEqZero ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw `listNil`
forces the target's raw projection to reduce to `listNil`. -/
theorem Conv.targetReaches_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.listNil : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar targetRaw RawTerm.listNil := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv sourceToJoin
  exact joinEqNil ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw `optionNone`
forces the target's raw projection to reduce to `optionNone`. -/
theorem Conv.targetReaches_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.optionNone : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar targetRaw RawTerm.optionNone := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv sourceToJoin
  exact joinEqNone ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw `var position`
forces the target's raw projection to reduce to the same `var
position`. -/
theorem Conv.targetReaches_var
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {position : Fin scope}
    {sourceTerm : Term context sourceType (RawTerm.var position : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar targetRaw (RawTerm.var position) := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqVar : joinRaw = RawTerm.var position :=
    RawStep.parStar.var_inv sourceToJoin
  exact joinEqVar ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw `universeCode
innerLevel` forces the target's raw projection to reduce to the
same `universeCode innerLevel`. -/
theorem Conv.targetReaches_universeCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar targetRaw (RawTerm.universeCode innerLevel) := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  exact joinEqCode ▸ targetToJoin

/-! ## Source-side canonical-head Conv corollaries

Symmetric variants of the `targetReaches_<head>` family: given a
`Conv sourceTerm targetTerm` where the **target** has a canonical
raw head, the **source** is forced to reduce to that head.  Each
proof is a one-line `Conv.sym` of the iter 26 theorem above.

These complete the canonical-form propagation grid: source→target
AND target→source for the eight canonical heads `unit`,
`boolTrue`, `boolFalse`, `natZero`, `listNil`, `optionNone`, `var`,
`universeCode`.  Useful for fundamental-theorem closed-head
closure clauses where the canonical normal form sits on either
side of the Conv. -/

/-- `Conv sourceTerm targetTerm` where target has raw `unit`
forces the source's raw projection to reduce to `unit`. -/
theorem Conv.sourceReaches_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar sourceRaw RawTerm.unit :=
  Conv.targetReaches_unit (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw `boolTrue`
forces the source's raw projection to reduce to `boolTrue`. -/
theorem Conv.sourceReaches_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar sourceRaw RawTerm.boolTrue :=
  Conv.targetReaches_boolTrue (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw `boolFalse`
forces the source's raw projection to reduce to `boolFalse`. -/
theorem Conv.sourceReaches_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar sourceRaw RawTerm.boolFalse :=
  Conv.targetReaches_boolFalse (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw `natZero`
forces the source's raw projection to reduce to `natZero`. -/
theorem Conv.sourceReaches_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar sourceRaw RawTerm.natZero :=
  Conv.targetReaches_natZero (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw `listNil`
forces the source's raw projection to reduce to `listNil`. -/
theorem Conv.sourceReaches_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar sourceRaw RawTerm.listNil :=
  Conv.targetReaches_listNil (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw `optionNone`
forces the source's raw projection to reduce to `optionNone`. -/
theorem Conv.sourceReaches_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar sourceRaw RawTerm.optionNone :=
  Conv.targetReaches_optionNone (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw `var position`
forces the source's raw projection to reduce to the same
`var position`. -/
theorem Conv.sourceReaches_var
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {position : Fin scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType (RawTerm.var position : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar sourceRaw (RawTerm.var position) :=
  Conv.targetReaches_var (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw `universeCode
innerLevel` forces the source's raw projection to reduce to the
same `universeCode innerLevel`. -/
theorem Conv.sourceReaches_universeCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    RawStep.parStar sourceRaw (RawTerm.universeCode innerLevel) :=
  Conv.targetReaches_universeCode (Conv.sym convertibility)

/-! ## Compound canonical-head Conv corollaries

Extension of the leaf-canonical-head propagation to **single-
payload compound** heads — `natSucc`, `optionSome`, `eitherInl`,
`eitherInr`.  Unlike the leaf case, the conclusion carries an
existential witness for the payload's projection target plus a
parStar chain on the payload itself.

Given `Conv sourceTerm targetTerm` with sourceRaw =
`<head> payloadSource`, we recover `∃ payloadTarget,
parStar targetRaw (<head> payloadTarget) ∧
parStar payloadSource payloadTarget`.  The dual signature handles
the case where the *target* carries the compound shape.

Useful for fundamental-theorem closure where a Conv connects a
known compound-shape canonical form to an unknown term — we
project the head AND lift the convergence to the payload.  The
payload chain composes with downstream Reducible / canonical-form
reasoning at one universe lower. -/

/-- `Conv sourceTerm targetTerm` where source has raw
`natSucc predecessor` forces the target's raw projection to
reduce to `natSucc payloadTarget` and the source predecessor to
parStar-reduce to that same `payloadTarget`. -/
theorem Conv.targetReaches_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.natSucc predecessor : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ payloadTarget,
      RawStep.parStar targetRaw (RawTerm.natSucc payloadTarget) ∧
      RawStep.parStar predecessor payloadTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨payloadTarget, joinEq, payloadChain⟩ :=
    RawStep.parStar.natSucc_inv sourceToJoin
  refine ⟨payloadTarget, ?_, payloadChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`optionSome value` forces the target's raw projection to reduce
to `optionSome payloadTarget` and the source value to
parStar-reduce to that same `payloadTarget`. -/
theorem Conv.targetReaches_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw valueRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionSome valueRaw : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ payloadTarget,
      RawStep.parStar targetRaw (RawTerm.optionSome payloadTarget) ∧
      RawStep.parStar valueRaw payloadTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨payloadTarget, joinEq, payloadChain⟩ :=
    RawStep.parStar.optionSome_inv sourceToJoin
  refine ⟨payloadTarget, ?_, payloadChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`eitherInl value` forces the target's raw projection to reduce
to `eitherInl payloadTarget` and the source value to
parStar-reduce to that same `payloadTarget`. -/
theorem Conv.targetReaches_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw valueRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInl valueRaw : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ payloadTarget,
      RawStep.parStar targetRaw (RawTerm.eitherInl payloadTarget) ∧
      RawStep.parStar valueRaw payloadTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨payloadTarget, joinEq, payloadChain⟩ :=
    RawStep.parStar.eitherInl_inv sourceToJoin
  refine ⟨payloadTarget, ?_, payloadChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`eitherInr value` forces the target's raw projection to reduce
to `eitherInr payloadTarget` and the source value to
parStar-reduce to that same `payloadTarget`. -/
theorem Conv.targetReaches_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw valueRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInr valueRaw : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ payloadTarget,
      RawStep.parStar targetRaw (RawTerm.eitherInr payloadTarget) ∧
      RawStep.parStar valueRaw payloadTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨payloadTarget, joinEq, payloadChain⟩ :=
    RawStep.parStar.eitherInr_inv sourceToJoin
  refine ⟨payloadTarget, ?_, payloadChain⟩
  exact joinEq ▸ targetToJoin

/-! ### Source-side mirrors of the compound canonical-head family

Symmetric form: target has the compound canonical raw, source's
raw projection is then forced to reduce to that compound shape
with a matching payload-target chain.  Each proof is a one-line
`Conv.sym` of the corresponding target-side theorem. -/

/-- `Conv sourceTerm targetTerm` where target has raw
`natSucc predecessor` forces the source's raw projection to
reduce to `natSucc payloadTarget` and the target predecessor to
parStar-reduce to that same `payloadTarget`. -/
theorem Conv.sourceReaches_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ payloadTarget,
      RawStep.parStar sourceRaw (RawTerm.natSucc payloadTarget) ∧
      RawStep.parStar predecessor payloadTarget :=
  Conv.targetReaches_natSucc (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw
`optionSome value` forces the source's raw projection to reduce
to `optionSome payloadTarget` and the target value to
parStar-reduce to that same `payloadTarget`. -/
theorem Conv.sourceReaches_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw valueRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueRaw : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ payloadTarget,
      RawStep.parStar sourceRaw (RawTerm.optionSome payloadTarget) ∧
      RawStep.parStar valueRaw payloadTarget :=
  Conv.targetReaches_optionSome (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw
`eitherInl value` forces the source's raw projection to reduce
to `eitherInl payloadTarget` and the target value to
parStar-reduce to that same `payloadTarget`. -/
theorem Conv.sourceReaches_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw valueRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueRaw : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ payloadTarget,
      RawStep.parStar sourceRaw (RawTerm.eitherInl payloadTarget) ∧
      RawStep.parStar valueRaw payloadTarget :=
  Conv.targetReaches_eitherInl (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw
`eitherInr value` forces the source's raw projection to reduce
to `eitherInr payloadTarget` and the target value to
parStar-reduce to that same `payloadTarget`. -/
theorem Conv.sourceReaches_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw valueRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueRaw : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ payloadTarget,
      RawStep.parStar sourceRaw (RawTerm.eitherInr payloadTarget) ∧
      RawStep.parStar valueRaw payloadTarget :=
  Conv.targetReaches_eitherInr (Conv.sym convertibility)

/-! ## Value-introduction Conv corollaries (refl / pair / listCons)

Three more value-level cong-only canonical-head Conv corollaries:
the identity-type intro `refl`, the dependent-pair intro `pair`,
and the list intro `listCons`.  Each `<head>_inv` lemma in
`Confluence/RawParStarCong.lean` (lines 1820, 1862, 1874) is
pure-cong (no β/ι firing), so the Conv corollary follows the
same pattern as the compound-head family but with one or two
payload chains.

These complete the value-level introduction-form Conv grid:
nullary canonical introductions (`unit`, `boolTrue`, `boolFalse`,
`natZero`, `listNil`, `optionNone` — iter 26 leaf family), unary
canonical introductions (`natSucc`, `optionSome`, `eitherInl`,
`eitherInr` — iter 28 compound family), and now the binary
introductions (`pair`, `listCons`) plus the identity-intro
(`refl`).  Downstream consumers: K12 fundamental theorem arms
for `fst`/`snd` (pair scrutinee), `listElim` (listCons scrutinee),
and `idJ` (refl scrutinee). -/

/-- `Conv sourceTerm targetTerm` where source has raw
`refl rawWitness` forces the target's raw projection to reduce
to `refl witnessTarget` for some `witnessTarget` and the source
witness to parStar-reduce to that same `witnessTarget`. -/
theorem Conv.targetReaches_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw rawWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refl rawWitness : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ witnessTarget,
      RawStep.parStar targetRaw (RawTerm.refl witnessTarget) ∧
      RawStep.parStar rawWitness witnessTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨witnessTarget, joinEq, witnessChain⟩ :=
    RawStep.parStar.refl_inv sourceToJoin
  refine ⟨witnessTarget, ?_, witnessChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`pair firstValue secondValue` forces the target's raw projection
to reduce to `pair firstTarget secondTarget` and the two source
components to parStar-reduce to the matching projections. -/
theorem Conv.targetReaches_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pair firstValue secondValue : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ firstTarget secondTarget,
      RawStep.parStar targetRaw (RawTerm.pair firstTarget secondTarget) ∧
      RawStep.parStar firstValue firstTarget ∧
      RawStep.parStar secondValue secondTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨firstTarget, secondTarget, joinEq, firstChain, secondChain⟩ :=
    RawStep.parStar.pair_inv sourceToJoin
  refine ⟨firstTarget, secondTarget, ?_, firstChain, secondChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`listCons headTerm tailTerm` forces the target's raw projection
to reduce to `listCons headTarget tailTarget` and both head and
tail components to parStar-reduce to the matching projections. -/
theorem Conv.targetReaches_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ headTarget tailTarget,
      RawStep.parStar targetRaw (RawTerm.listCons headTarget tailTarget) ∧
      RawStep.parStar headTerm headTarget ∧
      RawStep.parStar tailTerm tailTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨headTarget, tailTarget, joinEq, headChain, tailChain⟩ :=
    RawStep.parStar.listCons_inv sourceToJoin
  refine ⟨headTarget, tailTarget, ?_, headChain, tailChain⟩
  exact joinEq ▸ targetToJoin

/-! ### Source-side mirrors of the value-introduction family

Each proof is a one-line `Conv.sym` composition over the
corresponding target-side theorem.  Used when the canonical
intro shape sits on the *target* of the Conv. -/

/-- `Conv sourceTerm targetTerm` where target has raw
`refl rawWitness` forces the source's raw projection to reduce
to `refl witnessTarget` for some `witnessTarget` and the target
witness to parStar-reduce to that same `witnessTarget`. -/
theorem Conv.sourceReaches_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw rawWitness : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.refl rawWitness : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ witnessTarget,
      RawStep.parStar sourceRaw (RawTerm.refl witnessTarget) ∧
      RawStep.parStar rawWitness witnessTarget :=
  Conv.targetReaches_refl (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw
`pair firstValue secondValue` forces the source's raw projection
to reduce to `pair firstTarget secondTarget` and the two target
components to parStar-reduce to the matching projections. -/
theorem Conv.sourceReaches_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ firstTarget secondTarget,
      RawStep.parStar sourceRaw (RawTerm.pair firstTarget secondTarget) ∧
      RawStep.parStar firstValue firstTarget ∧
      RawStep.parStar secondValue secondTarget :=
  Conv.targetReaches_pair (Conv.sym convertibility)

/-- `Conv sourceTerm targetTerm` where target has raw
`listCons headTerm tailTerm` forces the source's raw projection
to reduce to `listCons headTarget tailTarget` and both head and
tail components to parStar-reduce to the matching projections. -/
theorem Conv.sourceReaches_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ headTarget tailTarget,
      RawStep.parStar sourceRaw (RawTerm.listCons headTarget tailTarget) ∧
      RawStep.parStar headTerm headTarget ∧
      RawStep.parStar tailTerm tailTarget :=
  Conv.targetReaches_listCons (Conv.sym convertibility)

/-! ## Type-code Conv corollaries (homogeneous-scope family)

Lift the type-code parStar inversions (lines 1925-2038 of
`Confluence/RawParStarCong.lean`) to Conv corollaries.  Type
codes are RawTerm-level representations of types — they carry no
binder bumps and the cong rules are pure preservation (no β/ι
firing).  The seven heads in this homogeneous-scope batch:

  - `listCode`     (unary; element type code)
  - `optionCode`   (unary; element type code)
  - `arrowCode`    (binary; domain + codomain code)
  - `productCode`  (binary; first + second code)
  - `sumCode`      (binary; left + right code)
  - `eitherCode`   (binary; left + right code)
  - `equivCode`    (binary; left + right code)

Each Conv corollary uses `Conv.canonicalRaw` + the corresponding
`<head>_inv` to project the head through the chain.  Useful for
K12.16 `cumulUp` and K12.14 `refine` fundamental-theorem closures
that work with type-code scrutinees, and for any downstream
universe-polymorphism reasoning where a Conv connects two type
codes. -/

/-- `Conv sourceTerm targetTerm` where source has raw
`listCode elementCode` forces the target's raw projection to
reduce to `listCode elementTarget` and the source element code
to parStar-reduce to that same `elementTarget`. -/
theorem Conv.targetReaches_listCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ elementTarget,
      RawStep.parStar targetRaw (RawTerm.listCode elementTarget) ∧
      RawStep.parStar elementCode elementTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨elementTarget, joinEq, elementChain⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  refine ⟨elementTarget, ?_, elementChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`optionCode elementCode` forces the target's raw projection to
reduce to `optionCode elementTarget` and the source element code
to parStar-reduce to that same `elementTarget`. -/
theorem Conv.targetReaches_optionCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ elementTarget,
      RawStep.parStar targetRaw (RawTerm.optionCode elementTarget) ∧
      RawStep.parStar elementCode elementTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨elementTarget, joinEq, elementChain⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  refine ⟨elementTarget, ?_, elementChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`arrowCode domainCode codomainCode` forces the target's raw
projection to reduce to `arrowCode domainTarget codomainTarget`
and both source codes to parStar-reduce to those matching
targets. -/
theorem Conv.targetReaches_arrowCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ domainTarget codomainTarget,
      RawStep.parStar targetRaw
        (RawTerm.arrowCode domainTarget codomainTarget) ∧
      RawStep.parStar domainCode domainTarget ∧
      RawStep.parStar codomainCode codomainTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨domainTarget, codomainTarget, joinEq, domainChain, codomainChain⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  refine ⟨domainTarget, codomainTarget, ?_, domainChain, codomainChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`productCode firstCode secondCode` forces the target's raw
projection to reduce to `productCode firstTarget secondTarget`
and both source codes to parStar-reduce to those matching
targets. -/
theorem Conv.targetReaches_productCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ firstTarget secondTarget,
      RawStep.parStar targetRaw
        (RawTerm.productCode firstTarget secondTarget) ∧
      RawStep.parStar firstCode firstTarget ∧
      RawStep.parStar secondCode secondTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨firstTarget, secondTarget, joinEq, firstChain, secondChain⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  refine ⟨firstTarget, secondTarget, ?_, firstChain, secondChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`sumCode leftCode rightCode` forces the target's raw projection
to reduce to `sumCode leftTarget rightTarget` and both source
codes to parStar-reduce to those matching targets. -/
theorem Conv.targetReaches_sumCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar targetRaw
        (RawTerm.sumCode leftTarget rightTarget) ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨leftTarget, rightTarget, joinEq, leftChain, rightChain⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  refine ⟨leftTarget, rightTarget, ?_, leftChain, rightChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`eitherCode leftCode rightCode` forces the target's raw
projection to reduce to `eitherCode leftTarget rightTarget` and
both source codes to parStar-reduce to those matching
targets. -/
theorem Conv.targetReaches_eitherCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar targetRaw
        (RawTerm.eitherCode leftTarget rightTarget) ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨leftTarget, rightTarget, joinEq, leftChain, rightChain⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  refine ⟨leftTarget, rightTarget, ?_, leftChain, rightChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`equivCode leftCode rightCode` forces the target's raw
projection to reduce to `equivCode leftTarget rightTarget` and
both source codes to parStar-reduce to those matching
targets. -/
theorem Conv.targetReaches_equivCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar targetRaw
        (RawTerm.equivCode leftTarget rightTarget) ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨leftTarget, rightTarget, joinEq, leftChain, rightChain⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  refine ⟨leftTarget, rightTarget, ?_, leftChain, rightChain⟩
  exact joinEq ▸ targetToJoin

/-! ### Source-side mirrors of the type-code homogeneous family

Each proof is a one-line `Conv.sym` composition of the
corresponding target-side theorem.  Used when the type-code
shape sits on the *target* of the Conv. -/

/-- Source-side mirror of `targetReaches_listCode`. -/
theorem Conv.sourceReaches_listCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.listCode elementCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ elementTarget,
      RawStep.parStar sourceRaw (RawTerm.listCode elementTarget) ∧
      RawStep.parStar elementCode elementTarget :=
  Conv.targetReaches_listCode (Conv.sym convertibility)

/-- Source-side mirror of `targetReaches_optionCode`. -/
theorem Conv.sourceReaches_optionCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ elementTarget,
      RawStep.parStar sourceRaw (RawTerm.optionCode elementTarget) ∧
      RawStep.parStar elementCode elementTarget :=
  Conv.targetReaches_optionCode (Conv.sym convertibility)

/-- Source-side mirror of `targetReaches_arrowCode`. -/
theorem Conv.sourceReaches_arrowCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ domainTarget codomainTarget,
      RawStep.parStar sourceRaw
        (RawTerm.arrowCode domainTarget codomainTarget) ∧
      RawStep.parStar domainCode domainTarget ∧
      RawStep.parStar codomainCode codomainTarget :=
  Conv.targetReaches_arrowCode (Conv.sym convertibility)

/-- Source-side mirror of `targetReaches_productCode`. -/
theorem Conv.sourceReaches_productCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ firstTarget secondTarget,
      RawStep.parStar sourceRaw
        (RawTerm.productCode firstTarget secondTarget) ∧
      RawStep.parStar firstCode firstTarget ∧
      RawStep.parStar secondCode secondTarget :=
  Conv.targetReaches_productCode (Conv.sym convertibility)

/-- Source-side mirror of `targetReaches_sumCode`. -/
theorem Conv.sourceReaches_sumCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.sumCode leftCode rightCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar sourceRaw
        (RawTerm.sumCode leftTarget rightTarget) ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget :=
  Conv.targetReaches_sumCode (Conv.sym convertibility)

/-- Source-side mirror of `targetReaches_eitherCode`. -/
theorem Conv.sourceReaches_eitherCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.eitherCode leftCode rightCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar sourceRaw
        (RawTerm.eitherCode leftTarget rightTarget) ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget :=
  Conv.targetReaches_eitherCode (Conv.sym convertibility)

/-- Source-side mirror of `targetReaches_equivCode`. -/
theorem Conv.sourceReaches_equivCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.equivCode leftCode rightCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar sourceRaw
        (RawTerm.equivCode leftTarget rightTarget) ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget :=
  Conv.targetReaches_equivCode (Conv.sym convertibility)

/-! ## Binder-scoped type-code Conv corollaries (piTyCode / sigmaTyCode)

Two type codes carry a binder bump: `piTyCode` has its codomain
at `RawTerm (scope + 1)` and `sigmaTyCode` has its second-payload
at `RawTerm (scope + 1)`.  The Conv corollary signatures stay
identical in shape to the homogeneous family — the bump lives in
the type of the codomain/second binder, not in the structure of
the corollary itself.  The parStar chain on the bumped payload
operates purely at the raw level over `RawTerm (scope + 1)`. -/

/-- `Conv sourceTerm targetTerm` where source has raw
`piTyCode domainCode codomainCode` forces the target's raw
projection to reduce to `piTyCode domainTarget codomainTarget`
with codomain target at scope+1, and both source codes
parStar-reduce to those matching targets. -/
theorem Conv.targetReaches_piTyCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (domainTarget : RawTerm scope) (codomainTarget : RawTerm (scope + 1)),
      RawStep.parStar targetRaw
        (RawTerm.piTyCode domainTarget codomainTarget) ∧
      RawStep.parStar domainCode domainTarget ∧
      RawStep.parStar codomainCode codomainTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨domainTarget, codomainTarget, joinEq, domainChain, codomainChain⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  refine ⟨domainTarget, codomainTarget, ?_, domainChain, codomainChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`sigmaTyCode firstCode secondCode` forces the target's raw
projection to reduce to `sigmaTyCode firstTarget secondTarget`
with second target at scope+1, and both source codes
parStar-reduce to those matching targets. -/
theorem Conv.targetReaches_sigmaTyCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw : RawTerm scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (firstTarget : RawTerm scope) (secondTarget : RawTerm (scope + 1)),
      RawStep.parStar targetRaw
        (RawTerm.sigmaTyCode firstTarget secondTarget) ∧
      RawStep.parStar firstCode firstTarget ∧
      RawStep.parStar secondCode secondTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨firstTarget, secondTarget, joinEq, firstChain, secondChain⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  refine ⟨firstTarget, secondTarget, ?_, firstChain, secondChain⟩
  exact joinEq ▸ targetToJoin

/-- Source-side mirror of `targetReaches_piTyCode`. -/
theorem Conv.sourceReaches_piTyCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (domainTarget : RawTerm scope) (codomainTarget : RawTerm (scope + 1)),
      RawStep.parStar sourceRaw
        (RawTerm.piTyCode domainTarget codomainTarget) ∧
      RawStep.parStar domainCode domainTarget ∧
      RawStep.parStar codomainCode codomainTarget :=
  Conv.targetReaches_piTyCode (Conv.sym convertibility)

/-- Source-side mirror of `targetReaches_sigmaTyCode`. -/
theorem Conv.sourceReaches_sigmaTyCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (firstTarget : RawTerm scope) (secondTarget : RawTerm (scope + 1)),
      RawStep.parStar sourceRaw
        (RawTerm.sigmaTyCode firstTarget secondTarget) ∧
      RawStep.parStar firstCode firstTarget ∧
      RawStep.parStar secondCode secondTarget :=
  Conv.targetReaches_sigmaTyCode (Conv.sym convertibility)

/-! ## Ternary type-code Conv corollaries (idCode)

`idCode` carries three homogeneous-scope payloads (type code +
left witness code + right witness code).  The Conv corollary
mirrors the pattern of binary heads with one extra payload. -/

/-- `Conv sourceTerm targetTerm` where source has raw
`idCode typeCode leftCode rightCode` forces the target's raw
projection to reduce to `idCode typeTarget leftTarget rightTarget`
and all three source codes parStar-reduce to matching targets. -/
theorem Conv.targetReaches_idCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ typeTarget leftTarget rightTarget,
      RawStep.parStar targetRaw
        (RawTerm.idCode typeTarget leftTarget rightTarget) ∧
      RawStep.parStar typeCode typeTarget ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨typeTarget, leftTarget, rightTarget,
      joinEq, typeChain, leftChain, rightChain⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  refine ⟨typeTarget, leftTarget, rightTarget, ?_,
    typeChain, leftChain, rightChain⟩
  exact joinEq ▸ targetToJoin

/-- Source-side mirror of `targetReaches_idCode`. -/
theorem Conv.sourceReaches_idCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ typeTarget leftTarget rightTarget,
      RawStep.parStar sourceRaw
        (RawTerm.idCode typeTarget leftTarget rightTarget) ∧
      RawStep.parStar typeCode typeTarget ∧
      RawStep.parStar leftCode leftTarget ∧
      RawStep.parStar rightCode rightTarget :=
  Conv.targetReaches_idCode (Conv.sym convertibility)

/-! ## Interval-operation Conv corollaries (intervalOpp / intervalMeet / intervalJoin)

Cubical-layer interval operations: `intervalOpp` is unary
(negation), `intervalMeet` and `intervalJoin` are binary lattice
operations.  Each cong-only `<head>_inv` lifts cleanly to a Conv
corollary.  Useful for cubical-layer reasoning where a Conv
connects two interval-shaped expressions in a Path / Glue
context. -/

/-- `Conv sourceTerm targetTerm` where source has raw
`intervalOpp intervalTerm` forces the target's raw projection
to reduce to `intervalOpp intervalTarget` and the source
interval to parStar-reduce to that same `intervalTarget`. -/
theorem Conv.targetReaches_intervalOpp
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ intervalTarget,
      RawStep.parStar targetRaw (RawTerm.intervalOpp intervalTarget) ∧
      RawStep.parStar intervalTerm intervalTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨intervalTarget, joinEq, intervalChain⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  refine ⟨intervalTarget, ?_, intervalChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`intervalMeet leftInterval rightInterval` forces the target's
raw projection to reduce to `intervalMeet leftTarget rightTarget`
and both source intervals parStar-reduce to matching targets. -/
theorem Conv.targetReaches_intervalMeet
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar targetRaw
        (RawTerm.intervalMeet leftTarget rightTarget) ∧
      RawStep.parStar leftInterval leftTarget ∧
      RawStep.parStar rightInterval rightTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨leftTarget, rightTarget, joinEq, leftChain, rightChain⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  refine ⟨leftTarget, rightTarget, ?_, leftChain, rightChain⟩
  exact joinEq ▸ targetToJoin

/-- `Conv sourceTerm targetTerm` where source has raw
`intervalJoin leftInterval rightInterval` forces the target's
raw projection to reduce to `intervalJoin leftTarget rightTarget`
and both source intervals parStar-reduce to matching targets. -/
theorem Conv.targetReaches_intervalJoin
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar targetRaw
        (RawTerm.intervalJoin leftTarget rightTarget) ∧
      RawStep.parStar leftInterval leftTarget ∧
      RawStep.parStar rightInterval rightTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨leftTarget, rightTarget, joinEq, leftChain, rightChain⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  refine ⟨leftTarget, rightTarget, ?_, leftChain, rightChain⟩
  exact joinEq ▸ targetToJoin

/-- Source-side mirror of `targetReaches_intervalOpp`. -/
theorem Conv.sourceReaches_intervalOpp
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ intervalTarget,
      RawStep.parStar sourceRaw (RawTerm.intervalOpp intervalTarget) ∧
      RawStep.parStar intervalTerm intervalTarget :=
  Conv.targetReaches_intervalOpp (Conv.sym convertibility)

/-- Source-side mirror of `targetReaches_intervalMeet`. -/
theorem Conv.sourceReaches_intervalMeet
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar sourceRaw
        (RawTerm.intervalMeet leftTarget rightTarget) ∧
      RawStep.parStar leftInterval leftTarget ∧
      RawStep.parStar rightInterval rightTarget :=
  Conv.targetReaches_intervalMeet (Conv.sym convertibility)

/-- Source-side mirror of `targetReaches_intervalJoin`. -/
theorem Conv.sourceReaches_intervalJoin
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ leftTarget rightTarget,
      RawStep.parStar sourceRaw
        (RawTerm.intervalJoin leftTarget rightTarget) ∧
      RawStep.parStar leftInterval leftTarget ∧
      RawStep.parStar rightInterval rightTarget :=
  Conv.targetReaches_intervalJoin (Conv.sym convertibility)

/-! ## HoTT-special `uaToEquiv` Conv corollaries

`uaToEquiv` is the (cong arm only — we lift the head-preserving
branch, leaving the β/oeqTrans branches to dedicated future
work).  Treated here as a unary cong inversion via the
`uaToEquiv_inv` lemma at line 2228 of `RawParStarCong.lean`. -/

/-- `Conv sourceTerm targetTerm` where source has raw
`uaToEquiv proofTerm` forces the target's raw projection to
reduce to `uaToEquiv proofTarget` and the source proof to
parStar-reduce to that same `proofTarget`. -/
theorem Conv.targetReaches_uaToEquiv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {targetRaw proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ proofTarget,
      RawStep.parStar targetRaw (RawTerm.uaToEquiv proofTarget) ∧
      RawStep.parStar proofTerm proofTarget := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨proofTarget, joinEq, proofChain⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  refine ⟨proofTarget, ?_, proofChain⟩
  exact joinEq ▸ targetToJoin

/-- Source-side mirror of `targetReaches_uaToEquiv`. -/
theorem Conv.sourceReaches_uaToEquiv
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ proofTarget,
      RawStep.parStar sourceRaw (RawTerm.uaToEquiv proofTarget) ∧
      RawStep.parStar proofTerm proofTarget :=
  Conv.targetReaches_uaToEquiv (Conv.sym convertibility)

/-! ## Leaf canonical-head disjointness lemmas

If two distinct leaf canonical heads sit at the two ends of a
Conv, no common reduct can satisfy both inversions — `noConfusion`
refutes via ctor disjointness.

Each impossibility proof follows the same shape:
  1. `Conv.canonicalRaw` extracts the join `joinRaw`.
  2. `RawStep.parStar.<headLeft>_inv` forces `joinRaw = headLeft`.
  3. `RawStep.parStar.<headRight>_inv` forces `joinRaw = headRight`.
  4. `Eq.trans` produces `headLeft = headRight`.
  5. `nomatch` discharges via ctor disjointness (auto-generated
     noConfusion mechanism with motive inferred from goal).

The construction is symmetric in source/target — `Conv.sym` flips
the lemma, so we ship only one direction per unordered pair.  Used
in K12 fundamental-theorem closure to rule out impossible
canonical-canonical Conv pairs (e.g. when a Conv with one side a
canonical boolTrue can't have the other side a canonical
boolFalse). -/

/-- A `unit`-headed source and a `boolTrue`-headed target are
not convertible. -/
theorem Conv.unit_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqTrue

/-- A `unit`-headed source and a `boolFalse`-headed target are
not convertible. -/
theorem Conv.unit_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqFalse

/-- A `unit`-headed source and a `natZero`-headed target are
not convertible. -/
theorem Conv.unit_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqZero

/-- A `unit`-headed source and a `listNil`-headed target are
not convertible. -/
theorem Conv.unit_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqNil

/-- A `unit`-headed source and an `optionNone`-headed target are
not convertible. -/
theorem Conv.unit_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqNone

/-- A `boolTrue`-headed source and a `boolFalse`-headed target
are not convertible.  Most-used impossibility — closure for the
`boolElim` fundamental-theorem ι-firing path requires that a
boolTrue-shape Conv excludes the boolFalse branch and vice
versa. -/
theorem Conv.boolTrue_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqFalse

/-- A `boolTrue`-headed source and a `natZero`-headed target are
not convertible. -/
theorem Conv.boolTrue_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqZero

/-- A `boolFalse`-headed source and a `natZero`-headed target
are not convertible. -/
theorem Conv.boolFalse_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqZero

/-- A `natZero`-headed source and a `listNil`-headed target are
not convertible. -/
theorem Conv.natZero_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqZero.symm.trans joinEqNil

/-- A `natZero`-headed source and an `optionNone`-headed target
are not convertible. -/
theorem Conv.natZero_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqZero.symm.trans joinEqNone

/-- A `listNil`-headed source and an `optionNone`-headed target
are not convertible. -/
theorem Conv.listNil_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.listNil : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqNil.symm.trans joinEqNone

/-- A `boolTrue`-headed source and a `listNil`-headed target are
not convertible. -/
theorem Conv.boolTrue_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqNil

/-- A `boolFalse`-headed source and a `listNil`-headed target are
not convertible. -/
theorem Conv.boolFalse_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqNil

/-- A `boolTrue`-headed source and an `optionNone`-headed target
are not convertible. -/
theorem Conv.boolTrue_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqNone

/-- A `boolFalse`-headed source and an `optionNone`-headed target
are not convertible. -/
theorem Conv.boolFalse_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqNone

/-! ## Parameterized-leaf uniqueness lemmas

For parameterized leaves (`var P`, `universeCode N`) the
canonical-form propagation gives the same head structure on both
ends; the additional uniqueness lemma forces the inner data to
match.  Used in K12 fundamental theorem closure when both
endpoints are known to be at the same canonical-leaf head with
data and we need to derive data equality. -/

/-- Two `var`-headed convertible terms have equal positions. -/
theorem Conv.var_position_eq
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {position1 position2 : Fin scope}
    {sourceTerm : Term context sourceType
      (RawTerm.var position1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.var position2 : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    position1 = position2 := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEq1 : joinRaw = RawTerm.var position1 :=
    RawStep.parStar.var_inv sourceToJoin
  have joinEq2 : joinRaw = RawTerm.var position2 :=
    RawStep.parStar.var_inv targetToJoin
  have varEq : RawTerm.var position1 = RawTerm.var position2 :=
    joinEq1.symm.trans joinEq2
  injection varEq

/-- Two `universeCode`-headed convertible terms have equal inner
levels. -/
theorem Conv.universeCode_level_eq
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel1 innerLevel2 : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.universeCode innerLevel2 : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    innerLevel1 = innerLevel2 := by
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEq1 : joinRaw = RawTerm.universeCode innerLevel1 :=
    RawStep.parStar.universeCode_inv sourceToJoin
  have joinEq2 : joinRaw = RawTerm.universeCode innerLevel2 :=
    RawStep.parStar.universeCode_inv targetToJoin
  have codeEq :
      RawTerm.universeCode innerLevel1 = RawTerm.universeCode innerLevel2 :=
    joinEq1.symm.trans joinEq2
  injection codeEq

/-! ## Leaf-vs-compound disjointness

Extension of the iter 32 leaf-vs-leaf disjointness grid to the
case where one Conv side is a closed-leaf canonical head and the
other is a unary-compound canonical head (`natSucc`, `optionSome`,
`eitherInl`, `eitherInr`).  The pattern is the same — distinct
ctors at the join produce `nomatch` — but compound `*_inv` lemmas
return ∃ tuples instead of plain Eq, so we `obtain` the head
equality witness.

The most load-bearing entry is `Conv.natZero_ne_natSucc`, which
the K12 fundamental theorem's `natElim` case needs to rule out
convertibility between the zero branch's scrutinee and a non-zero
canonical Nat — closure of the ι-firing dispatch.  The remaining
five (`unit_ne_natSucc`, `boolTrue_ne_natSucc`, etc.) extend the
grid for completeness and document the disjointness regardless of
the specific scrutinee shape encountered downstream. -/

/-- A `unit`-headed source and a `natSucc`-headed target are not
convertible. -/
theorem Conv.unit_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqNatSucc

/-- A `boolTrue`-headed source and a `natSucc`-headed target are
not convertible. -/
theorem Conv.boolTrue_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqNatSucc

/-- A `boolFalse`-headed source and a `natSucc`-headed target are
not convertible. -/
theorem Conv.boolFalse_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqNatSucc

/-- A `natZero`-headed source and a `natSucc`-headed target are
not convertible.  LOAD-BEARING for K12 fundamental theorem's
`natElim` case — the ι-firing dispatch on a canonical Nat
scrutinee uses this to rule out the zero/non-zero ambiguity. -/
theorem Conv.natZero_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqZero.symm.trans joinEqNatSucc

/-- A `listNil`-headed source and a `natSucc`-headed target are
not convertible. -/
theorem Conv.listNil_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.listNil : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv sourceToJoin
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqNil.symm.trans joinEqNatSucc

/-- An `optionNone`-headed source and a `natSucc`-headed target
are not convertible. -/
theorem Conv.optionNone_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.optionNone : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv sourceToJoin
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqNone.symm.trans joinEqNatSucc

/-! ## Leaf-vs-optionSome disjointness

Same shape as the leaf-vs-natSucc grid above, with `optionSome` in
the compound role.  Load-bearing entry is
`Conv.optionNone_ne_optionSome`, used by K12 fundamental theorem's
`optionMatch` ι-firing dispatch to rule out the None/Some
ambiguity on a canonical Option scrutinee.  The remaining five
(`unit_ne_optionSome`, `boolTrue_ne_optionSome`, etc.) extend the
grid for completeness across the closed-leaf canonical heads. -/

/-- A `unit`-headed source and an `optionSome`-headed target are
not convertible. -/
theorem Conv.unit_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqOptionSome

/-- A `boolTrue`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.boolTrue_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqOptionSome

/-- A `boolFalse`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.boolFalse_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqOptionSome

/-- A `natZero`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.natZero_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqZero.symm.trans joinEqOptionSome

/-- A `listNil`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.listNil_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.listNil : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv sourceToJoin
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqNil.symm.trans joinEqOptionSome

/-- An `optionNone`-headed source and an `optionSome`-headed
target are not convertible.  LOAD-BEARING for K12 fundamental
theorem's `optionMatch` case — the ι-firing dispatch on a
canonical Option scrutinee uses this to rule out the None/Some
ambiguity. -/
theorem Conv.optionNone_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.optionNone : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv sourceToJoin
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqNone.symm.trans joinEqOptionSome

/-! ## Leaf-vs-eitherInl disjointness

Same pattern as leaf-vs-natSucc / leaf-vs-optionSome, with
`eitherInl` in the compound role.  Each lemma rules out
convertibility between a closed leaf canonical head and an Either
left injection.  Used in K12 fundamental theorem's `eitherMatch`
case alongside the eitherInr counterpart below to rule out
canonical-leaf scrutinee shapes that cannot fire the Left arm. -/

/-- A `unit`-headed source and an `eitherInl`-headed target are
not convertible. -/
theorem Conv.unit_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqEitherInl

/-- A `boolTrue`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.boolTrue_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqEitherInl

/-- A `boolFalse`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.boolFalse_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqEitherInl

/-- A `natZero`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.natZero_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqZero.symm.trans joinEqEitherInl

/-- A `listNil`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.listNil_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.listNil : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv sourceToJoin
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqNil.symm.trans joinEqEitherInl

/-- An `optionNone`-headed source and an `eitherInl`-headed
target are not convertible. -/
theorem Conv.optionNone_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.optionNone : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv sourceToJoin
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqNone.symm.trans joinEqEitherInl

/-! ## Leaf-vs-eitherInr disjointness

Companion grid to leaf-vs-eitherInl above, for the Right
injection.  Used in the eitherMatch case to rule out the canonical
leaf scrutinee shapes that cannot fire the Right arm.  Together
with the eitherInl grid above, completes the leaf-vs-{4 unary
compounds: natSucc, optionSome, eitherInl, eitherInr}
disjointness coverage. -/

/-- A `unit`-headed source and an `eitherInr`-headed target are
not convertible. -/
theorem Conv.unit_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqEitherInr

/-- A `boolTrue`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.boolTrue_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqEitherInr

/-- A `boolFalse`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.boolFalse_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqEitherInr

/-- A `natZero`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.natZero_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqZero.symm.trans joinEqEitherInr

/-- A `listNil`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.listNil_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.listNil : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv sourceToJoin
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqNil.symm.trans joinEqEitherInr

/-- An `optionNone`-headed source and an `eitherInr`-headed
target are not convertible. -/
theorem Conv.optionNone_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.optionNone : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv sourceToJoin
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqNone.symm.trans joinEqEitherInr

/-! ## Compound-vs-compound disjointness

The 6 unordered pairs over the 4 unary canonical compound heads
`{natSucc, optionSome, eitherInl, eitherInr}` — distinct
compound heads at the two Conv ends cannot share a join.  Both
sides require the ∃-tuple `obtain` from compound `*_inv` lemmas;
the distinct outer ctors then discharge via `nomatch`.

Most load-bearing entry is `Conv.eitherInl_ne_eitherInr` — used
by K12 fundamental theorem's `eitherMatch` case to rule out the
Left/Right ambiguity on a canonical Either scrutinee (parallel
to optionMatch's None/Some shipped in iter 34).  Together with
the leaf-vs-compound grid (iters 33-35), this completes the
unary-canonical disjointness matrix: 24 leaf×compound + 6
compound×compound = 30 pairs total. -/

/-- A `natSucc`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.natSucc_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.natSucc predecessor : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv sourceToJoin
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqNatSucc.symm.trans joinEqOptionSome

/-- A `natSucc`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.natSucc_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.natSucc predecessor : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv sourceToJoin
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqNatSucc.symm.trans joinEqEitherInl

/-- A `natSucc`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.natSucc_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.natSucc predecessor : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv sourceToJoin
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqNatSucc.symm.trans joinEqEitherInr

/-- An `optionSome`-headed source and an `eitherInl`-headed
target are not convertible. -/
theorem Conv.optionSome_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTermSrc valueTermTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionSome valueTermSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTermTgt : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv sourceToJoin
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqOptionSome.symm.trans joinEqEitherInl

/-- An `optionSome`-headed source and an `eitherInr`-headed
target are not convertible. -/
theorem Conv.optionSome_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTermSrc valueTermTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionSome valueTermSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTermTgt : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv sourceToJoin
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqOptionSome.symm.trans joinEqEitherInr

/-- An `eitherInl`-headed source and an `eitherInr`-headed target
are not convertible.  LOAD-BEARING for K12 fundamental theorem's
`eitherMatch` case — the ι-firing dispatch on a canonical Either
scrutinee uses this to rule out the Left/Right ambiguity. -/
theorem Conv.eitherInl_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTermSrc valueTermTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInl valueTermSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTermTgt : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv sourceToJoin
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqEitherInl.symm.trans joinEqEitherInr

/-! ### Same-head compatibility lemmas (positive matrix half)

The disjointness lemmas above answer "when do two canonical heads
not match."  The compatibility lemmas below answer the dual:
"when they DO match, what does that tell us about the inner
subterms?"  Each produces a common raw reduct for the inner
parameter on both sides — the raw-level analog of typed Conv on
the inner subterm.  K12 fundamental theorem's ι-firing dispatch
on a canonical scrutinee uses these to descend into the canonical
witness once the head has been pinned down by the disjointness
matrix.

The pattern is the obvious dual: extract both `parStar` chains,
invert under the matching head's `_inv` lemma, identify the two
inner joins via constructor injectivity, then transport one chain
along that equation. -/

/-- Two `natSucc`-headed canonically-convertible terms have a
common raw reduct for their predecessor subterms. -/
theorem Conv.natSucc_compatibility
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessorSrc predecessorTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.natSucc predecessorSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessorTgt : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ predecessorJoin : RawTerm scope,
      RawStep.parStar predecessorSrc predecessorJoin ∧
      RawStep.parStar predecessorTgt predecessorJoin := by
  obtain ⟨_, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨predecessorJoinSrc, joinEqSrc, sourceInner⟩ :=
    RawStep.parStar.natSucc_inv sourceToJoin
  obtain ⟨predecessorJoinTgt, joinEqTgt, targetInner⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  have predecessorJoinEq :
      predecessorJoinSrc = predecessorJoinTgt :=
    RawTerm.natSucc.inj (joinEqSrc.symm.trans joinEqTgt)
  exact ⟨predecessorJoinTgt,
    predecessorJoinEq ▸ sourceInner, targetInner⟩

/-- Two `optionSome`-headed canonically-convertible terms have a
common raw reduct for their payload subterms. -/
theorem Conv.optionSome_compatibility
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueSrc valueTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionSome valueSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTgt : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ valueJoin : RawTerm scope,
      RawStep.parStar valueSrc valueJoin ∧
      RawStep.parStar valueTgt valueJoin := by
  obtain ⟨_, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨valueJoinSrc, joinEqSrc, sourceInner⟩ :=
    RawStep.parStar.optionSome_inv sourceToJoin
  obtain ⟨valueJoinTgt, joinEqTgt, targetInner⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  have valueJoinEq : valueJoinSrc = valueJoinTgt :=
    RawTerm.optionSome.inj (joinEqSrc.symm.trans joinEqTgt)
  exact ⟨valueJoinTgt, valueJoinEq ▸ sourceInner, targetInner⟩

/-- Two `eitherInl`-headed canonically-convertible terms have a
common raw reduct for their left-payload subterms.  LOAD-BEARING
for K12 fundamental theorem's `eitherMatch` Left-canonical ι
firing — once disjointness rules out Right, this compatibility
lemma extracts the canonical Left witness. -/
theorem Conv.eitherInl_compatibility
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueSrc valueTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInl valueSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTgt : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ valueJoin : RawTerm scope,
      RawStep.parStar valueSrc valueJoin ∧
      RawStep.parStar valueTgt valueJoin := by
  obtain ⟨_, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨valueJoinSrc, joinEqSrc, sourceInner⟩ :=
    RawStep.parStar.eitherInl_inv sourceToJoin
  obtain ⟨valueJoinTgt, joinEqTgt, targetInner⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  have valueJoinEq : valueJoinSrc = valueJoinTgt :=
    RawTerm.eitherInl.inj (joinEqSrc.symm.trans joinEqTgt)
  exact ⟨valueJoinTgt, valueJoinEq ▸ sourceInner, targetInner⟩

/-- Two `eitherInr`-headed canonically-convertible terms have a
common raw reduct for their right-payload subterms.  LOAD-BEARING
for K12 fundamental theorem's `eitherMatch` Right-canonical ι
firing — once disjointness rules out Left, this compatibility
lemma extracts the canonical Right witness. -/
theorem Conv.eitherInr_compatibility
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueSrc valueTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInr valueSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTgt : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ valueJoin : RawTerm scope,
      RawStep.parStar valueSrc valueJoin ∧
      RawStep.parStar valueTgt valueJoin := by
  obtain ⟨_, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨valueJoinSrc, joinEqSrc, sourceInner⟩ :=
    RawStep.parStar.eitherInr_inv sourceToJoin
  obtain ⟨valueJoinTgt, joinEqTgt, targetInner⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  have valueJoinEq : valueJoinSrc = valueJoinTgt :=
    RawTerm.eitherInr.inj (joinEqSrc.symm.trans joinEqTgt)
  exact ⟨valueJoinTgt, valueJoinEq ▸ sourceInner, targetInner⟩

/-! ### `listCons` canonical-head disjointness (binary compound head)

`listCons` is the first binary canonical head added to the
matrix.  It is load-bearing for K12 fundamental theorem's
`listElim` ι-firing dispatch — once the scrutinee canonicalizes
to a list, the recursor needs to know whether it lands on
`listNil` (covered by `Conv.listNil_ne_*` above) or on
`listCons head tail`, which these lemmas formally rule out for
every non-list canonical head.

The pattern matches iters 33-35 leaf-vs-compound shape; the only
structural difference is `listCons` has TWO inner parameters
(head + tail) rather than one, so the inv-obtain destructures
`⟨_, _, joinEqListCons, _, _⟩` instead of `⟨_, joinEq, _⟩`.
Otherwise the `nomatch` refutation is identical.

This iteration ships the 6 leaf-vs-listCons pairs; the 4
unary-compound-vs-listCons pairs ship in the next iteration. -/

/-- A `unit`-headed source and a `listCons`-headed target are
not convertible. -/
theorem Conv.unit_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqListCons

/-- A `boolTrue`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.boolTrue_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqListCons

/-- A `boolFalse`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.boolFalse_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqListCons

/-- A `natZero`-headed source and a `listCons`-headed target are
not convertible. -/
theorem Conv.natZero_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqZero.symm.trans joinEqListCons

/-- A `listNil`-headed source and a `listCons`-headed target are
not convertible.  LOAD-BEARING for K12 fundamental theorem's
`listElim` ι-firing dispatch on a canonical list scrutinee —
this rules out the nil-vs-cons ambiguity once the scrutinee has
canonicalized. -/
theorem Conv.listNil_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.listNil : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqNil.symm.trans joinEqListCons

/-- An `optionNone`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.optionNone_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.optionNone : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqNone.symm.trans joinEqListCons

/-! ### `listCons` vs unary compounds (4 disjointness + 1 compatibility)

Completes the `listCons` canonical-head row: 4 disjointness
pairs against the unary compound heads {natSucc, optionSome,
eitherInl, eitherInr} plus the same-head compatibility lemma.
Together with the 6 leaf-vs-listCons pairs above, this finishes
the 10-cell listCons disjointness matrix and adds positive
extraction for the listCons-vs-listCons case. -/

/-- A `natSucc`-headed source and a `listCons`-headed target are
not convertible. -/
theorem Conv.natSucc_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.natSucc predecessor : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqNatSucc.symm.trans joinEqListCons

/-- An `optionSome`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.optionSome_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionSome valueTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqOptionSome.symm.trans joinEqListCons

/-- An `eitherInl`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.eitherInl_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInl valueTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqEitherInl.symm.trans joinEqListCons

/-- An `eitherInr`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.eitherInr_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInr valueTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv sourceToJoin
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqEitherInr.symm.trans joinEqListCons

/-- Two `listCons`-headed canonically-convertible terms have a
common raw reduct for both the head subterm and the tail subterm.
LOAD-BEARING for K12 fundamental theorem's `listElim` cons-arm ι
firing — once disjointness rules out nil, this compatibility
lemma extracts the canonical head + tail witnesses for the
recursive call.  The proof mirrors the unary compatibility
template (iter 37), with `RawTerm.listCons.inj` producing the
pair `headJoinEq ∧ tailJoinEq` consumed by two `▸`-rewrites. -/
theorem Conv.listCons_compatibility
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headSrc tailSrc headTgt tailTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCons headSrc tailSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTgt tailTgt : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ headJoin tailJoin : RawTerm scope,
      RawStep.parStar headSrc headJoin ∧
      RawStep.parStar headTgt headJoin ∧
      RawStep.parStar tailSrc tailJoin ∧
      RawStep.parStar tailTgt tailJoin := by
  obtain ⟨_, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨headJoinSrc, tailJoinSrc, joinEqSrc,
      headSrcInner, tailSrcInner⟩ :=
    RawStep.parStar.listCons_inv sourceToJoin
  obtain ⟨headJoinTgt, tailJoinTgt, joinEqTgt,
      headTgtInner, tailTgtInner⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  have ⟨headJoinEq, tailJoinEq⟩ :
      headJoinSrc = headJoinTgt ∧ tailJoinSrc = tailJoinTgt :=
    RawTerm.listCons.inj (joinEqSrc.symm.trans joinEqTgt)
  exact ⟨headJoinTgt, tailJoinTgt,
    headJoinEq ▸ headSrcInner, headTgtInner,
    tailJoinEq ▸ tailSrcInner, tailTgtInner⟩

/-! ### `pair` canonical-head disjointness (binary Σ-intro head)

`pair` is the second binary canonical head added to the matrix.
It is load-bearing for K12 fundamental theorem's β-redex case
on `fst` / `snd` (K12.21) — once a Σ-typed scrutinee
canonicalizes, the projection's β rule fires against `pair head
tail`, and these disjointness lemmas formally rule out the case
where canonicalization yields a non-pair head.

Proof shape identical to iters 33-39's leaf-vs-compound pattern:
the leaf-side inv returns plain Eq, the pair-side inv returns
an existential triple `⟨_, _, joinEqPair, _, _⟩` whose only
relevant component is the head-shape equation joinEqPair.  The
`nomatch` refutation chains the two equations through .symm /
.trans, producing an impossible `RawTerm.<leaf> = RawTerm.pair _ _`.

This iter ships the 6 leaf-vs-pair pairs; the 4 unary-compound-
vs-pair + listCons-vs-pair + pair compatibility ship in the
next iteration. -/

/-- A `unit`-headed source and a `pair`-headed target are not
convertible. -/
theorem Conv.unit_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqPair

/-- A `boolTrue`-headed source and a `pair`-headed target are not
convertible. -/
theorem Conv.boolTrue_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqPair

/-- A `boolFalse`-headed source and a `pair`-headed target are not
convertible. -/
theorem Conv.boolFalse_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqPair

/-- A `natZero`-headed source and a `pair`-headed target are not
convertible. -/
theorem Conv.natZero_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqZero.symm.trans joinEqPair

/-- A `listNil`-headed source and a `pair`-headed target are not
convertible. -/
theorem Conv.listNil_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.listNil : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqNil.symm.trans joinEqPair

/-- An `optionNone`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.optionNone_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.optionNone : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqNone.symm.trans joinEqPair

/-! ### `pair` vs unary compounds + binary `listCons` + compatibility

Completes the `pair` canonical-head row started in iter 40.
Adds the 4 unary-compound-vs-pair disjointness pairs, the first
binary-vs-binary disjointness (listCons-vs-pair), and the
same-head pair compatibility extraction lemma.

The binary-vs-binary case (`Conv.listCons_ne_pair`) is novel —
both inv lemmas return existential triples, so both `obtain`
destructures discard 4 components each.  The refutation logic
is unchanged: chain the two head-shape equations through
.symm/.trans, then `nomatch` refutes the impossible
`RawTerm.listCons _ _ = RawTerm.pair _ _`. -/

/-- A `natSucc`-headed source and a `pair`-headed target are not
convertible. -/
theorem Conv.natSucc_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.natSucc predecessor : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqNatSucc.symm.trans joinEqPair

/-- An `optionSome`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.optionSome_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionSome valueTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqOptionSome.symm.trans joinEqPair

/-- An `eitherInl`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.eitherInl_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInl valueTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqEitherInl.symm.trans joinEqPair

/-- An `eitherInr`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.eitherInr_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInr valueTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqEitherInr.symm.trans joinEqPair

/-- A `listCons`-headed source and a `pair`-headed target are
not convertible.  First binary-vs-binary disjointness pair —
both sides yield existential-triple inv-obtain patterns, but
the refutation logic via `nomatch` on the inter-ctor equation
remains the same as unary cases. -/
theorem Conv.listCons_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqListCons.symm.trans joinEqPair

/-- Two `pair`-headed canonically-convertible terms have a
common raw reduct for both the first and second components.
LOAD-BEARING for K12 fundamental theorem's β-redex cases on
`fst` / `snd` (K12.21) — once a Σ-typed scrutinee canonicalizes
to `pair head tail`, this compatibility lemma extracts the
canonical first/second witnesses for the projection β to apply.
Mirrors `listCons_compatibility` (iter 39) — same binary-arity
template with `RawTerm.pair.inj` producing `firstEq ∧ secondEq`. -/
theorem Conv.pair_compatibility
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstSrc secondSrc firstTgt secondTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pair firstSrc secondSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstTgt secondTgt : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ firstJoin secondJoin : RawTerm scope,
      RawStep.parStar firstSrc firstJoin ∧
      RawStep.parStar firstTgt firstJoin ∧
      RawStep.parStar secondSrc secondJoin ∧
      RawStep.parStar secondTgt secondJoin := by
  obtain ⟨_, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨firstJoinSrc, secondJoinSrc, joinEqSrc,
      firstSrcInner, secondSrcInner⟩ :=
    RawStep.parStar.pair_inv sourceToJoin
  obtain ⟨firstJoinTgt, secondJoinTgt, joinEqTgt,
      firstTgtInner, secondTgtInner⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  have ⟨firstJoinEq, secondJoinEq⟩ :
      firstJoinSrc = firstJoinTgt ∧ secondJoinSrc = secondJoinTgt :=
    RawTerm.pair.inj (joinEqSrc.symm.trans joinEqTgt)
  exact ⟨firstJoinTgt, secondJoinTgt,
    firstJoinEq ▸ firstSrcInner, firstTgtInner,
    secondJoinEq ▸ secondSrcInner, secondTgtInner⟩

/-! ### `refl` canonical-head disjointness (HoTT identity intro)

`refl` is the third canonical compound head added to the matrix.
It is the unary witness-carrying intro for HoTT identity types
(`Ty.id`, `Ty.oeq`, `Ty.idStrict`).  Although K12.23 HOTT cases
shipped without consuming this row, the lemmas remain useful for
K12.24 cubical cases and downstream NbE work (K13.17 quote at
identity types must canonicalize to `refl` shape).

Proof shape identical to the unary-compound template (iters 33,
34) — `refl_inv` returns `∃ witnessTarget, target = RawTerm.refl
witnessTarget ∧ RawStep.parStar witness witnessTarget`, same
3-component existential as natSucc/optionSome.

This iter ships the 6 leaf-vs-refl pairs; iter 43 will close
the row with 4 unary-compound-vs-refl + 2 binary-vs-refl +
refl compatibility. -/

/-- A `unit`-headed source and a `refl`-headed target are not
convertible. -/
theorem Conv.unit_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.unit : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqUnit.symm.trans joinEqRefl

/-- A `boolTrue`-headed source and a `refl`-headed target are not
convertible. -/
theorem Conv.boolTrue_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolTrue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqTrue.symm.trans joinEqRefl

/-- A `boolFalse`-headed source and a `refl`-headed target are
not convertible. -/
theorem Conv.boolFalse_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.boolFalse : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqFalse.symm.trans joinEqRefl

/-- A `natZero`-headed source and a `refl`-headed target are not
convertible. -/
theorem Conv.natZero_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.natZero : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqZero.symm.trans joinEqRefl

/-- A `listNil`-headed source and a `refl`-headed target are not
convertible. -/
theorem Conv.listNil_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.listNil : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqNil.symm.trans joinEqRefl

/-- An `optionNone`-headed source and a `refl`-headed target are
not convertible. -/
theorem Conv.optionNone_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType (RawTerm.optionNone : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqNone.symm.trans joinEqRefl

/-! ### `refl` row closure: unary compounds + binary + compatibility

Closes the `refl` canonical-head row started in iter 42.  Ships
the 4 unary-compound-vs-refl pairs, the 2 binary-vs-refl pairs
(listCons-vs-refl, pair-vs-refl), and the same-head refl
compatibility extraction lemma.  Together with iter 42's 6 leaf
pairs, the row is now a complete 13-cell matrix slice. -/

/-- A `natSucc`-headed source and a `refl`-headed target are not
convertible. -/
theorem Conv.natSucc_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.natSucc predecessor : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqNatSucc, _⟩ :=
    RawStep.parStar.natSucc_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqNatSucc.symm.trans joinEqRefl

/-- An `optionSome`-headed source and a `refl`-headed target are
not convertible. -/
theorem Conv.optionSome_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionSome valueTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOptionSome, _⟩ :=
    RawStep.parStar.optionSome_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqOptionSome.symm.trans joinEqRefl

/-- An `eitherInl`-headed source and a `refl`-headed target are
not convertible. -/
theorem Conv.eitherInl_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInl valueTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqEitherInl, _⟩ :=
    RawStep.parStar.eitherInl_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqEitherInl.symm.trans joinEqRefl

/-- An `eitherInr`-headed source and a `refl`-headed target are
not convertible. -/
theorem Conv.eitherInr_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherInr valueTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqEitherInr, _⟩ :=
    RawStep.parStar.eitherInr_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqEitherInr.symm.trans joinEqRefl

/-- A `listCons`-headed source and a `refl`-headed target are
not convertible.  Second binary-vs-unary disjointness pair —
listCons inv returns the 5-component existential, refl inv
returns the 3-component existential, both inter-ctor refuted by
`nomatch`. -/
theorem Conv.listCons_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqListCons, _, _⟩ :=
    RawStep.parStar.listCons_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqListCons.symm.trans joinEqRefl

/-- A `pair`-headed source and a `refl`-headed target are not
convertible.  Third binary-vs-unary disjointness pair. -/
theorem Conv.pair_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstValue secondValue witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pair firstValue secondValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqPair.symm.trans joinEqRefl

/-- Two `refl`-headed canonically-convertible terms have a
common raw reduct for their witness subterms.  Useful for the
HOTT idJ/oeqJ ι-firing dispatch: once an identity-type
scrutinee canonicalizes to `refl witness`, the J β rule fires
against the canonical witness, and this lemma extracts the
common reduct for downstream reasoning.  Same shape as
natSucc_compatibility (iter 37) — unary RawTerm.refl.inj
produces a single witnessEq consumed by one ▸-rewrite. -/
theorem Conv.refl_compatibility
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessSrc witnessTgt : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refl witnessSrc : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTgt : RawTerm scope)}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ witnessJoin : RawTerm scope,
      RawStep.parStar witnessSrc witnessJoin ∧
      RawStep.parStar witnessTgt witnessJoin := by
  obtain ⟨_, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨witnessJoinSrc, joinEqSrc, sourceInner⟩ :=
    RawStep.parStar.refl_inv sourceToJoin
  obtain ⟨witnessJoinTgt, joinEqTgt, targetInner⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  have witnessJoinEq : witnessJoinSrc = witnessJoinTgt :=
    RawTerm.refl.inj (joinEqSrc.symm.trans joinEqTgt)
  exact ⟨witnessJoinTgt, witnessJoinEq ▸ sourceInner, targetInner⟩

/-- A `interval0`-headed source and a `unit`-headed target are not
convertible. -/
theorem Conv.interval0_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqUnit

/-- A `interval0`-headed source and a `boolTrue`-headed target are not
convertible. -/
theorem Conv.interval0_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqTrue

/-- A `interval0`-headed source and a `boolFalse`-headed target are
not convertible. -/
theorem Conv.interval0_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqFalse

/-- A `interval0`-headed source and a `natZero`-headed target are not
convertible. -/
theorem Conv.interval0_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqZero

/-- A `interval0`-headed source and a `listNil`-headed target are not
convertible. -/
theorem Conv.interval0_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqNil

/-- A `interval0`-headed source and a `optionNone`-headed target are
not convertible. -/
theorem Conv.interval0_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqNone

/-- A `interval0`-headed source and a `natSucc`-headed target are not
convertible. -/
theorem Conv.interval0_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqSucc

/-- A `interval0`-headed source and a `optionSome`-headed target are
not convertible. -/
theorem Conv.interval0_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqSome

/-- A `interval0`-headed source and a `eitherInl`-headed target are
not convertible. -/
theorem Conv.interval0_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqInl

/-- A `interval0`-headed source and a `eitherInr`-headed target are
not convertible. -/
theorem Conv.interval0_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqInr

/-- A `interval0`-headed source and a `listCons`-headed target are
not convertible.  Cubical-leaf vs binary disjointness. -/
theorem Conv.interval0_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqCons

/-- A `interval0`-headed source and a `pair`-headed target are not
convertible.  Cubical-leaf vs binary disjointness. -/
theorem Conv.interval0_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqPair

/-- A `interval0`-headed source and a `refl`-headed target are not
convertible.  Cubical-leaf vs HOTT witness-carrier disjointness. -/
theorem Conv.interval0_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval0 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqRefl

/-- A `interval1`-headed source and a `unit`-headed target are not
convertible. -/
theorem Conv.interval1_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqUnit

/-- A `interval1`-headed source and a `boolTrue`-headed target are not
convertible. -/
theorem Conv.interval1_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqTrue

/-- A `interval1`-headed source and a `boolFalse`-headed target are
not convertible. -/
theorem Conv.interval1_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqFalse

/-- A `interval1`-headed source and a `natZero`-headed target are not
convertible. -/
theorem Conv.interval1_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqZero

/-- A `interval1`-headed source and a `listNil`-headed target are not
convertible. -/
theorem Conv.interval1_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqNil

/-- A `interval1`-headed source and a `optionNone`-headed target are
not convertible. -/
theorem Conv.interval1_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqNone

/-- A `interval1`-headed source and a `interval0`-headed target are
not convertible.  Cubical-leaf vs cubical-leaf — the two endpoints
of the interval are distinct values. -/
theorem Conv.interval1_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqOne.symm.trans joinEqZero

/-- A `interval1`-headed source and a `natSucc`-headed target are not
convertible. -/
theorem Conv.interval1_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqSucc

/-- A `interval1`-headed source and a `optionSome`-headed target are
not convertible. -/
theorem Conv.interval1_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqSome

/-- A `interval1`-headed source and a `eitherInl`-headed target are
not convertible. -/
theorem Conv.interval1_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqInl

/-- A `interval1`-headed source and a `eitherInr`-headed target are
not convertible. -/
theorem Conv.interval1_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqInr

/-- A `interval1`-headed source and a `listCons`-headed target are
not convertible.  Cubical-leaf vs binary disjointness. -/
theorem Conv.interval1_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqCons

/-- A `interval1`-headed source and a `pair`-headed target are not
convertible.  Cubical-leaf vs binary disjointness. -/
theorem Conv.interval1_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqPair

/-- A `interval1`-headed source and a `refl`-headed target are not
convertible.  Cubical-leaf vs HOTT witness-carrier disjointness. -/
theorem Conv.interval1_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.interval1 : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqInterval : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqInterval.symm.trans joinEqRefl

/-- A `universeCode`-headed source and a `unit`-headed target are not
convertible.  Opens the type-code-leaf row of the canonical-head
matrix: `universeCode` represents Type universes, structurally
distinct from data and cubical leaves. -/
theorem Conv.universeCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqUnit

/-- A `universeCode`-headed source and a `boolTrue`-headed target are
not convertible. -/
theorem Conv.universeCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqTrue

/-- A `universeCode`-headed source and a `boolFalse`-headed target
are not convertible. -/
theorem Conv.universeCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqFalse

/-- A `universeCode`-headed source and a `natZero`-headed target are
not convertible. -/
theorem Conv.universeCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqZero

/-- A `universeCode`-headed source and a `listNil`-headed target are
not convertible. -/
theorem Conv.universeCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqNil

/-- A `universeCode`-headed source and a `optionNone`-headed target
are not convertible. -/
theorem Conv.universeCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqNone

/-- A `universeCode`-headed source and a `interval0`-headed target
are not convertible.  Type-universe vs cubical-endpoint
disjointness. -/
theorem Conv.universeCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqZero

/-- A `universeCode`-headed source and a `interval1`-headed target
are not convertible.  Type-universe vs cubical-endpoint
disjointness. -/
theorem Conv.universeCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqOne

/-- A `universeCode`-headed source and a `natSucc`-headed target are
not convertible.  Type-universe vs unary-compound data-leaf
disjointness. -/
theorem Conv.universeCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqSucc

/-- A `universeCode`-headed source and a `optionSome`-headed target
are not convertible.  Type-universe vs unary-compound option-leaf
disjointness. -/
theorem Conv.universeCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqSome

/-- A `universeCode`-headed source and a `eitherInl`-headed target
are not convertible.  Type-universe vs unary-compound either-leaf
disjointness. -/
theorem Conv.universeCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqInl

/-- A `universeCode`-headed source and a `eitherInr`-headed target
are not convertible.  Type-universe vs unary-compound either-leaf
disjointness. -/
theorem Conv.universeCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqInr

/-- A `universeCode`-headed source and a `listCons`-headed target
are not convertible.  Type-universe vs binary-compound list-leaf
disjointness. -/
theorem Conv.universeCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqCons

/-- A `universeCode`-headed source and a `pair`-headed target are
not convertible.  Type-universe vs binary-compound product-leaf
disjointness. -/
theorem Conv.universeCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqPair

/-- A `universeCode`-headed source and a `refl`-headed target are
not convertible.  Type-universe vs HOTT witness-carrier
disjointness. -/
theorem Conv.universeCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerLevel : Nat}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.universeCode innerLevel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  have joinEqCode : joinRaw = RawTerm.universeCode innerLevel :=
    RawStep.parStar.universeCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqCode.symm.trans joinEqRefl

/-- A `listCode`-headed source and a `unit`-headed target are not
convertible.  Opens the type-code unary-payload row of the
canonical-head matrix: `listCode` is the type-code for the
list-of type former, distinct from data leaves. -/
theorem Conv.listCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqUnit

/-- A `listCode`-headed source and a `boolTrue`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.listCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqTrue

/-- A `listCode`-headed source and a `boolFalse`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.listCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqFalse

/-- A `listCode`-headed source and a `natZero`-headed target are not
convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.listCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqZero

/-- A `listCode`-headed source and a `listNil`-headed target are not
convertible.  Type-code vs data-leaf disjointness — the `listCode`
type-code is structurally distinct from the value-level `listNil`. -/
theorem Conv.listCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqNil

/-- A `listCode`-headed source and a `optionNone`-headed target are
not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.listCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqNone

/-- A `listCode`-headed source and a `interval0`-headed target are
not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.listCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqZero

/-- A `listCode`-headed source and a `interval1`-headed target are
not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.listCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqOne

/-- A `listCode`-headed source and a `natSucc`-headed target are
not convertible.  Type-code vs unary-compound data-leaf
disjointness. -/
theorem Conv.listCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqSucc

/-- A `listCode`-headed source and a `optionSome`-headed target are
not convertible.  Type-code vs unary-compound option-leaf
disjointness. -/
theorem Conv.listCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqSome

/-- A `listCode`-headed source and a `eitherInl`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.listCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqInl

/-- A `listCode`-headed source and a `eitherInr`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.listCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqInr

/-- A `listCode`-headed source and a `listCons`-headed target are
not convertible.  Type-code vs binary-compound list-leaf
disjointness — the type-code `listCode` distinct from the value
constructor `listCons` even though both relate to list type
former. -/
theorem Conv.listCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqCons

/-- A `listCode`-headed source and a `pair`-headed target are not
convertible.  Type-code vs binary-compound product-leaf
disjointness. -/
theorem Conv.listCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqPair

/-- A `listCode`-headed source and a `refl`-headed target are not
convertible.  Type-code vs HOTT witness-carrier disjointness. -/
theorem Conv.listCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.listCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqList, _⟩ :=
    RawStep.parStar.listCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqList.symm.trans joinEqRefl

/-- A `optionCode`-headed source and a `unit`-headed target are not
convertible.  Opens the optionCode row of the canonical-head
matrix: `optionCode` is the type-code for the option-of type
former, sibling to listCode at the type-code level. -/
theorem Conv.optionCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqUnit

/-- A `optionCode`-headed source and a `boolTrue`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.optionCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqTrue

/-- A `optionCode`-headed source and a `boolFalse`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.optionCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqFalse

/-- A `optionCode`-headed source and a `natZero`-headed target are
not convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.optionCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqZero

/-- A `optionCode`-headed source and a `listNil`-headed target are
not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.optionCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqNil

/-- A `optionCode`-headed source and a `optionNone`-headed target
are not convertible.  Type-code vs data-leaf disjointness — the
type-code `optionCode` is structurally distinct from the value
constructor `optionNone`. -/
theorem Conv.optionCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqNone

/-- A `optionCode`-headed source and a `interval0`-headed target are
not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.optionCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqZero

/-- A `optionCode`-headed source and a `interval1`-headed target are
not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.optionCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqOne

/-- A `optionCode`-headed source and a `natSucc`-headed target are
not convertible.  Type-code vs unary-compound data-leaf
disjointness. -/
theorem Conv.optionCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqSucc

/-- A `optionCode`-headed source and a `optionSome`-headed target
are not convertible.  Type-code vs unary-compound option-leaf
disjointness — the type-code `optionCode` distinct from the
value constructor `optionSome` even though both relate to the
option type former. -/
theorem Conv.optionCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqSome

/-- A `optionCode`-headed source and a `eitherInl`-headed target
are not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.optionCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqInl

/-- A `optionCode`-headed source and a `eitherInr`-headed target
are not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.optionCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqInr

/-- A `optionCode`-headed source and a `listCons`-headed target are
not convertible.  Type-code vs binary-compound list-leaf
disjointness. -/
theorem Conv.optionCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqCons

/-- A `optionCode`-headed source and a `pair`-headed target are not
convertible.  Type-code vs binary-compound product-leaf
disjointness. -/
theorem Conv.optionCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqPair

/-- A `optionCode`-headed source and a `refl`-headed target are not
convertible.  Type-code vs HOTT witness-carrier disjointness. -/
theorem Conv.optionCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {elementCode witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.optionCode elementCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOption, _⟩ :=
    RawStep.parStar.optionCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqOption.symm.trans joinEqRefl

/-- A `arrowCode`-headed source and a `unit`-headed target are not
convertible.  Opens the binary type-code row of the canonical-head
matrix: `arrowCode` is the type-code for the simple-arrow type
former, sibling to `piTyCode` (dependent Π) at the type-code
level. -/
theorem Conv.arrowCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqUnit

/-- A `arrowCode`-headed source and a `boolTrue`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.arrowCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqTrue

/-- A `arrowCode`-headed source and a `boolFalse`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.arrowCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqFalse

/-- A `arrowCode`-headed source and a `natZero`-headed target are
not convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.arrowCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqZero

/-- A `arrowCode`-headed source and a `listNil`-headed target are
not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.arrowCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqNil

/-- A `arrowCode`-headed source and a `optionNone`-headed target are
not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.arrowCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqNone

/-- A `arrowCode`-headed source and a `interval0`-headed target are
not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.arrowCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqZero

/-- A `arrowCode`-headed source and a `interval1`-headed target are
not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.arrowCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqOne

/-- A `arrowCode`-headed source and a `natSucc`-headed target are
not convertible.  Type-code vs unary-compound data-leaf
disjointness. -/
theorem Conv.arrowCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqSucc

/-- A `arrowCode`-headed source and a `optionSome`-headed target
are not convertible.  Type-code vs unary-compound option-leaf
disjointness. -/
theorem Conv.arrowCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqSome

/-- A `arrowCode`-headed source and a `eitherInl`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.arrowCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqInl

/-- A `arrowCode`-headed source and a `eitherInr`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.arrowCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqInr

/-- A `arrowCode`-headed source and a `listCons`-headed target are
not convertible.  Type-code vs binary-compound list-leaf
disjointness. -/
theorem Conv.arrowCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqCons

/-- A `arrowCode`-headed source and a `pair`-headed target are not
convertible.  Type-code vs binary-compound product-leaf
disjointness. -/
theorem Conv.arrowCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqPair

/-- A `arrowCode`-headed source and a `refl`-headed target are not
convertible.  Type-code vs HOTT witness-carrier disjointness. -/
theorem Conv.arrowCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqRefl

/-- A `piTyCode`-headed source and a `unit`-headed target are not
convertible.  Opens the binder-binding type-code row of the
canonical-head matrix: `piTyCode` is the type-code for the
dependent-Π type former with its codomain in extended scope. -/
theorem Conv.piTyCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqUnit

/-- A `piTyCode`-headed source and a `boolTrue`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.piTyCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqTrue

/-- A `piTyCode`-headed source and a `boolFalse`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.piTyCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqFalse

/-- A `piTyCode`-headed source and a `natZero`-headed target are
not convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.piTyCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqZero

/-- A `piTyCode`-headed source and a `listNil`-headed target are
not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.piTyCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqNil

/-- A `piTyCode`-headed source and a `optionNone`-headed target are
not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.piTyCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqNone

/-- A `piTyCode`-headed source and a `interval0`-headed target are
not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.piTyCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqZero

/-- A `piTyCode`-headed source and a `interval1`-headed target are
not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.piTyCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqOne

/-- A `piTyCode`-headed source and a `natSucc`-headed target are
not convertible.  Type-code vs unary-compound data-leaf
disjointness. -/
theorem Conv.piTyCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqSucc

/-- A `piTyCode`-headed source and a `optionSome`-headed target are
not convertible.  Type-code vs unary-compound option-leaf
disjointness. -/
theorem Conv.piTyCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqSome

/-- A `piTyCode`-headed source and a `eitherInl`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.piTyCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqInl

/-- A `piTyCode`-headed source and a `eitherInr`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.piTyCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqInr

/-- A `piTyCode`-headed source and a `listCons`-headed target are
not convertible.  Type-code vs binary-compound list-leaf
disjointness. -/
theorem Conv.piTyCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqCons

/-- A `piTyCode`-headed source and a `pair`-headed target are not
convertible.  Type-code vs binary-compound product-leaf
disjointness. -/
theorem Conv.piTyCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqPair

/-- A `piTyCode`-headed source and a `refl`-headed target are not
convertible.  Type-code vs HOTT witness-carrier disjointness. -/
theorem Conv.piTyCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.piTyCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPi, _, _⟩ :=
    RawStep.parStar.piTyCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqPi.symm.trans joinEqRefl

/-- A `sigmaTyCode`-headed source and a `unit`-headed target are
not convertible.  Opens the dependent-Σ type-code row of the
canonical-head matrix: `sigmaTyCode` is the type-code for the
dependent-Σ type former with its second component in extended
scope, sibling to `piTyCode`. -/
theorem Conv.sigmaTyCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqUnit

/-- A `sigmaTyCode`-headed source and a `boolTrue`-headed target
are not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.sigmaTyCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqTrue

/-- A `sigmaTyCode`-headed source and a `boolFalse`-headed target
are not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.sigmaTyCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqFalse

/-- A `sigmaTyCode`-headed source and a `natZero`-headed target
are not convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.sigmaTyCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqZero

/-- A `sigmaTyCode`-headed source and a `listNil`-headed target
are not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.sigmaTyCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqNil

/-- A `sigmaTyCode`-headed source and a `optionNone`-headed target
are not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.sigmaTyCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqNone

/-- A `sigmaTyCode`-headed source and a `interval0`-headed target
are not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.sigmaTyCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqZero

/-- A `sigmaTyCode`-headed source and a `interval1`-headed target
are not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.sigmaTyCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqOne

/-- A `sigmaTyCode`-headed source and a `natSucc`-headed target
are not convertible.  Type-code vs unary-compound data-leaf
disjointness. -/
theorem Conv.sigmaTyCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqSucc

/-- A `sigmaTyCode`-headed source and a `optionSome`-headed target
are not convertible.  Type-code vs unary-compound option-leaf
disjointness. -/
theorem Conv.sigmaTyCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqSome

/-- A `sigmaTyCode`-headed source and a `eitherInl`-headed target
are not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.sigmaTyCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqInl

/-- A `sigmaTyCode`-headed source and a `eitherInr`-headed target
are not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.sigmaTyCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqInr

/-- A `sigmaTyCode`-headed source and a `listCons`-headed target
are not convertible.  Type-code vs binary-compound list-leaf
disjointness. -/
theorem Conv.sigmaTyCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqCons

/-- A `sigmaTyCode`-headed source and a `pair`-headed target are
not convertible.  Type-code vs binary-compound product-leaf
disjointness — sigmaTyCode is the type-code, pair is the value-
level constructor of the corresponding Σ type. -/
theorem Conv.sigmaTyCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqPair

/-- A `sigmaTyCode`-headed source and a `refl`-headed target are
not convertible.  Type-code vs HOTT witness-carrier disjointness. -/
theorem Conv.sigmaTyCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sigmaTyCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSigma, _, _⟩ :=
    RawStep.parStar.sigmaTyCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqSigma.symm.trans joinEqRefl

/-- A `productCode`-headed source and a `unit`-headed target are
not convertible.  Opens the non-dependent-product type-code row
of the canonical-head matrix: `productCode` is the flat-binary
type-code for the non-dependent product type former. -/
theorem Conv.productCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqUnit

/-- A `productCode`-headed source and a `boolTrue`-headed target
are not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.productCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqTrue

/-- A `productCode`-headed source and a `boolFalse`-headed target
are not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.productCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqFalse

/-- A `productCode`-headed source and a `natZero`-headed target
are not convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.productCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqZero

/-- A `productCode`-headed source and a `listNil`-headed target
are not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.productCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqNil

/-- A `productCode`-headed source and a `optionNone`-headed target
are not convertible.  Type-code vs data-leaf disjointness. -/
theorem Conv.productCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqNone

/-- A `productCode`-headed source and a `interval0`-headed target
are not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.productCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqZero

/-- A `productCode`-headed source and a `interval1`-headed target
are not convertible.  Type-code vs cubical-endpoint disjointness. -/
theorem Conv.productCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqOne

/-- A `productCode`-headed source and a `natSucc`-headed target are
not convertible.  Type-code vs unary-compound data-leaf
disjointness. -/
theorem Conv.productCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqSucc

/-- A `productCode`-headed source and a `optionSome`-headed target
are not convertible.  Type-code vs unary-compound option-leaf
disjointness. -/
theorem Conv.productCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqSome

/-- A `productCode`-headed source and a `eitherInl`-headed target
are not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.productCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqInl

/-- A `productCode`-headed source and a `eitherInr`-headed target
are not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.productCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqInr

/-- A `productCode`-headed source and a `listCons`-headed target are
not convertible.  Type-code vs binary-compound list-leaf
disjointness. -/
theorem Conv.productCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqCons

/-- A `productCode`-headed source and a `pair`-headed target are not
convertible.  Type-code vs binary-compound product-leaf disjointness
— `productCode` is the type-code for the non-dependent product type
former and `pair` is its value-level constructor; they live at
different syntactic strata. -/
theorem Conv.productCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqPair

/-- A `productCode`-headed source and a `refl`-headed target are not
convertible.  Type-code vs HOTT witness-carrier disjointness. -/
theorem Conv.productCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.productCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqProduct, _, _⟩ :=
    RawStep.parStar.productCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqProduct.symm.trans joinEqRefl

/-- A `sumCode`-headed source and a `unit`-headed target are not
convertible.  Opens the sum-type-code row of the canonical-head
matrix: `sumCode` is the flat-binary type-code for the disjoint-
union type former, dual to `productCode`. -/
theorem Conv.sumCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqUnit

/-- A `sumCode`-headed source and a `boolTrue`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.sumCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqTrue

/-- A `sumCode`-headed source and a `boolFalse`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.sumCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqFalse

/-- A `sumCode`-headed source and a `natZero`-headed target are
not convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.sumCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqZero

/-- A `sumCode`-headed source and a `listNil`-headed target are
not convertible.  Type-code vs nullary-list-leaf disjointness. -/
theorem Conv.sumCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqNil

/-- A `sumCode`-headed source and a `optionNone`-headed target are
not convertible.  Type-code vs nullary-option-leaf disjointness. -/
theorem Conv.sumCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqNone

/-- A `sumCode`-headed source and a `interval0`-headed target are
not convertible.  Type-code vs cubical-interval-leaf disjointness. -/
theorem Conv.sumCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqZero

/-- A `sumCode`-headed source and a `interval1`-headed target are
not convertible.  Type-code vs cubical-interval-leaf disjointness. -/
theorem Conv.sumCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqOne

/-- A `sumCode`-headed source and a `natSucc`-headed target are
not convertible.  Type-code vs unary-compound data-leaf
disjointness. -/
theorem Conv.sumCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqSucc

/-- A `sumCode`-headed source and a `optionSome`-headed target are
not convertible.  Type-code vs unary-compound option-leaf
disjointness. -/
theorem Conv.sumCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqSome

/-- A `sumCode`-headed source and a `eitherInl`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness — `sumCode` is the type-code for the disjoint-union
type former and `eitherInl` is its left-injection value-level
constructor; they live at different syntactic strata. -/
theorem Conv.sumCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqInl

/-- A `sumCode`-headed source and a `eitherInr`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness — `sumCode` is the type-code, `eitherInr` is the
right-injection value-level constructor. -/
theorem Conv.sumCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqInr

/-- A `sumCode`-headed source and a `listCons`-headed target are
not convertible.  Type-code vs binary-compound list-leaf
disjointness. -/
theorem Conv.sumCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqCons

/-- A `sumCode`-headed source and a `pair`-headed target are not
convertible.  Type-code vs binary-compound product-leaf
disjointness — `sumCode` is the type-code for the disjoint-union
type former and `pair` is the value-level constructor for the
non-dependent product type; they live at different syntactic
strata. -/
theorem Conv.sumCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqPair

/-- A `sumCode`-headed source and a `refl`-headed target are not
convertible.  Type-code vs HOTT witness-carrier disjointness. -/
theorem Conv.sumCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sumCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSum, _, _⟩ :=
    RawStep.parStar.sumCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqSum.symm.trans joinEqRefl

/-- A `eitherCode`-headed source and a `unit`-headed target are not
convertible.  Opens the either-type-code row of the canonical-head
matrix: `eitherCode` is the flat-binary type-code for the tagged
disjoint-union type former, dual to `sumCode` at the parametric
level. -/
theorem Conv.eitherCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqUnit

/-- A `eitherCode`-headed source and a `boolTrue`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.eitherCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqTrue

/-- A `eitherCode`-headed source and a `boolFalse`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.eitherCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqFalse

/-- A `eitherCode`-headed source and a `natZero`-headed target are
not convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.eitherCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqZero

/-- A `eitherCode`-headed source and a `listNil`-headed target are
not convertible.  Type-code vs nullary-list-leaf disjointness. -/
theorem Conv.eitherCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqNil

/-- A `eitherCode`-headed source and a `optionNone`-headed target are
not convertible.  Type-code vs nullary-option-leaf disjointness. -/
theorem Conv.eitherCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqNone

/-- A `eitherCode`-headed source and a `interval0`-headed target are
not convertible.  Type-code vs cubical-interval-leaf disjointness. -/
theorem Conv.eitherCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqZero

/-- A `eitherCode`-headed source and a `interval1`-headed target are
not convertible.  Type-code vs cubical-interval-leaf disjointness. -/
theorem Conv.eitherCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqOne

/-- A `eitherCode`-headed source and a `natSucc`-headed target are
not convertible.  Type-code vs unary-compound data-leaf
disjointness. -/
theorem Conv.eitherCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqSucc

/-- A `eitherCode`-headed source and a `optionSome`-headed target
are not convertible.  Type-code vs unary-compound option-leaf
disjointness. -/
theorem Conv.eitherCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqSome

/-- A `eitherCode`-headed source and a `eitherInl`-headed target
are not convertible.  Type-code vs unary-compound either-leaf
disjointness — `eitherCode` is the type-code for the tagged
disjoint-union type former and `eitherInl` is its left-injection
value-level constructor; they live at different syntactic strata. -/
theorem Conv.eitherCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqInl

/-- A `eitherCode`-headed source and a `eitherInr`-headed target
are not convertible.  Type-code vs unary-compound either-leaf
disjointness — `eitherCode` is the type-code, `eitherInr` is the
right-injection value-level constructor. -/
theorem Conv.eitherCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqInr

/-- A `eitherCode`-headed source and a `listCons`-headed target are
not convertible.  Type-code vs binary-compound list-leaf
disjointness. -/
theorem Conv.eitherCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqCons

/-- A `eitherCode`-headed source and a `pair`-headed target are not
convertible.  Type-code vs binary-compound product-leaf
disjointness — `eitherCode` is the type-code for the tagged
disjoint-union type former and `pair` is the value-level
constructor for the non-dependent product type. -/
theorem Conv.eitherCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqPair

/-- A `eitherCode`-headed source and a `refl`-headed target are not
convertible.  Type-code vs HOTT witness-carrier disjointness. -/
theorem Conv.eitherCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.eitherCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqEither.symm.trans joinEqRefl

/-- A `equivCode`-headed source and a `unit`-headed target are not
convertible.  Opens the equivalence-type-code row of the
canonical-head matrix: `equivCode` is the flat-binary type-code
for the HOTT equivalence type former (parameterized by source and
target types). -/
theorem Conv.equivCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqUnit

/-- A `equivCode`-headed source and a `boolTrue`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.equivCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqTrue

/-- A `equivCode`-headed source and a `boolFalse`-headed target are
not convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.equivCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqFalse

/-- A `equivCode`-headed source and a `natZero`-headed target are
not convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.equivCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqZero

/-- A `equivCode`-headed source and a `listNil`-headed target are
not convertible.  Type-code vs nullary-list-leaf disjointness. -/
theorem Conv.equivCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqNil

/-- A `equivCode`-headed source and a `optionNone`-headed target are
not convertible.  Type-code vs nullary-option-leaf disjointness. -/
theorem Conv.equivCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqNone

/-- A `equivCode`-headed source and a `interval0`-headed target are
not convertible.  Type-code vs cubical-interval-leaf disjointness. -/
theorem Conv.equivCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqZero

/-- A `equivCode`-headed source and a `interval1`-headed target are
not convertible.  Type-code vs cubical-interval-leaf disjointness. -/
theorem Conv.equivCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqOne

/-- A `equivCode`-headed source and a `natSucc`-headed target are
not convertible.  Type-code vs unary-compound data-leaf
disjointness. -/
theorem Conv.equivCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqSucc

/-- A `equivCode`-headed source and a `optionSome`-headed target are
not convertible.  Type-code vs unary-compound option-leaf
disjointness. -/
theorem Conv.equivCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqSome

/-- A `equivCode`-headed source and a `eitherInl`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.equivCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqInl

/-- A `equivCode`-headed source and a `eitherInr`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.equivCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqInr

/-- A `equivCode`-headed source and a `listCons`-headed target are
not convertible.  Type-code vs binary-compound list-leaf
disjointness. -/
theorem Conv.equivCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqCons

/-- A `equivCode`-headed source and a `pair`-headed target are not
convertible.  Type-code vs binary-compound product-leaf
disjointness — `equivCode` is the type-code for the HOTT
equivalence type former and `pair` is the value-level constructor
for the non-dependent product type. -/
theorem Conv.equivCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqPair

/-- A `equivCode`-headed source and a `refl`-headed target are not
convertible.  Type-code vs HOTT witness-carrier disjointness —
notable because `equivCode` and `refl` both inhabit the HOTT
fragment but at different syntactic strata (type-code vs proof
witness for the underlying identity type). -/
theorem Conv.equivCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstCode secondCode : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCode firstCode secondCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqRefl

/-- A `idCode`-headed source and a `unit`-headed target are not
convertible.  Opens the identity-type-code row of the canonical-
head matrix: `idCode` is the TERNARY type-code for the HOTT
identity type former (carrying a type code plus left and right
endpoint codes).  First non-binary canonical head — destructure
expands to ⟨_, _, _, joinEqId, _, _, _⟩ from ternary_inv_helper. -/
theorem Conv.idCode_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqUnit

/-- A `idCode`-headed source and a `boolTrue`-headed target are not
convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.idCode_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqTrue

/-- A `idCode`-headed source and a `boolFalse`-headed target are not
convertible.  Type-code vs boolean-leaf disjointness. -/
theorem Conv.idCode_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqFalse

/-- A `idCode`-headed source and a `natZero`-headed target are not
convertible.  Type-code vs nat-leaf disjointness. -/
theorem Conv.idCode_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqZero

/-- A `idCode`-headed source and a `listNil`-headed target are not
convertible.  Type-code vs nullary-list-leaf disjointness. -/
theorem Conv.idCode_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqNil

/-- A `idCode`-headed source and a `optionNone`-headed target are
not convertible.  Type-code vs nullary-option-leaf disjointness. -/
theorem Conv.idCode_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqNone

/-- A `idCode`-headed source and a `interval0`-headed target are not
convertible.  Type-code vs cubical-interval-leaf disjointness. -/
theorem Conv.idCode_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqZero

/-- A `idCode`-headed source and a `interval1`-headed target are not
convertible.  Type-code vs cubical-interval-leaf disjointness. -/
theorem Conv.idCode_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqOne

/-- A `idCode`-headed source and a `natSucc`-headed target are not
convertible.  Type-code vs unary-compound data-leaf disjointness
(ternary source destructure). -/
theorem Conv.idCode_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqSucc

/-- A `idCode`-headed source and a `optionSome`-headed target are
not convertible.  Type-code vs unary-compound option-leaf
disjointness. -/
theorem Conv.idCode_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqSome

/-- A `idCode`-headed source and a `eitherInl`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.idCode_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqInl

/-- A `idCode`-headed source and a `eitherInr`-headed target are
not convertible.  Type-code vs unary-compound either-leaf
disjointness. -/
theorem Conv.idCode_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqInr

/-- A `idCode`-headed source and a `listCons`-headed target are not
convertible.  Type-code vs binary-compound list-leaf disjointness. -/
theorem Conv.idCode_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqCons

/-- A `idCode`-headed source and a `pair`-headed target are not
convertible.  Type-code vs binary-compound product-leaf
disjointness. -/
theorem Conv.idCode_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqPair

/-- A `idCode`-headed source and a `refl`-headed target are not
convertible.  Type-code vs HOTT witness-carrier disjointness —
notable because `idCode` and `refl` both inhabit the HOTT identity-
type fragment but at orthogonal syntactic strata: `idCode` is the
type-code carrying the underlying type and endpoints, while `refl`
is the canonical proof witness of identity. -/
theorem Conv.idCode_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {typeCode leftCode rightCode : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idCode typeCode leftCode rightCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqId, _, _, _⟩ :=
    RawStep.parStar.idCode_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqId.symm.trans joinEqRefl

/-! ## glueIntro row of canonical-head disjointness matrix

`RawTerm.glueIntro baseValue partialValue` is the cubical `Glue`
type's introduction form — carries a base-type value and a partial
equiv-witness on the boundary face.  Admitting it to the matrix
extends canonical-head disjointness into the cubical fragment
beyond just the interval-leaf endpoints `interval0` / `interval1`.

Binary source destructure (5-binder shape):
  `obtain ⟨_, _, joinEqGlue, _, _⟩ :=
     RawStep.parStar.glueIntro_inv sourceToJoin` -/

/-- A `glueIntro`-headed source and a `unit`-headed target are not
convertible.  Cubical introduction vs unit-leaf disjointness. -/
theorem Conv.glueIntro_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqUnit

/-- A `glueIntro`-headed source and a `boolTrue`-headed target are
not convertible. -/
theorem Conv.glueIntro_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqTrue

/-- A `glueIntro`-headed source and a `boolFalse`-headed target are
not convertible. -/
theorem Conv.glueIntro_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqFalse

/-- A `glueIntro`-headed source and a `natZero`-headed target are
not convertible. -/
theorem Conv.glueIntro_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqZero

/-- A `glueIntro`-headed source and a `listNil`-headed target are
not convertible. -/
theorem Conv.glueIntro_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqNil

/-- A `glueIntro`-headed source and an `optionNone`-headed target are
not convertible. -/
theorem Conv.glueIntro_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqNone

/-- A `glueIntro`-headed source and an `interval0`-headed target are
not convertible.  Cubical introduction vs cubical-leaf disjointness —
notable since both inhabit the cubical fragment but at orthogonal
strata. -/
theorem Conv.glueIntro_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqZero

/-- A `glueIntro`-headed source and an `interval1`-headed target are
not convertible. -/
theorem Conv.glueIntro_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqOne

/-- A `glueIntro`-headed source and a `natSucc`-headed target are
not convertible.  Cubical introduction vs unary-compound nat-leaf
disjointness. -/
theorem Conv.glueIntro_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqSucc

/-- A `glueIntro`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.glueIntro_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqSome

/-- A `glueIntro`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.glueIntro_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqInl

/-- A `glueIntro`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.glueIntro_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqInr

/-- A `glueIntro`-headed source and a `listCons`-headed target are
not convertible.  Cubical introduction vs binary-compound list-leaf
disjointness. -/
theorem Conv.glueIntro_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqCons

/-- A `glueIntro`-headed source and a `pair`-headed target are not
convertible.  Cubical introduction vs binary-compound product-leaf
disjointness — both ctors are binary introductions but inhabit
orthogonal type formers (`Glue` for `pair` would be Σ). -/
theorem Conv.glueIntro_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqPair

/-- A `glueIntro`-headed source and a `refl`-headed target are not
convertible.  Cubical introduction vs HOTT identity-witness
disjointness — distinct ctors at orthogonal type-theoretic strata. -/
theorem Conv.glueIntro_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseValue partialValue : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.glueIntro baseValue partialValue : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqGlue.symm.trans joinEqRefl

/-! ## pathCompose row of canonical-head disjointness matrix

`RawTerm.pathCompose leftPath rightPath` is the HoTT-family path
composition operator — combines two path witnesses (proofs of
identity) at consecutive endpoints into one composite witness.
Admitting it to the matrix extends canonical-head disjointness
into the HoTT path-witness fragment beyond just the identity
introduction `refl`.

Binary source destructure (5-binder shape, mirrors glueIntro):
  `obtain ⟨_, _, joinEqPath, _, _⟩ :=
     RawStep.parStar.pathCompose_inv sourceToJoin` -/

/-- A `pathCompose`-headed source and a `unit`-headed target are
not convertible.  HoTT path composition vs unit-leaf disjointness. -/
theorem Conv.pathCompose_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqUnit

/-- A `pathCompose`-headed source and a `boolTrue`-headed target
are not convertible. -/
theorem Conv.pathCompose_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqTrue

/-- A `pathCompose`-headed source and a `boolFalse`-headed target
are not convertible. -/
theorem Conv.pathCompose_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqFalse

/-- A `pathCompose`-headed source and a `natZero`-headed target are
not convertible. -/
theorem Conv.pathCompose_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqZero

/-- A `pathCompose`-headed source and a `listNil`-headed target are
not convertible. -/
theorem Conv.pathCompose_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqNil

/-- A `pathCompose`-headed source and an `optionNone`-headed target
are not convertible. -/
theorem Conv.pathCompose_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqNone

/-- A `pathCompose`-headed source and an `interval0`-headed target
are not convertible.  HoTT path composition vs cubical-leaf
disjointness — notable since both inhabit the path/cubical theory
but at orthogonal strata: pathCompose composes proof witnesses,
while interval0 is a dimension-0 endpoint inhabiting the cube. -/
theorem Conv.pathCompose_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqZero

/-- A `pathCompose`-headed source and an `interval1`-headed target
are not convertible. -/
theorem Conv.pathCompose_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqOne

/-- A `pathCompose`-headed source and a `natSucc`-headed target are
not convertible. -/
theorem Conv.pathCompose_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqSucc

/-- A `pathCompose`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.pathCompose_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqSome

/-- A `pathCompose`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.pathCompose_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqInl

/-- A `pathCompose`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.pathCompose_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqInr

/-- A `pathCompose`-headed source and a `listCons`-headed target are
not convertible. -/
theorem Conv.pathCompose_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqCons

/-- A `pathCompose`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.pathCompose_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqPair

/-- A `pathCompose`-headed source and a `refl`-headed target are
not convertible.  HoTT path composition vs HoTT identity-witness
disjointness — both inhabit the HoTT identity fragment but at
orthogonal strata: pathCompose is binary witness composition,
while refl is the unary identity introduction. -/
theorem Conv.pathCompose_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftPath rightPath : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.pathCompose leftPath rightPath : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPath, _, _⟩ :=
    RawStep.parStar.pathCompose_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqPath.symm.trans joinEqRefl

/-! ## oeqTrans row of canonical-head disjointness matrix

`RawTerm.oeqTrans firstProof secondProof` is the HoTT observational-
equality transitivity operator — combines two observational-equality
proofs at consecutive endpoints into one composite proof.  This is
the inner-mode analog of `pathCompose`: pathCompose composes path
witnesses, oeqTrans composes observational-equality witnesses.

Binary source destructure (5-binder shape, mirrors pathCompose):
  `obtain ⟨_, _, joinEqOeq, _, _⟩ :=
     RawStep.parStar.oeqTrans_inv sourceToJoin` -/

/-- A `oeqTrans`-headed source and a `unit`-headed target are not
convertible.  HoTT observational transitivity vs unit-leaf
disjointness. -/
theorem Conv.oeqTrans_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqUnit

/-- A `oeqTrans`-headed source and a `boolTrue`-headed target are
not convertible. -/
theorem Conv.oeqTrans_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqTrue

/-- A `oeqTrans`-headed source and a `boolFalse`-headed target are
not convertible. -/
theorem Conv.oeqTrans_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqFalse

/-- A `oeqTrans`-headed source and a `natZero`-headed target are
not convertible. -/
theorem Conv.oeqTrans_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqZero

/-- A `oeqTrans`-headed source and a `listNil`-headed target are
not convertible. -/
theorem Conv.oeqTrans_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqNil

/-- A `oeqTrans`-headed source and an `optionNone`-headed target
are not convertible. -/
theorem Conv.oeqTrans_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqNone

/-- A `oeqTrans`-headed source and an `interval0`-headed target
are not convertible. -/
theorem Conv.oeqTrans_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqZero

/-- A `oeqTrans`-headed source and an `interval1`-headed target
are not convertible. -/
theorem Conv.oeqTrans_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqOne

/-- A `oeqTrans`-headed source and a `natSucc`-headed target are
not convertible. -/
theorem Conv.oeqTrans_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqSucc

/-- A `oeqTrans`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.oeqTrans_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqSome

/-- A `oeqTrans`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.oeqTrans_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqInl

/-- A `oeqTrans`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.oeqTrans_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqInr

/-- A `oeqTrans`-headed source and a `listCons`-headed target are
not convertible. -/
theorem Conv.oeqTrans_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqCons

/-- A `oeqTrans`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.oeqTrans_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqPair

/-- A `oeqTrans`-headed source and a `refl`-headed target are
not convertible.  HoTT observational-equality transitivity vs HoTT
identity-witness disjointness — both inhabit the HoTT identity
fragment but at orthogonal strata: oeqTrans is binary observational
witness composition (inner mode), while refl is the unary identity
introduction. -/
theorem Conv.oeqTrans_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstProof secondProof : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqTrans firstProof secondProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeq, _, _⟩ :=
    RawStep.parStar.oeqTrans_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqOeq.symm.trans joinEqRefl

/-! ## equivCompose row of canonical-head disjointness matrix

`RawTerm.equivCompose firstEquiv secondEquiv` is the HoTT
equivalence-composition operator — combines two type equivalences
at consecutive endpoints into one composite equivalence.  This is
the equivalence-stratum analog of `pathCompose` (path stratum) and
`oeqTrans` (observational-equality stratum), extending HoTT-fragment
matrix coverage to the equivalence layer.

Binary source destructure (5-binder shape, mirrors pathCompose /
oeqTrans):
  `obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
     RawStep.parStar.equivCompose_inv sourceToJoin` -/

/-- An `equivCompose`-headed source and a `unit`-headed target are
not convertible.  HoTT equivalence composition vs unit-leaf
disjointness. -/
theorem Conv.equivCompose_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqUnit

/-- An `equivCompose`-headed source and a `boolTrue`-headed target
are not convertible. -/
theorem Conv.equivCompose_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqTrue

/-- An `equivCompose`-headed source and a `boolFalse`-headed target
are not convertible. -/
theorem Conv.equivCompose_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqFalse

/-- An `equivCompose`-headed source and a `natZero`-headed target
are not convertible. -/
theorem Conv.equivCompose_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqZero

/-- An `equivCompose`-headed source and a `listNil`-headed target
are not convertible. -/
theorem Conv.equivCompose_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqNil

/-- An `equivCompose`-headed source and an `optionNone`-headed
target are not convertible. -/
theorem Conv.equivCompose_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqNone

/-- An `equivCompose`-headed source and an `interval0`-headed target
are not convertible. -/
theorem Conv.equivCompose_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqZero

/-- An `equivCompose`-headed source and an `interval1`-headed target
are not convertible. -/
theorem Conv.equivCompose_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqOne

/-- An `equivCompose`-headed source and a `natSucc`-headed target
are not convertible. -/
theorem Conv.equivCompose_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqSucc

/-- An `equivCompose`-headed source and an `optionSome`-headed
target are not convertible. -/
theorem Conv.equivCompose_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqSome

/-- An `equivCompose`-headed source and an `eitherInl`-headed
target are not convertible. -/
theorem Conv.equivCompose_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqInl

/-- An `equivCompose`-headed source and an `eitherInr`-headed
target are not convertible. -/
theorem Conv.equivCompose_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqInr

/-- An `equivCompose`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.equivCompose_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqCons

/-- An `equivCompose`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.equivCompose_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqPair

/-- An `equivCompose`-headed source and a `refl`-headed target are
not convertible.  HoTT equivalence composition vs HoTT identity-
witness disjointness — equivCompose lives in the equivalence
stratum, while refl is the identity introduction.  The three
HoTT-fragment row cross-strata terms (pathCompose / oeqTrans /
equivCompose) all disjoin from refl at orthogonal strata. -/
theorem Conv.equivCompose_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquiv, _, _⟩ :=
    RawStep.parStar.equivCompose_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqEquiv.symm.trans joinEqRefl

/-! ## intervalOpp row of canonical-head disjointness matrix

`RawTerm.intervalOpp intervalTerm` is the cubical interval opposite
(also called involution or negation): swaps the two endpoints of an
interval term.  This is the first unary-source row in the cubical-
interval stratum, complementing the existing closed-leaf coverage
(interval0 and interval1 are already canonical leaves in every prior
row's target column).

Unary source destructure (3-binder shape):
  `obtain ⟨_, joinEqOpp, _⟩ :=
     RawStep.parStar.intervalOpp_inv sourceToJoin` -/

/-- An `intervalOpp`-headed source and a `unit`-headed target are
not convertible. -/
theorem Conv.intervalOpp_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqUnit

/-- An `intervalOpp`-headed source and a `boolTrue`-headed target
are not convertible. -/
theorem Conv.intervalOpp_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqTrue

/-- An `intervalOpp`-headed source and a `boolFalse`-headed target
are not convertible. -/
theorem Conv.intervalOpp_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqFalse

/-- An `intervalOpp`-headed source and a `natZero`-headed target
are not convertible. -/
theorem Conv.intervalOpp_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqZero

/-- An `intervalOpp`-headed source and a `listNil`-headed target
are not convertible. -/
theorem Conv.intervalOpp_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqNil

/-- An `intervalOpp`-headed source and an `optionNone`-headed
target are not convertible. -/
theorem Conv.intervalOpp_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqNone

/-- An `intervalOpp`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum cubical: the involution applied
to a generic interval term never normalises to the endpoint without
β-reducing the inner term to interval1. -/
theorem Conv.intervalOpp_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqZero

/-- An `intervalOpp`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum cubical: the involution applied
to a generic interval term never normalises to the endpoint without
β-reducing the inner term to interval0. -/
theorem Conv.intervalOpp_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqOne

/-- An `intervalOpp`-headed source and a `natSucc`-headed target
are not convertible. -/
theorem Conv.intervalOpp_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqSucc

/-- An `intervalOpp`-headed source and an `optionSome`-headed
target are not convertible. -/
theorem Conv.intervalOpp_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqSome

/-- An `intervalOpp`-headed source and an `eitherInl`-headed
target are not convertible. -/
theorem Conv.intervalOpp_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqInl

/-- An `intervalOpp`-headed source and an `eitherInr`-headed
target are not convertible. -/
theorem Conv.intervalOpp_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqInr

/-- An `intervalOpp`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.intervalOpp_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqCons

/-- An `intervalOpp`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.intervalOpp_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqPair

/-- An `intervalOpp`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum cubical-vs-HoTT-identity: the
interval involution operates on the cubical interval, while refl
is the HoTT identity-type introduction; these inhabit fully
orthogonal type strata. -/
theorem Conv.intervalOpp_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {intervalTerm : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalOpp intervalTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOpp, _⟩ :=
    RawStep.parStar.intervalOpp_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqOpp.symm.trans joinEqRefl

/-! ## intervalMeet row of canonical-head disjointness matrix

`RawTerm.intervalMeet leftInterval rightInterval` is the cubical
interval minimum / meet operator (also called interval ∧):
combines two interval terms into the pointwise minimum.  This is
the binary-source companion of intervalOpp (unary), extending the
cubical-interval stratum.

Binary source destructure (5-binder shape, mirrors pathCompose):
  `obtain ⟨_, _, joinEqMeet, _, _⟩ :=
     RawStep.parStar.intervalMeet_inv sourceToJoin` -/

/-- An `intervalMeet`-headed source and a `unit`-headed target are
not convertible. -/
theorem Conv.intervalMeet_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqUnit

/-- An `intervalMeet`-headed source and a `boolTrue`-headed target
are not convertible. -/
theorem Conv.intervalMeet_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqTrue

/-- An `intervalMeet`-headed source and a `boolFalse`-headed target
are not convertible. -/
theorem Conv.intervalMeet_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqFalse

/-- An `intervalMeet`-headed source and a `natZero`-headed target
are not convertible. -/
theorem Conv.intervalMeet_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqZero

/-- An `intervalMeet`-headed source and a `listNil`-headed target
are not convertible. -/
theorem Conv.intervalMeet_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqNil

/-- An `intervalMeet`-headed source and an `optionNone`-headed
target are not convertible. -/
theorem Conv.intervalMeet_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqNone

/-- An `intervalMeet`-headed source and an `interval0`-headed
target are not convertible.  Cross-stratum cubical: the meet
operator preserves head through every parallel chain (no β-rule
collapsing meet to a canonical endpoint at the current kernel
state), while interval0 is a canonical leaf. -/
theorem Conv.intervalMeet_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqZero

/-- An `intervalMeet`-headed source and an `interval1`-headed
target are not convertible.  Cross-stratum cubical: same argument
as `intervalMeet_ne_interval0` — head is preserved through every
parallel chain, while interval1 is a canonical leaf. -/
theorem Conv.intervalMeet_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqOne

/-- An `intervalMeet`-headed source and a `natSucc`-headed target
are not convertible. -/
theorem Conv.intervalMeet_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqSucc

/-- An `intervalMeet`-headed source and an `optionSome`-headed
target are not convertible. -/
theorem Conv.intervalMeet_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqSome

/-- An `intervalMeet`-headed source and an `eitherInl`-headed
target are not convertible. -/
theorem Conv.intervalMeet_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqInl

/-- An `intervalMeet`-headed source and an `eitherInr`-headed
target are not convertible. -/
theorem Conv.intervalMeet_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqInr

/-- An `intervalMeet`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.intervalMeet_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqCons

/-- An `intervalMeet`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.intervalMeet_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqPair

/-- An `intervalMeet`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum cubical-vs-HoTT-identity: the
interval meet operates in the cubical-interval stratum, while
refl is the HoTT identity-type introduction. -/
theorem Conv.intervalMeet_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalMeet leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqMeet, _, _⟩ :=
    RawStep.parStar.intervalMeet_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqMeet.symm.trans joinEqRefl

/-! ### `intervalJoin` row — cubical-interval lattice join operator

The `intervalJoin` head is the cubical-interval ∨ (lattice join) on
the interval `I`.  No current `Step.par` rule reduces
`intervalJoin x y` to a non-Join canonical head, so the head is
preserved through every parallel chain.  Together with
`intervalMeet` (lattice ∧) and `intervalOpp` (involution), the row
completes the Heyting-algebra operator triple for the cubical
interval stratum at the canonical-head disjointness matrix.

Binary source destructure follows the
`RawStep.parStar.intervalJoin_inv` 5-binder pattern:
  `obtain ⟨_, _, joinEqJoin, _, _⟩ := RawStep.parStar.intervalJoin_inv sourceToJoin` -/

/-- An `intervalJoin`-headed source and a `unit`-headed target are
not convertible. -/
theorem Conv.intervalJoin_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqUnit

/-- An `intervalJoin`-headed source and a `boolTrue`-headed target
are not convertible. -/
theorem Conv.intervalJoin_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqTrue

/-- An `intervalJoin`-headed source and a `boolFalse`-headed target
are not convertible. -/
theorem Conv.intervalJoin_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqFalse

/-- An `intervalJoin`-headed source and a `natZero`-headed target
are not convertible. -/
theorem Conv.intervalJoin_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqZero

/-- An `intervalJoin`-headed source and a `listNil`-headed target
are not convertible. -/
theorem Conv.intervalJoin_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqNil

/-- An `intervalJoin`-headed source and an `optionNone`-headed
target are not convertible. -/
theorem Conv.intervalJoin_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqNone

/-- An `intervalJoin`-headed source and an `interval0`-headed
target are not convertible.  Cross-stratum cubical: the join
operator preserves head through every parallel chain (no β-rule
collapsing join to a canonical endpoint at the current kernel
state), while interval0 is a canonical leaf. -/
theorem Conv.intervalJoin_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqZero

/-- An `intervalJoin`-headed source and an `interval1`-headed
target are not convertible.  Cross-stratum cubical: same argument
as `intervalJoin_ne_interval0` — head is preserved through every
parallel chain, while interval1 is a canonical leaf. -/
theorem Conv.intervalJoin_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqOne

/-- An `intervalJoin`-headed source and a `natSucc`-headed target
are not convertible. -/
theorem Conv.intervalJoin_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqSucc

/-- An `intervalJoin`-headed source and an `optionSome`-headed
target are not convertible. -/
theorem Conv.intervalJoin_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqSome

/-- An `intervalJoin`-headed source and an `eitherInl`-headed
target are not convertible. -/
theorem Conv.intervalJoin_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqInl

/-- An `intervalJoin`-headed source and an `eitherInr`-headed
target are not convertible. -/
theorem Conv.intervalJoin_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqInr

/-- An `intervalJoin`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.intervalJoin_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqCons

/-- An `intervalJoin`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.intervalJoin_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqPair

/-- An `intervalJoin`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum cubical-vs-HoTT-identity: the
interval join operates in the cubical-interval stratum, while
refl is the HoTT identity-type introduction. -/
theorem Conv.intervalJoin_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {leftInterval rightInterval : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.intervalJoin leftInterval rightInterval : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqJoin, _, _⟩ :=
    RawStep.parStar.intervalJoin_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqJoin.symm.trans joinEqRefl

/-! ### `uaToEquiv` row — HoTT univalence-to-equivalence converter

The `uaToEquiv` head wraps a univalence proof to obtain an
equivalence.  It is unary at the raw level (one component proof
sub-term), and no current `Step.par` rule β-reduces
`uaToEquiv proof` to a non-uaToEquiv canonical head — the
non-disjunctive `RawStep.parStar.uaToEquiv_inv` lemma at
`RawParStarCong.lean:2228` confirms the head is preserved through
every parallel chain.

Source destructure follows the 3-binder unary pattern:
  `obtain ⟨_, joinEqUa, _⟩ := RawStep.parStar.uaToEquiv_inv sourceToJoin`

Opening this row brings the HoTT equivalence stratum to three
source-head rows ({oeqTrans, equivCompose, uaToEquiv}). -/

/-- A `uaToEquiv`-headed source and a `unit`-headed target are
not convertible. -/
theorem Conv.uaToEquiv_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqUnit

/-- A `uaToEquiv`-headed source and a `boolTrue`-headed target
are not convertible. -/
theorem Conv.uaToEquiv_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqTrue

/-- A `uaToEquiv`-headed source and a `boolFalse`-headed target
are not convertible. -/
theorem Conv.uaToEquiv_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqFalse

/-- A `uaToEquiv`-headed source and a `natZero`-headed target
are not convertible. -/
theorem Conv.uaToEquiv_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqZero

/-- A `uaToEquiv`-headed source and a `listNil`-headed target
are not convertible. -/
theorem Conv.uaToEquiv_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqNil

/-- A `uaToEquiv`-headed source and an `optionNone`-headed target
are not convertible. -/
theorem Conv.uaToEquiv_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqNone

/-- A `uaToEquiv`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum HoTT-vs-cubical: the
univalence-to-equivalence converter operates in the HoTT
equivalence stratum, while interval0 is a cubical-interval leaf. -/
theorem Conv.uaToEquiv_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqZero

/-- A `uaToEquiv`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum HoTT-vs-cubical: same
argument as `uaToEquiv_ne_interval0`. -/
theorem Conv.uaToEquiv_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqOne

/-- A `uaToEquiv`-headed source and a `natSucc`-headed target are
not convertible. -/
theorem Conv.uaToEquiv_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqSucc

/-- A `uaToEquiv`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.uaToEquiv_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqSome

/-- A `uaToEquiv`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.uaToEquiv_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqInl

/-- A `uaToEquiv`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.uaToEquiv_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqInr

/-- A `uaToEquiv`-headed source and a `listCons`-headed target
are not convertible. -/
theorem Conv.uaToEquiv_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqCons

/-- A `uaToEquiv`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.uaToEquiv_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqPair

/-- A `uaToEquiv`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum HoTT-equivalence-vs-HoTT-identity:
the univalence converter operates in the equivalence stratum,
while refl is the identity-type introduction. -/
theorem Conv.uaToEquiv_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {proofTerm : RawTerm scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.uaToEquiv proofTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl witnessTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqUa, _⟩ :=
    RawStep.parStar.uaToEquiv_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqUa.symm.trans joinEqRefl

/-! ### `oeqRefl` row — HoTT observational-equality reflexivity

The `oeqRefl` head is the introduction form for inner-mode
observational equality (`OEq`), distinct from `refl` which
introduces strict-mode identity (`Id`).  Together with `oeqTrans`
(transitivity, already shipped) and `oeqJ` (eliminator), `oeqRefl`
completes the HoTT observational-equality introduction surface.

Unary at the raw level (one witness sub-term), and the
non-disjunctive `RawStep.parStar.oeqRefl_inv` lemma at
`RawParStarCong.lean:2328` confirms the head is preserved through
every parallel chain — no β rule collapses `oeqRefl witness` to
a non-oeqRefl canonical head.

Source destructure follows the 3-binder unary pattern:
  `obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin` -/

/-- An `oeqRefl`-headed source and a `unit`-headed target are
not convertible. -/
theorem Conv.oeqRefl_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqUnit

/-- An `oeqRefl`-headed source and a `boolTrue`-headed target are
not convertible. -/
theorem Conv.oeqRefl_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqTrue

/-- An `oeqRefl`-headed source and a `boolFalse`-headed target
are not convertible. -/
theorem Conv.oeqRefl_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqFalse

/-- An `oeqRefl`-headed source and a `natZero`-headed target are
not convertible. -/
theorem Conv.oeqRefl_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqZero

/-- An `oeqRefl`-headed source and a `listNil`-headed target are
not convertible. -/
theorem Conv.oeqRefl_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqNil

/-- An `oeqRefl`-headed source and an `optionNone`-headed target
are not convertible. -/
theorem Conv.oeqRefl_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqNone

/-- An `oeqRefl`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum HoTT-vs-cubical: oeqRefl
operates in the HoTT observational-equality stratum, while
interval0 is a cubical-interval leaf. -/
theorem Conv.oeqRefl_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqZero

/-- An `oeqRefl`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum HoTT-vs-cubical: same
argument as `oeqRefl_ne_interval0`. -/
theorem Conv.oeqRefl_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqOne

/-- An `oeqRefl`-headed source and a `natSucc`-headed target are
not convertible. -/
theorem Conv.oeqRefl_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqSucc

/-- An `oeqRefl`-headed source and an `optionSome`-headed target
are not convertible. -/
theorem Conv.oeqRefl_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqSome

/-- An `oeqRefl`-headed source and an `eitherInl`-headed target
are not convertible. -/
theorem Conv.oeqRefl_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqInl

/-- An `oeqRefl`-headed source and an `eitherInr`-headed target
are not convertible. -/
theorem Conv.oeqRefl_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqInr

/-- An `oeqRefl`-headed source and a `listCons`-headed target are
not convertible. -/
theorem Conv.oeqRefl_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqCons

/-- An `oeqRefl`-headed source and a `pair`-headed target are
not convertible. -/
theorem Conv.oeqRefl_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqPair

/-- An `oeqRefl`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum HoTT-observational-vs-HoTT-identity:
`oeqRefl` is the inner-mode observational-equality reflexivity
introduction, while `refl` is the strict-mode identity-type
introduction.  Distinct introduction forms across the two HoTT
equality strata. -/
theorem Conv.oeqRefl_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {strictWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl strictWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqRefl, _⟩ :=
    RawStep.parStar.oeqRefl_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqOeqRefl.symm.trans joinEqRefl

/-! ### `idStrictRefl` row — HoTT strict-identity reflexivity

The `idStrictRefl` head introduces strict-mode identity-type
reflexivity, distinct from `oeqRefl` (inner-mode observational-
equality reflexivity).  The two reflexivity ctors live in
disjoint identity strata at the RawTerm level — strict vs
observational — even though both populate equality types.

Unary at the raw level (one witness sub-term), and the
non-disjunctive `RawStep.parStar.idStrictRefl_inv` lemma at
`RawParStarCong.lean:2363` confirms the head is preserved
through every parallel chain — no β rule collapses
`idStrictRefl witness` to a non-idStrictRefl canonical head.

Source destructure follows the 3-binder unary pattern:
  `obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin` -/

/-- An `idStrictRefl`-headed source and a `unit`-headed target
are not convertible. -/
theorem Conv.idStrictRefl_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqUnit

/-- An `idStrictRefl`-headed source and a `boolTrue`-headed target
are not convertible. -/
theorem Conv.idStrictRefl_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqTrue

/-- An `idStrictRefl`-headed source and a `boolFalse`-headed
target are not convertible. -/
theorem Conv.idStrictRefl_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqFalse

/-- An `idStrictRefl`-headed source and a `natZero`-headed target
are not convertible. -/
theorem Conv.idStrictRefl_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqZero

/-- An `idStrictRefl`-headed source and a `listNil`-headed target
are not convertible. -/
theorem Conv.idStrictRefl_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqNil

/-- An `idStrictRefl`-headed source and an `optionNone`-headed
target are not convertible. -/
theorem Conv.idStrictRefl_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqNone

/-- An `idStrictRefl`-headed source and an `interval0`-headed
target are not convertible.  Cross-stratum HoTT-vs-cubical:
idStrictRefl operates in the HoTT strict-identity stratum, while
interval0 is a cubical-interval leaf. -/
theorem Conv.idStrictRefl_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqZero

/-- An `idStrictRefl`-headed source and an `interval1`-headed
target are not convertible.  Cross-stratum HoTT-vs-cubical:
same argument as `idStrictRefl_ne_interval0`. -/
theorem Conv.idStrictRefl_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqOne

/-- An `idStrictRefl`-headed source and a `natSucc`-headed
target are not convertible.  The source introduces strict-identity
reflexivity at a witness; the target inhabits Nat with a
successor.  Distinct canonical heads at the raw level. -/
theorem Conv.idStrictRefl_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqSucc

/-- An `idStrictRefl`-headed source and an `optionSome`-headed
target are not convertible.  Strict-identity reflexivity versus
inhabited Option — disjoint canonical heads. -/
theorem Conv.idStrictRefl_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqSome

/-- An `idStrictRefl`-headed source and an `eitherInl`-headed
target are not convertible.  Strict-identity reflexivity versus
the left injection of an Either — disjoint canonical heads. -/
theorem Conv.idStrictRefl_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqInl

/-- An `idStrictRefl`-headed source and an `eitherInr`-headed
target are not convertible.  Symmetric to the `eitherInl`
companion above; same proof up to the right-versus-left
injection ctor distinction. -/
theorem Conv.idStrictRefl_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqInr

/-- An `idStrictRefl`-headed source and a `listCons`-headed target
are not convertible.  Strict-identity reflexivity versus a list
cons cell — disjoint canonical heads.  `listCons` is binary, so
the inversion lemma packs the head and tail develop chains
together. -/
theorem Conv.idStrictRefl_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqCons

/-- An `idStrictRefl`-headed source and a `pair`-headed target
are not convertible.  Strict-identity reflexivity versus a Σ-pair
inhabitant — disjoint canonical heads.  `pair` is binary, so the
inversion lemma packs both component develop chains together. -/
theorem Conv.idStrictRefl_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqPair

/-- An `idStrictRefl`-headed source and a `refl`-headed target
are not convertible.  Cross-stratum identity-reflexivity:
`idStrictRefl` introduces the strict (definitional) identity-type
reflexivity, while `refl` introduces the HoTT identity-type
reflexivity (intro for `Ty.id`).  Both inhabit identity-flavored
type families, but at distinct strata that the kernel keeps
disjoint at the raw level. -/
theorem Conv.idStrictRefl_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {witnessTerm : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.idStrictRefl witnessTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqIdStrictRefl, _⟩ :=
    RawStep.parStar.idStrictRefl_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqIdStrictRefl.symm.trans joinEqRefl

/-! ### `oeqFunext` row — HoTT observational-equality funext

The `oeqFunext` head introduces observational equality between
two functions from a witness of their pointwise equality.  Lives
at the HoTT observational stratum (same as `oeqRefl` / `oeqTrans`)
but encodes the funext principle: pointwise equality yields
function-level equality.  Unary at the raw level (one pointwise-
proof witness), and the non-disjunctive
`RawStep.parStar.oeqFunext_inv` lemma at `RawParStarCong.lean:2339`
confirms the head is preserved through every parallel reduction
chain.  Eight leaf disjointness lemmas cover the unary `oeqFunext`
source versus every nullary canonical target. -/

/-- An `oeqFunext`-headed source and a `unit`-headed target are
not convertible.  Disjoint canonical heads at the raw level: the
funext-style observational-equality introduction cannot
postnormalize to the unit value. -/
theorem Conv.oeqFunext_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqUnit

/-- An `oeqFunext`-headed source and a `boolTrue`-headed target
are not convertible.  Symmetric to the `unit` companion: the
canonical heads are syntactically disjoint at the raw level. -/
theorem Conv.oeqFunext_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqTrue

/-- An `oeqFunext`-headed source and a `boolFalse`-headed target
are not convertible.  Same argument as the `boolTrue` companion,
just with the opposite boolean canonical form. -/
theorem Conv.oeqFunext_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqFalse

/-- An `oeqFunext`-headed source and a `natZero`-headed target
are not convertible.  HoTT funext introduction versus the Nat
zero — disjoint canonical heads. -/
theorem Conv.oeqFunext_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqZero

/-- An `oeqFunext`-headed source and a `listNil`-headed target
are not convertible.  Funext versus the empty list — distinct
canonical heads at the raw level. -/
theorem Conv.oeqFunext_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqNil

/-- An `oeqFunext`-headed source and an `optionNone`-headed
target are not convertible.  Funext versus the empty option —
distinct canonical heads at the raw level. -/
theorem Conv.oeqFunext_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqNone

/-- An `oeqFunext`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum HoTT-vs-cubical: the HoTT
funext introduction lives in the observational-equality stratum,
while `interval0` is the cubical interval's zero endpoint. -/
theorem Conv.oeqFunext_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqZero

/-- An `oeqFunext`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum HoTT-vs-cubical: same argument
as `oeqFunext_ne_interval0`. -/
theorem Conv.oeqFunext_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqOne

/-- An `oeqFunext`-headed source and a `natSucc`-headed target
are not convertible.  Funext-style observational equality versus
the Nat successor — disjoint canonical heads at the raw level. -/
theorem Conv.oeqFunext_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqSucc

/-- An `oeqFunext`-headed source and an `optionSome`-headed
target are not convertible.  Funext versus inhabited Option —
disjoint canonical heads. -/
theorem Conv.oeqFunext_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqSome

/-- An `oeqFunext`-headed source and an `eitherInl`-headed target
are not convertible.  Funext versus the left injection of Either
— disjoint canonical heads. -/
theorem Conv.oeqFunext_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqInl

/-- An `oeqFunext`-headed source and an `eitherInr`-headed target
are not convertible.  Symmetric to the `eitherInl` companion. -/
theorem Conv.oeqFunext_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqInr

/-- An `oeqFunext`-headed source and a `listCons`-headed target
are not convertible.  Funext versus a list cons cell — distinct
canonical heads.  `listCons` is binary, so the inversion lemma
packs the head and tail develop chains together. -/
theorem Conv.oeqFunext_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqCons

/-- An `oeqFunext`-headed source and a `pair`-headed target are
not convertible.  Funext versus a Σ-pair inhabitant — distinct
canonical heads.  `pair` is binary; the inversion lemma packs
both component develop chains together. -/
theorem Conv.oeqFunext_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqPair

/-- An `oeqFunext`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum HoTT-observational-vs-HoTT-
identity: `oeqFunext` introduces observational equality via
pointwise function witnessing (funext principle), while `refl`
introduces HoTT identity-type reflexivity for the `Ty.id` family.
Both inhabit equality-flavored types semantically, but their
syntactic raw heads remain disjoint through any parStar chain. -/
theorem Conv.oeqFunext_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pointwiseProof : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqFunext pointwiseProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqOeqFunext, _⟩ :=
    RawStep.parStar.oeqFunext_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqOeqFunext.symm.trans joinEqRefl

/-! ### `cumulUpMarker` row — universe-cumulativity marker

The `cumulUpMarker` head wraps an inner code (typically a type
code at universe level `N`) and lifts it to a code at universe
level `N+1`.  Lives at the universe-cumulativity stratum,
orthogonal to HoTT, cubical, and modal strata.  Unary at the raw
level (one inner-code witness), and the non-disjunctive
`RawStep.parStar.cumulUpMarker_inv` lemma at
`RawParStarCong.lean:2661` confirms the head is preserved through
every parallel reduction chain.  Eight leaf disjointness lemmas
cover the unary `cumulUpMarker` source versus every nullary
canonical target. -/

/-- A `cumulUpMarker`-headed source and a `unit`-headed target
are not convertible.  Universe-cumulativity wrapping versus the
unit value — disjoint canonical heads at the raw level. -/
theorem Conv.cumulUpMarker_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqUnit

/-- A `cumulUpMarker`-headed source and a `boolTrue`-headed
target are not convertible.  Same argument as the `unit`
companion: distinct canonical heads at the raw level. -/
theorem Conv.cumulUpMarker_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqTrue

/-- A `cumulUpMarker`-headed source and a `boolFalse`-headed
target are not convertible.  Symmetric to the `boolTrue`
companion. -/
theorem Conv.cumulUpMarker_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqFalse

/-- A `cumulUpMarker`-headed source and a `natZero`-headed target
are not convertible.  Universe-cumulativity wrapping versus the
Nat zero — disjoint canonical heads at the raw level. -/
theorem Conv.cumulUpMarker_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqZero

/-- A `cumulUpMarker`-headed source and a `listNil`-headed target
are not convertible.  Universe-cumulativity wrapping versus the
empty list — distinct canonical heads. -/
theorem Conv.cumulUpMarker_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqNil

/-- A `cumulUpMarker`-headed source and an `optionNone`-headed
target are not convertible.  Universe-cumulativity wrapping
versus the empty option — distinct canonical heads. -/
theorem Conv.cumulUpMarker_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqNone

/-- A `cumulUpMarker`-headed source and an `interval0`-headed
target are not convertible.  Cross-stratum cumulativity-versus-
cubical: distinct semantic universes. -/
theorem Conv.cumulUpMarker_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqZero

/-- A `cumulUpMarker`-headed source and an `interval1`-headed
target are not convertible.  Symmetric to the `interval0`
companion. -/
theorem Conv.cumulUpMarker_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqOne

/-- A `cumulUpMarker`-headed source and a `natSucc`-headed target
are not convertible.  Universe-cumulativity wrapping versus the
Nat successor — disjoint canonical heads at the raw level. -/
theorem Conv.cumulUpMarker_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqSucc

/-- A `cumulUpMarker`-headed source and an `optionSome`-headed
target are not convertible.  Universe-cumulativity wrapping
versus inhabited Option — disjoint canonical heads. -/
theorem Conv.cumulUpMarker_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqSome

/-- A `cumulUpMarker`-headed source and an `eitherInl`-headed
target are not convertible.  Universe-cumulativity wrapping
versus the left injection of Either — disjoint canonical
heads. -/
theorem Conv.cumulUpMarker_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqInl

/-- A `cumulUpMarker`-headed source and an `eitherInr`-headed
target are not convertible.  Symmetric to the `eitherInl`
companion. -/
theorem Conv.cumulUpMarker_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqInr

/-- A `cumulUpMarker`-headed source and a `listCons`-headed
target are not convertible.  Universe-cumulativity wrapping
versus a list cons cell — distinct canonical heads.  `listCons`
is binary, so the inversion lemma packs head and tail develop
chains together. -/
theorem Conv.cumulUpMarker_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqCons

/-- A `cumulUpMarker`-headed source and a `pair`-headed target
are not convertible.  Universe-cumulativity wrapping versus a
Σ-pair inhabitant — distinct canonical heads. -/
theorem Conv.cumulUpMarker_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqPair

/-- A `cumulUpMarker`-headed source and a `refl`-headed target
are not convertible.  Cross-stratum cumulativity-vs-HoTT-identity:
the universe-cumulativity marker lives at a distinct semantic
stratum from HoTT identity-type reflexivity. -/
theorem Conv.cumulUpMarker_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerCodeRaw : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.cumulUpMarker innerCodeRaw : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqCumulUp, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqCumulUp.symm.trans joinEqRefl

/-! ### `transpFill` row — cubical Kan-op filler

The `transpFill` head is the kernel's cubical Kan filler — given
a path proof, an interval position, and a source value, it
produces the partial fill of the source along the path at the
specified interval position.  Ternary at the raw level (three
sub-witnesses), and the non-disjunctive
`RawStep.parStar.transpFill_inv` lemma at
`RawParStarCong.lean:2444` confirms the head is preserved through
every parallel reduction chain.  The inversion returns three
witness targets plus three step chains (7-component destructure).

Lives at the cubical Kan-op stratum, distinct from HoTT-equality,
universe-cumulativity, and the cubical-base layer (interval
endpoints + lattice operations).  Eight leaf disjointness lemmas
cover the ternary `transpFill` source versus every nullary
canonical target. -/

/-- A `transpFill`-headed source and a `unit`-headed target are
not convertible.  Cubical Kan filler versus the unit value —
disjoint canonical heads at the raw level. -/
theorem Conv.transpFill_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqUnit

/-- A `transpFill`-headed source and a `boolTrue`-headed target
are not convertible.  Same argument as the `unit` companion. -/
theorem Conv.transpFill_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqTrue

/-- A `transpFill`-headed source and a `boolFalse`-headed target
are not convertible.  Symmetric to the `boolTrue` companion. -/
theorem Conv.transpFill_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqFalse

/-- A `transpFill`-headed source and a `natZero`-headed target
are not convertible.  Cubical Kan filler versus Nat zero —
distinct canonical heads. -/
theorem Conv.transpFill_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqZero

/-- A `transpFill`-headed source and a `listNil`-headed target
are not convertible.  Cubical Kan filler versus the empty list
— distinct canonical heads. -/
theorem Conv.transpFill_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqNil

/-- A `transpFill`-headed source and an `optionNone`-headed
target are not convertible.  Cubical Kan filler versus the
empty option — distinct canonical heads. -/
theorem Conv.transpFill_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqNone

/-- A `transpFill`-headed source and an `interval0`-headed
target are not convertible.  Cubical Kan filler versus the
cubical interval zero endpoint — even though both inhabit the
cubical stratum, the Kan-op layer and the interval-base layer
are syntactically distinguishable at the raw level. -/
theorem Conv.transpFill_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqZero

/-- A `transpFill`-headed source and an `interval1`-headed
target are not convertible.  Symmetric to the `interval0`
companion. -/
theorem Conv.transpFill_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqOne

/-- A `transpFill`-headed source and a `natSucc`-headed target
are not convertible.  Cubical Kan filler versus Nat successor —
disjoint canonical heads at the raw level. -/
theorem Conv.transpFill_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqSucc

/-- A `transpFill`-headed source and an `optionSome`-headed
target are not convertible.  Cubical Kan filler versus inhabited
Option — disjoint canonical heads. -/
theorem Conv.transpFill_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqSome

/-- A `transpFill`-headed source and an `eitherInl`-headed target
are not convertible.  Cubical Kan filler versus the left injection
of Either — disjoint canonical heads. -/
theorem Conv.transpFill_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqInl

/-- A `transpFill`-headed source and an `eitherInr`-headed target
are not convertible.  Symmetric to the `eitherInl` companion. -/
theorem Conv.transpFill_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqInr

/-- A `transpFill`-headed source and a `listCons`-headed target
are not convertible.  Cubical Kan filler versus list cons cell
— distinct canonical heads. -/
theorem Conv.transpFill_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqCons

/-- A `transpFill`-headed source and a `pair`-headed target are
not convertible.  Cubical Kan filler versus Σ-pair inhabitant —
distinct canonical heads. -/
theorem Conv.transpFill_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqPair

/-- A `transpFill`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum cubical-Kan-op-vs-HoTT-identity:
the cubical Kan filler lives at the Kan-op layer of the cubical
stratum, while `refl` introduces HoTT identity-type reflexivity.
Distinct semantic strata, syntactically disjoint at the raw
level. -/
theorem Conv.transpFill_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {pathTerm intervalTerm sourceRawTerm : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.transpFill pathTerm intervalTerm sourceRawTerm :
        RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, _, joinEqTranspFill, _, _, _⟩ :=
    RawStep.parStar.transpFill_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqTranspFill.symm.trans joinEqRefl

/-! ### `subsume` row — modal subsumption stratum

The `subsume` head wraps an inner term and lifts it through a
modal-subtyping coercion (e.g. boxing of a discrete value, or
implicit upcast across a flat/sharp modality boundary).  Distinct
from the universe-cumulativity marker (`cumulUpMarker`, which is
the explicit universe-level shift), `subsume` is the modal-shape
coercion at the term level.  Unary at the raw level, and the
non-disjunctive `RawStep.parStar.subsume_inv` lemma at
`RawParStarCong.lean:2650` confirms the head is preserved through
every parallel reduction chain.

Eight leaf disjointness lemmas cover the unary `subsume` source
versus every nullary canonical target. -/

/-- A `subsume`-headed source and a `unit`-headed target are
not convertible.  Modal subsumption versus the unit value —
disjoint canonical heads at the raw level. -/
theorem Conv.subsume_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqUnit

/-- A `subsume`-headed source and a `boolTrue`-headed target are
not convertible.  Same argument as the `unit` companion. -/
theorem Conv.subsume_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqTrue

/-- A `subsume`-headed source and a `boolFalse`-headed target
are not convertible.  Symmetric to the `boolTrue` companion. -/
theorem Conv.subsume_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqFalse

/-- A `subsume`-headed source and a `natZero`-headed target are
not convertible.  Modal subsumption versus Nat zero — distinct
canonical heads. -/
theorem Conv.subsume_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqZero

/-- A `subsume`-headed source and a `listNil`-headed target are
not convertible.  Modal subsumption versus the empty list —
distinct canonical heads. -/
theorem Conv.subsume_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqNil

/-- A `subsume`-headed source and an `optionNone`-headed target
are not convertible.  Modal subsumption versus the empty option
— distinct canonical heads. -/
theorem Conv.subsume_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqNone

/-- A `subsume`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum modal-vs-cubical: distinct
semantic strata. -/
theorem Conv.subsume_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqZero

/-- A `subsume`-headed source and an `interval1`-headed target
are not convertible.  Symmetric to the `interval0` companion. -/
theorem Conv.subsume_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqOne

/-- A `subsume`-headed source and a `natSucc`-headed target are
not convertible.  Modal subsumption versus Nat successor —
disjoint canonical heads. -/
theorem Conv.subsume_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqSucc

/-- A `subsume`-headed source and an `optionSome`-headed target
are not convertible.  Modal subsumption versus inhabited Option
— disjoint canonical heads. -/
theorem Conv.subsume_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqSome

/-- A `subsume`-headed source and an `eitherInl`-headed target
are not convertible.  Modal subsumption versus the left
injection of Either — disjoint canonical heads. -/
theorem Conv.subsume_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqInl

/-- A `subsume`-headed source and an `eitherInr`-headed target
are not convertible.  Symmetric to the `eitherInl` companion. -/
theorem Conv.subsume_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqInr

/-- A `subsume`-headed source and a `listCons`-headed target are
not convertible.  Modal subsumption versus list cons cell —
distinct canonical heads. -/
theorem Conv.subsume_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {headTerm tailTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headTerm tailTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqCons

/-- A `subsume`-headed source and a `pair`-headed target are not
convertible.  Modal subsumption versus Σ-pair inhabitant —
distinct canonical heads. -/
theorem Conv.subsume_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqPair

/-- A `subsume`-headed source and a `refl`-headed target are not
convertible.  Cross-stratum modal-subsumption-vs-HoTT-identity:
the modal subsumption coercion and the HoTT identity-type
reflexivity introduction live at distinct semantic strata. -/
theorem Conv.subsume_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerSubsumed : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.subsume innerSubsumed : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSubsume, _⟩ :=
    RawStep.parStar.subsume_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqSubsume.symm.trans joinEqRefl

/-- An `oeqJ`-headed source and a `unit`-headed target are not
convertible.  Disjoint canonical heads at the raw level: the
observational-equality J recursor is a HoTT-stratum elimination
form, whereas `unit` is the canonical inhabitant of the unit
type — neither can postnormalize to the other. -/
theorem Conv.oeqJ_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqUnit

/-- An `oeqJ`-headed source and a `boolTrue`-headed target are
not convertible.  Symmetric to the `unit` companion: the
observational-equality J recursor and the Bool true value have
syntactically disjoint canonical heads at the raw level. -/
theorem Conv.oeqJ_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqTrue

/-- An `oeqJ`-headed source and a `boolFalse`-headed target are
not convertible.  Same argument as the `boolTrue` companion,
just with the opposite boolean canonical form. -/
theorem Conv.oeqJ_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqFalse

/-- An `oeqJ`-headed source and a `natZero`-headed target are
not convertible.  HoTT observational-equality J recursor versus
the Nat zero canonical form — disjoint canonical heads. -/
theorem Conv.oeqJ_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqZero

/-- An `oeqJ`-headed source and a `listNil`-headed target are
not convertible.  The HoTT observational-equality J recursor and
the empty list have distinct canonical heads at the raw level. -/
theorem Conv.oeqJ_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqNil

/-- An `oeqJ`-headed source and an `optionNone`-headed target
are not convertible.  HoTT observational-equality J versus the
empty option — distinct canonical heads at the raw level. -/
theorem Conv.oeqJ_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqNone

/-- An `oeqJ`-headed source and an `interval0`-headed target are
not convertible.  Cross-stratum HoTT-vs-cubical: the HoTT
observational-equality J recursor lives at the HoTT identity
stratum, while `interval0` is the cubical interval's zero
endpoint — they cannot share a canonical reduct. -/
theorem Conv.oeqJ_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqZero

/-- An `oeqJ`-headed source and an `interval1`-headed target are
not convertible.  Cross-stratum HoTT-vs-cubical: same argument
as `oeqJ_ne_interval0`. -/
theorem Conv.oeqJ_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqOne

/-- An `oeqJ`-headed source and a `natSucc`-headed target are
not convertible.  HoTT observational-equality J recursor versus
the Nat successor compound canonical form — distinct heads at
the raw level. -/
theorem Conv.oeqJ_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqSucc

/-- An `oeqJ`-headed source and an `optionSome`-headed target
are not convertible.  HoTT J recursor versus inhabited Option —
disjoint canonical heads. -/
theorem Conv.oeqJ_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqSome

/-- An `oeqJ`-headed source and an `eitherInl`-headed target are
not convertible.  HoTT J recursor versus the left injection of
Either — disjoint canonical heads. -/
theorem Conv.oeqJ_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqInl

/-- An `oeqJ`-headed source and an `eitherInr`-headed target are
not convertible.  Symmetric to the `eitherInl` companion. -/
theorem Conv.oeqJ_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqInr

/-- An `oeqJ`-headed source and a `listCons`-headed target are
not convertible.  HoTT J recursor versus the non-empty list
constructor — disjoint canonical heads at the raw level. -/
theorem Conv.oeqJ_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {headValue tailValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headValue tailValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqCons

/-- An `oeqJ`-headed source and a `pair`-headed target are not
convertible.  HoTT observational-equality J recursor versus the
Σ-pair inhabitant — distinct canonical heads at the raw level. -/
theorem Conv.oeqJ_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqPair

/-- An `oeqJ`-headed source and a `refl`-headed target are not
convertible.  Within the HoTT identity-family stratum, the J
recursor (an elimination form) and the `refl` reflexivity
introduction are distinct ctors that cannot share a canonical
raw reduct.  This case is the J-versus-refl head clash inside
the same semantic stratum, not cross-stratum. -/
theorem Conv.oeqJ_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {baseCase witness : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.oeqJ baseCase witness : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqOeqJ, _, _⟩ :=
    RawStep.parStar.oeqJ_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqOeqJ.symm.trans joinEqRefl

/-- A `modIntro`-headed source and a `unit`-headed target are not
convertible.  Disjoint canonical heads at the raw level: the
modality introduction form is the universal box/diamond/flat/
sharp/ghost/cap/later/clock packing, while `unit` is the
canonical inhabitant of the unit type — neither can postnormalize
to the other. -/
theorem Conv.modIntro_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqUnit

/-- A `modIntro`-headed source and a `boolTrue`-headed target
are not convertible.  Modal introduction versus the Bool true
value — distinct canonical heads at the raw level. -/
theorem Conv.modIntro_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqTrue

/-- A `modIntro`-headed source and a `boolFalse`-headed target
are not convertible.  Same argument as the `boolTrue` companion,
just with the opposite boolean canonical form. -/
theorem Conv.modIntro_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqFalse

/-- A `modIntro`-headed source and a `natZero`-headed target are
not convertible.  Modal introduction versus the Nat zero
canonical form — disjoint canonical heads. -/
theorem Conv.modIntro_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqZero

/-- A `modIntro`-headed source and a `listNil`-headed target are
not convertible.  Modal introduction versus the empty list —
distinct canonical heads at the raw level. -/
theorem Conv.modIntro_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqNil

/-- A `modIntro`-headed source and an `optionNone`-headed target
are not convertible.  Modal introduction versus the empty option
— distinct canonical heads at the raw level. -/
theorem Conv.modIntro_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqNone

/-- A `modIntro`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum modal-vs-cubical: the modal
introduction lives at the modal stratum (♭/◇/□/♯/ghost/cap/later/
clock), while `interval0` is the cubical interval's zero endpoint
— they cannot share a canonical reduct. -/
theorem Conv.modIntro_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqZero

/-- A `modIntro`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum modal-vs-cubical: same
argument as `modIntro_ne_interval0`. -/
theorem Conv.modIntro_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqOne

/-- A `modIntro`-headed source and a `natSucc`-headed target are
not convertible.  Modal introduction versus the Nat successor —
distinct canonical heads at the raw level. -/
theorem Conv.modIntro_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqSucc

/-- A `modIntro`-headed source and an `optionSome`-headed target
are not convertible.  Modal introduction versus inhabited
Option — disjoint canonical heads. -/
theorem Conv.modIntro_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqSome

/-- A `modIntro`-headed source and an `eitherInl`-headed target
are not convertible.  Modal introduction versus the left
injection of Either — disjoint canonical heads. -/
theorem Conv.modIntro_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqInl

/-- A `modIntro`-headed source and an `eitherInr`-headed target
are not convertible.  Symmetric to the `eitherInl` companion. -/
theorem Conv.modIntro_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqInr

/-- A `modIntro`-headed source and a `listCons`-headed target
are not convertible.  Modal introduction versus the non-empty
list constructor — disjoint canonical heads at the raw level. -/
theorem Conv.modIntro_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {headValue tailValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headValue tailValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqCons

/-- A `modIntro`-headed source and a `pair`-headed target are
not convertible.  Modal introduction versus the Σ-pair
inhabitant — distinct canonical heads at the raw level. -/
theorem Conv.modIntro_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqPair

/-- A `modIntro`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum modal-vs-HoTT-identity: the
modal introduction lives at the modal stratum, while `refl` is
the HoTT identity-type reflexivity introduction — they cannot
share a canonical raw reduct.  Symmetric companion to iter 97's
`subsume_ne_refl` (which is also modal-vs-HoTT-identity but at
the SUBSUMPTION side of the modal stratum, not the intro side). -/
theorem Conv.modIntro_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {innerTerm : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.modIntro innerTerm : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqModIntro, _⟩ :=
    RawStep.parStar.modIntro_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqModIntro.symm.trans joinEqRefl

/-- An `equivIntro`-headed source and a `unit`-headed target are
not convertible.  Disjoint canonical heads at the raw level: the
HoTT equivalence introduction packages a forward function with
its quasi-inverse, whereas `unit` is the canonical inhabitant of
the unit type — they cannot share a canonical reduct. -/
theorem Conv.equivIntro_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqUnit

/-- An `equivIntro`-headed source and a `boolTrue`-headed target
are not convertible.  HoTT equivalence introduction versus the
Bool true value — distinct canonical heads at the raw level. -/
theorem Conv.equivIntro_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqTrue

/-- An `equivIntro`-headed source and a `boolFalse`-headed target
are not convertible.  Same argument as the `boolTrue` companion. -/
theorem Conv.equivIntro_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqFalse

/-- An `equivIntro`-headed source and a `natZero`-headed target
are not convertible.  HoTT equivalence introduction versus the
Nat zero — disjoint canonical heads. -/
theorem Conv.equivIntro_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqZero

/-- An `equivIntro`-headed source and a `listNil`-headed target
are not convertible.  HoTT equivalence introduction versus the
empty list — distinct canonical heads at the raw level. -/
theorem Conv.equivIntro_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqNil

/-- An `equivIntro`-headed source and an `optionNone`-headed
target are not convertible.  HoTT equivalence introduction
versus the empty option — distinct canonical heads. -/
theorem Conv.equivIntro_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqNone

/-- An `equivIntro`-headed source and an `interval0`-headed
target are not convertible.  Cross-stratum HoTT-equivalence vs
cubical-interval: the equivalence introduction lives at the
HoTT layer, while `interval0` is the cubical interval's zero
endpoint — they cannot share a canonical reduct. -/
theorem Conv.equivIntro_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqZero

/-- An `equivIntro`-headed source and an `interval1`-headed
target are not convertible.  Cross-stratum HoTT-equivalence vs
cubical-interval: symmetric companion to
`equivIntro_ne_interval0`. -/
theorem Conv.equivIntro_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqOne

/-- An `equivIntro`-headed source and a `natSucc`-headed target
are not convertible.  HoTT equivalence introduction versus the
Nat successor — distinct canonical heads at the raw level. -/
theorem Conv.equivIntro_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqSucc

/-- An `equivIntro`-headed source and an `optionSome`-headed
target are not convertible.  HoTT equivalence introduction versus
inhabited Option — disjoint canonical heads. -/
theorem Conv.equivIntro_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqSome

/-- An `equivIntro`-headed source and an `eitherInl`-headed
target are not convertible.  HoTT equivalence introduction versus
the left injection of Either — disjoint canonical heads. -/
theorem Conv.equivIntro_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqInl

/-- An `equivIntro`-headed source and an `eitherInr`-headed
target are not convertible.  Symmetric to the `eitherInl`
companion. -/
theorem Conv.equivIntro_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqInr

/-- An `equivIntro`-headed source and a `listCons`-headed target
are not convertible.  HoTT equivalence introduction versus the
non-empty list constructor — disjoint canonical heads at the
raw level. -/
theorem Conv.equivIntro_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {headValue tailValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headValue tailValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqCons

/-- An `equivIntro`-headed source and a `pair`-headed target are
not convertible.  HoTT equivalence introduction versus the
Σ-pair inhabitant — distinct canonical heads. -/
theorem Conv.equivIntro_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqPair

/-- An `equivIntro`-headed source and a `refl`-headed target are
not convertible.  HoTT equivalence introduction versus HoTT
identity-type reflexivity introduction — both live at the HoTT
layer but at distinct strata (equivalence vs identity); they
are distinct ctors that cannot share a canonical raw reduct. -/
theorem Conv.equivIntro_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {forwardFn backwardFn : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.equivIntro forwardFn backwardFn : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqEquivIntro.symm.trans joinEqRefl

/-- A `recordIntro`-headed source and a `unit`-headed target are not
convertible.  Disjoint canonical heads at the raw level: the record
introducer packages a first-field value into a record canonical
form, whereas `unit` is the canonical inhabitant of the unit type —
they cannot share a canonical reduct. -/
theorem Conv.recordIntro_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqUnit

/-- A `recordIntro`-headed source and a `boolTrue`-headed target are
not convertible.  Record introduction versus the Bool true value —
distinct canonical heads at the raw level. -/
theorem Conv.recordIntro_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqTrue

/-- A `recordIntro`-headed source and a `boolFalse`-headed target
are not convertible.  Same argument as the `boolTrue` companion. -/
theorem Conv.recordIntro_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqFalse

/-- A `recordIntro`-headed source and a `natZero`-headed target are
not convertible.  Record introduction versus the Nat zero — disjoint
canonical heads. -/
theorem Conv.recordIntro_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqZero

/-- A `recordIntro`-headed source and a `listNil`-headed target are
not convertible.  Record introduction versus the empty list —
distinct canonical heads at the raw level. -/
theorem Conv.recordIntro_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqNil

/-- A `recordIntro`-headed source and an `optionNone`-headed target
are not convertible.  Record introduction versus the empty option —
distinct canonical heads. -/
theorem Conv.recordIntro_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqNone

/-- A `recordIntro`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum record-vs-cubical: the record
introduction lives at the structural stratum, while `interval0` is
the cubical interval's zero endpoint — they cannot share a
canonical reduct. -/
theorem Conv.recordIntro_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqZero

/-- A `recordIntro`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum record-vs-cubical: symmetric
companion to `recordIntro_ne_interval0`. -/
theorem Conv.recordIntro_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqOne

/-- A `recordIntro`-headed source and a `natSucc`-headed target are
not convertible.  Record introduction versus the Nat successor —
distinct canonical heads at the raw level. -/
theorem Conv.recordIntro_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqSucc

/-- A `recordIntro`-headed source and an `optionSome`-headed target
are not convertible.  Record introduction versus inhabited Option —
disjoint canonical heads. -/
theorem Conv.recordIntro_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqSome

/-- A `recordIntro`-headed source and an `eitherInl`-headed target
are not convertible.  Record introduction versus the left injection
of Either — disjoint canonical heads. -/
theorem Conv.recordIntro_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqInl

/-- A `recordIntro`-headed source and an `eitherInr`-headed target
are not convertible.  Symmetric to the `eitherInl` companion. -/
theorem Conv.recordIntro_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqInr

/-- A `recordIntro`-headed source and a `listCons`-headed target are
not convertible.  Record introduction versus the non-empty list
constructor — disjoint canonical heads at the raw level. -/
theorem Conv.recordIntro_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {headValue tailValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headValue tailValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqCons

/-- A `recordIntro`-headed source and a `pair`-headed target are
not convertible.  Record introduction versus the Σ-pair inhabitant
— distinct canonical heads at the raw level.  Both are compound
data introducers but at distinct strata (record vs Σ-pair). -/
theorem Conv.recordIntro_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqPair

/-- A `recordIntro`-headed source and a `refl`-headed target are not
convertible.  Cross-stratum record-vs-HoTT-identity: record
introduction lives at the structural stratum, while `refl` is the
HoTT identity-type reflexivity introduction — they cannot share a
canonical raw reduct. -/
theorem Conv.recordIntro_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {firstField : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.recordIntro firstField : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqRecord, _⟩ :=
    RawStep.parStar.recordIntro_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqRecord.symm.trans joinEqRefl

/-- A `refineIntro`-headed source and a `unit`-headed target are not
convertible.  Disjoint canonical heads at the raw level: refinement
introduction packages a value with a predicate proof to inhabit a
refined type, whereas `unit` is the canonical inhabitant of the
unit type — they cannot share a canonical reduct. -/
theorem Conv.refineIntro_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqUnit

/-- A `refineIntro`-headed source and a `boolTrue`-headed target are
not convertible.  Refinement introduction versus the Bool true value
— distinct canonical heads at the raw level. -/
theorem Conv.refineIntro_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqTrue

/-- A `refineIntro`-headed source and a `boolFalse`-headed target
are not convertible.  Same argument as the `boolTrue` companion. -/
theorem Conv.refineIntro_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqFalse

/-- A `refineIntro`-headed source and a `natZero`-headed target are
not convertible.  Refinement introduction versus the Nat zero —
disjoint canonical heads. -/
theorem Conv.refineIntro_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqZero

/-- A `refineIntro`-headed source and a `listNil`-headed target are
not convertible.  Refinement introduction versus the empty list —
distinct canonical heads at the raw level. -/
theorem Conv.refineIntro_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqNil

/-- A `refineIntro`-headed source and an `optionNone`-headed target
are not convertible.  Refinement introduction versus the empty
option — distinct canonical heads. -/
theorem Conv.refineIntro_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqNone

/-- A `refineIntro`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum refine-vs-cubical: refinement
introduction lives at the refinement-type stratum, while
`interval0` is the cubical interval's zero endpoint — they cannot
share a canonical reduct. -/
theorem Conv.refineIntro_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqZero

/-- A `refineIntro`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum refine-vs-cubical: symmetric
companion to `refineIntro_ne_interval0`. -/
theorem Conv.refineIntro_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqOne

/-- A `refineIntro`-headed source and a `natSucc`-headed target are
not convertible.  Refinement introduction versus the Nat successor
— distinct canonical heads at the raw level. -/
theorem Conv.refineIntro_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqSucc

/-- A `refineIntro`-headed source and an `optionSome`-headed target
are not convertible.  Refinement introduction versus inhabited
Option — disjoint canonical heads. -/
theorem Conv.refineIntro_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqSome

/-- A `refineIntro`-headed source and an `eitherInl`-headed target
are not convertible.  Refinement introduction versus the left
injection of Either — disjoint canonical heads. -/
theorem Conv.refineIntro_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqInl

/-- A `refineIntro`-headed source and an `eitherInr`-headed target
are not convertible.  Symmetric to the `eitherInl` companion. -/
theorem Conv.refineIntro_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqInr

/-- A `refineIntro`-headed source and a `listCons`-headed target
are not convertible.  Refinement introduction versus the non-empty
list constructor — disjoint canonical heads at the raw level. -/
theorem Conv.refineIntro_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {headValue tailValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headValue tailValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqCons

/-- A `refineIntro`-headed source and a `pair`-headed target are
not convertible.  Refinement introduction versus the Σ-pair
inhabitant — distinct canonical heads at the raw level. -/
theorem Conv.refineIntro_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqPair

/-- A `refineIntro`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum refine-vs-HoTT-identity: refinement
introduction lives at the refinement-type stratum, while `refl` is
the HoTT identity-type reflexivity introduction — they cannot share
a canonical raw reduct. -/
theorem Conv.refineIntro_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {rawValue predicateProof : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.refineIntro rawValue predicateProof : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqRefineIntro, _, _⟩ :=
    RawStep.parStar.refineIntro_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqRefineIntro.symm.trans joinEqRefl

/-- A `sessionRecv`-headed source and a `unit`-headed target are not
convertible.  Disjoint canonical heads at the raw level: the session
receive operation suspends pending message arrival on a session-typed
channel, whereas `unit` is the canonical inhabitant of the unit type
— they cannot share a canonical reduct. -/
theorem Conv.sessionRecv_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqUnit

/-- A `sessionRecv`-headed source and a `boolTrue`-headed target are
not convertible.  Session receive versus the Bool true value —
distinct canonical heads at the raw level. -/
theorem Conv.sessionRecv_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqTrue

/-- A `sessionRecv`-headed source and a `boolFalse`-headed target
are not convertible.  Same argument as the `boolTrue` companion. -/
theorem Conv.sessionRecv_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqFalse

/-- A `sessionRecv`-headed source and a `natZero`-headed target are
not convertible.  Session receive versus the Nat zero canonical
form — disjoint canonical heads. -/
theorem Conv.sessionRecv_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqZero

/-- A `sessionRecv`-headed source and a `listNil`-headed target are
not convertible.  Session receive versus the empty list — distinct
canonical heads at the raw level. -/
theorem Conv.sessionRecv_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqNil

/-- A `sessionRecv`-headed source and an `optionNone`-headed target
are not convertible.  Session receive versus the empty option —
distinct canonical heads. -/
theorem Conv.sessionRecv_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqNone

/-- A `sessionRecv`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum session-vs-cubical: the session
receive operation lives at the session-type stratum, while
`interval0` is the cubical interval's zero endpoint — they cannot
share a canonical reduct. -/
theorem Conv.sessionRecv_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqZero

/-- A `sessionRecv`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum session-vs-cubical: symmetric
companion to `sessionRecv_ne_interval0`. -/
theorem Conv.sessionRecv_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqOne

/-- A `sessionRecv`-headed source and a `natSucc`-headed target are
not convertible.  Session receive versus the Nat successor —
distinct canonical heads at the raw level. -/
theorem Conv.sessionRecv_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqSucc

/-- A `sessionRecv`-headed source and an `optionSome`-headed target
are not convertible.  Session receive versus inhabited Option —
disjoint canonical heads. -/
theorem Conv.sessionRecv_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqSome

/-- A `sessionRecv`-headed source and an `eitherInl`-headed target
are not convertible.  Session receive versus the left injection of
Either — disjoint canonical heads. -/
theorem Conv.sessionRecv_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqInl

/-- A `sessionRecv`-headed source and an `eitherInr`-headed target
are not convertible.  Symmetric to the `eitherInl` companion. -/
theorem Conv.sessionRecv_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {valueTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr valueTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqInr

/-- A `sessionRecv`-headed source and a `listCons`-headed target
are not convertible.  Session receive versus the non-empty list
constructor — disjoint canonical heads. -/
theorem Conv.sessionRecv_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {headValue tailValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headValue tailValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqCons

/-- A `sessionRecv`-headed source and a `pair`-headed target are
not convertible.  Session receive versus the Σ-pair inhabitant —
distinct canonical heads at the raw level. -/
theorem Conv.sessionRecv_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqPair

/-- A `sessionRecv`-headed source and a `refl`-headed target are
not convertible.  Cross-stratum session-vs-HoTT-identity: session
receive lives at the session stratum, refl at the HoTT identity
stratum; they cannot share a canonical raw reduct. -/
theorem Conv.sessionRecv_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel : RawTerm scope}
    {hottWitness : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionRecv channel : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl hottWitness : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, joinEqSessionRecv, _⟩ :=
    RawStep.parStar.sessionRecv_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqSessionRecv.symm.trans joinEqRefl

/-- A `codataUnfold`-headed source and a `unit`-headed target are
not convertible.  Disjoint canonical heads at the raw level: codata
unfold packages an initial state and a transition function to
produce a coinductive stream, whereas `unit` is the canonical
inhabitant of the unit type — they cannot share a canonical reduct. -/
theorem Conv.codataUnfold_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqUnit

/-- A `codataUnfold`-headed source and a `boolTrue`-headed target
are not convertible.  Codata unfold versus the Bool true value —
distinct canonical heads at the raw level. -/
theorem Conv.codataUnfold_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqTrue

/-- A `codataUnfold`-headed source and a `boolFalse`-headed target
are not convertible.  Same argument as the `boolTrue` companion. -/
theorem Conv.codataUnfold_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqFalse

/-- A `codataUnfold`-headed source and a `natZero`-headed target
are not convertible.  Codata unfold versus the Nat zero — disjoint
canonical heads. -/
theorem Conv.codataUnfold_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqZero

/-- A `codataUnfold`-headed source and a `listNil`-headed target
are not convertible.  Codata unfold versus the empty list —
distinct canonical heads at the raw level. -/
theorem Conv.codataUnfold_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqNil

/-- A `codataUnfold`-headed source and an `optionNone`-headed
target are not convertible.  Codata unfold versus the empty option
— distinct canonical heads. -/
theorem Conv.codataUnfold_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqNone

/-- A `codataUnfold`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum codata-vs-cubical: codata unfold
lives at the coinductive stratum, while `interval0` is the cubical
interval's zero endpoint — they cannot share a canonical reduct. -/
theorem Conv.codataUnfold_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqZero

/-- A `codataUnfold`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum codata-vs-cubical: symmetric
companion to `codataUnfold_ne_interval0`. -/
theorem Conv.codataUnfold_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqOne

/-- A `codataUnfold`-headed source and a `natSucc`-headed target
are not convertible.  Codata unfold versus Nat successor —
distinct canonical heads at the raw level. -/
theorem Conv.codataUnfold_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqSucc

/-- A `codataUnfold`-headed source and an `optionSome`-headed
target are not convertible.  Codata unfold versus Some — distinct
canonical heads at the raw level. -/
theorem Conv.codataUnfold_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {value : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome value : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqSome

/-- A `codataUnfold`-headed source and an `eitherInl`-headed
target are not convertible.  Codata unfold versus Inl — distinct
canonical heads at the raw level. -/
theorem Conv.codataUnfold_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {leftValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl leftValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqInl

/-- A `codataUnfold`-headed source and an `eitherInr`-headed
target are not convertible.  Codata unfold versus Inr — distinct
canonical heads at the raw level. -/
theorem Conv.codataUnfold_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {rightValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr rightValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqInr

/-- A `codataUnfold`-headed source and a `listCons`-headed target
are not convertible.  Codata unfold versus list cons — both
binary at the raw level, but distinct canonical heads. -/
theorem Conv.codataUnfold_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {headValue tailValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headValue tailValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqCons

/-- A `codataUnfold`-headed source and a `pair`-headed target are
not convertible.  Codata unfold versus dependent-pair introduction
— both binary at the raw level, but distinct canonical heads. -/
theorem Conv.codataUnfold_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqPair

/-- A `codataUnfold`-headed source and a `refl`-headed target are
not convertible.  Codata unfold versus reflexivity proof —
distinct canonical heads at the raw level. -/
theorem Conv.codataUnfold_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {initialState transition : RawTerm scope}
    {reflTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.codataUnfold initialState transition : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl reflTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqCodataUnfold, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqCodataUnfold.symm.trans joinEqRefl

/-- An `effectPerform`-headed source and a `unit`-headed target are
not convertible.  Disjoint canonical heads at the raw level:
effect perform packages an operation tag with arguments to invoke
an algebraic effect, whereas `unit` is the canonical inhabitant of
the unit type — they cannot share a canonical reduct. -/
theorem Conv.effectPerform_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqUnit

/-- An `effectPerform`-headed source and a `boolTrue`-headed target
are not convertible.  Effect perform versus the Bool true value —
distinct canonical heads at the raw level. -/
theorem Conv.effectPerform_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqTrue

/-- An `effectPerform`-headed source and a `boolFalse`-headed
target are not convertible.  Same argument as the `boolTrue`
companion. -/
theorem Conv.effectPerform_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqFalse

/-- An `effectPerform`-headed source and a `natZero`-headed target
are not convertible.  Effect perform versus the Nat zero — disjoint
canonical heads. -/
theorem Conv.effectPerform_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqZero

/-- An `effectPerform`-headed source and a `listNil`-headed target
are not convertible.  Effect perform versus the empty list —
distinct canonical heads at the raw level. -/
theorem Conv.effectPerform_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqNil

/-- An `effectPerform`-headed source and an `optionNone`-headed
target are not convertible.  Effect perform versus the empty
option — distinct canonical heads. -/
theorem Conv.effectPerform_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqNone

/-- An `effectPerform`-headed source and an `interval0`-headed
target are not convertible.  Cross-stratum effect-vs-cubical:
effect perform lives at the algebraic-effects stratum, while
`interval0` is the cubical interval's zero endpoint — they cannot
share a canonical reduct. -/
theorem Conv.effectPerform_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqZero

/-- An `effectPerform`-headed source and an `interval1`-headed
target are not convertible.  Cross-stratum effect-vs-cubical:
symmetric companion to `effectPerform_ne_interval0`. -/
theorem Conv.effectPerform_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqOne

/-- An `effectPerform`-headed source and a `natSucc`-headed target
are not convertible.  Effect perform versus Nat successor —
distinct canonical heads at the raw level. -/
theorem Conv.effectPerform_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqSucc

/-- An `effectPerform`-headed source and an `optionSome`-headed
target are not convertible.  Effect perform versus Some — distinct
canonical heads at the raw level. -/
theorem Conv.effectPerform_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {value : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome value : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqSome

/-- An `effectPerform`-headed source and an `eitherInl`-headed
target are not convertible.  Effect perform versus Inl — distinct
canonical heads at the raw level. -/
theorem Conv.effectPerform_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {leftValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl leftValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqInl

/-- An `effectPerform`-headed source and an `eitherInr`-headed
target are not convertible.  Effect perform versus Inr — distinct
canonical heads at the raw level. -/
theorem Conv.effectPerform_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {rightValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr rightValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqInr

/-- An `effectPerform`-headed source and a `listCons`-headed target
are not convertible.  Effect perform versus list cons — both
binary at the raw level, but distinct canonical heads. -/
theorem Conv.effectPerform_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {headValue tailValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headValue tailValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqCons

/-- An `effectPerform`-headed source and a `pair`-headed target are
not convertible.  Effect perform versus dependent-pair introduction
— both binary at the raw level, but distinct canonical heads. -/
theorem Conv.effectPerform_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqPair

/-- An `effectPerform`-headed source and a `refl`-headed target are
not convertible.  Effect perform versus reflexivity proof —
distinct canonical heads at the raw level. -/
theorem Conv.effectPerform_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {operationTag arguments : RawTerm scope}
    {reflTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.effectPerform operationTag arguments : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl reflTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqPerform, _, _⟩ :=
    RawStep.parStar.effectPerform_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqPerform.symm.trans joinEqRefl

/-- A `sessionSend`-headed source and a `unit`-headed target are
not convertible.  Disjoint canonical heads at the raw level:
session send packages a channel with a payload to perform an
output protocol step, whereas `unit` is the canonical inhabitant
of the unit type — they cannot share a canonical reduct. -/
theorem Conv.sessionSend_ne_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.unit : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  have joinEqUnit : joinRaw = RawTerm.unit :=
    RawStep.parStar.unit_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqUnit

/-- A `sessionSend`-headed source and a `boolTrue`-headed target
are not convertible.  Session send versus the Bool true value —
distinct canonical heads at the raw level. -/
theorem Conv.sessionSend_ne_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolTrue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  have joinEqTrue : joinRaw = RawTerm.boolTrue :=
    RawStep.parStar.boolTrue_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqTrue

/-- A `sessionSend`-headed source and a `boolFalse`-headed target
are not convertible.  Same argument as the `boolTrue` companion. -/
theorem Conv.sessionSend_ne_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.boolFalse : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  have joinEqFalse : joinRaw = RawTerm.boolFalse :=
    RawStep.parStar.boolFalse_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqFalse

/-- A `sessionSend`-headed source and a `natZero`-headed target are
not convertible.  Session send versus the Nat zero — disjoint
canonical heads. -/
theorem Conv.sessionSend_ne_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.natZero : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.natZero :=
    RawStep.parStar.natZero_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqZero

/-- A `sessionSend`-headed source and a `listNil`-headed target are
not convertible.  Session send versus the empty list — distinct
canonical heads at the raw level. -/
theorem Conv.sessionSend_ne_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType (RawTerm.listNil : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  have joinEqNil : joinRaw = RawTerm.listNil :=
    RawStep.parStar.listNil_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqNil

/-- A `sessionSend`-headed source and an `optionNone`-headed target
are not convertible.  Session send versus the empty option —
distinct canonical heads. -/
theorem Conv.sessionSend_ne_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionNone : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  have joinEqNone : joinRaw = RawTerm.optionNone :=
    RawStep.parStar.optionNone_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqNone

/-- A `sessionSend`-headed source and an `interval0`-headed target
are not convertible.  Cross-stratum session-vs-cubical: session
send lives at the protocol stratum, while `interval0` is the
cubical interval's zero endpoint — they cannot share a canonical
reduct. -/
theorem Conv.sessionSend_ne_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval0 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  have joinEqZero : joinRaw = RawTerm.interval0 :=
    RawStep.parStar.interval0_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqZero

/-- A `sessionSend`-headed source and an `interval1`-headed target
are not convertible.  Cross-stratum session-vs-cubical: symmetric
companion to `sessionSend_ne_interval0`. -/
theorem Conv.sessionSend_ne_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.interval1 : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  have joinEqOne : joinRaw = RawTerm.interval1 :=
    RawStep.parStar.interval1_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqOne

/-- A `sessionSend`-headed source and a `natSucc`-headed target
are not convertible.  Session send versus Nat successor —
distinct canonical heads at the raw level. -/
theorem Conv.sessionSend_ne_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {predecessor : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.natSucc predecessor : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  obtain ⟨_, joinEqSucc, _⟩ :=
    RawStep.parStar.natSucc_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqSucc

/-- A `sessionSend`-headed source and an `optionSome`-headed target
are not convertible.  Session send versus Some — distinct canonical
heads at the raw level. -/
theorem Conv.sessionSend_ne_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {value : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.optionSome value : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  obtain ⟨_, joinEqSome, _⟩ :=
    RawStep.parStar.optionSome_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqSome

/-- A `sessionSend`-headed source and an `eitherInl`-headed target
are not convertible.  Session send versus Inl — distinct canonical
heads at the raw level. -/
theorem Conv.sessionSend_ne_eitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {leftValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInl leftValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  obtain ⟨_, joinEqInl, _⟩ :=
    RawStep.parStar.eitherInl_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqInl

/-- A `sessionSend`-headed source and an `eitherInr`-headed target
are not convertible.  Session send versus Inr — distinct canonical
heads at the raw level. -/
theorem Conv.sessionSend_ne_eitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {rightValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherInr rightValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  obtain ⟨_, joinEqInr, _⟩ :=
    RawStep.parStar.eitherInr_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqInr

/-- A `sessionSend`-headed source and a `listCons`-headed target
are not convertible.  Session send versus list cons — both binary
at the raw level, but distinct canonical heads. -/
theorem Conv.sessionSend_ne_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {headValue tailValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.listCons headValue tailValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  obtain ⟨_, _, joinEqCons, _, _⟩ :=
    RawStep.parStar.listCons_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqCons

/-- A `sessionSend`-headed source and a `pair`-headed target are
not convertible.  Session send versus dependent-pair introduction —
both binary at the raw level, but distinct canonical heads. -/
theorem Conv.sessionSend_ne_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.pair firstValue secondValue : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  obtain ⟨_, _, joinEqPair, _, _⟩ :=
    RawStep.parStar.pair_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqPair

/-- A `sessionSend`-headed source and a `refl`-headed target are
not convertible.  Session send versus reflexivity proof —
distinct canonical heads at the raw level. -/
theorem Conv.sessionSend_ne_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {channel payload : RawTerm scope}
    {reflTerm : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.sessionSend channel payload : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.refl reflTerm : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqSessionSend, _, _⟩ :=
    RawStep.parStar.sessionSend_inv sourceToJoin
  obtain ⟨_, joinEqRefl, _⟩ :=
    RawStep.parStar.refl_inv targetToJoin
  nomatch joinEqSessionSend.symm.trans joinEqRefl

/-! ## Compound × compound disjointness — arrowCode row (open)

Opens the compound × compound matrix.  The previous tiers established
that every compound canonical source head is disjoint from every leaf
canonical target head; this tier extends to disjointness against other
distinct compound canonical heads.  Each lemma follows the standard
recipe: `Conv.canonicalRaw` exposes a raw join, both endpoints' parStar
inv lemmas force the join into two distinct ctor shapes, and `nomatch`
on the chained equality refutes via raw-ctor injectivity. -/

/-- A `arrowCode`-headed source and a `codataUnfold`-headed target
are not convertible.  Type-code (universe-encoded arrow type) versus
codata-elimination form — distinct canonical heads at the raw level. -/
theorem Conv.arrowCode_ne_codataUnfold
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {observer scrutinee : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.codataUnfold observer scrutinee : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, _, joinEqCodata, _, _⟩ :=
    RawStep.parStar.codataUnfold_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqCodata

/-- A `arrowCode`-headed source and a `cumulUpMarker`-headed target
are not convertible.  Type-code versus universe-cumulativity marker —
distinct canonical heads even though both are universe-level. -/
theorem Conv.arrowCode_ne_cumulUpMarker
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {innerCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.cumulUpMarker innerCode : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, joinEqCumul, _⟩ :=
    RawStep.parStar.cumulUpMarker_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqCumul

/-- A `arrowCode`-headed source and an `effectPerform`-headed target
are not convertible.  Type-code versus effect-performance form —
distinct canonical heads at the raw level. -/
theorem Conv.arrowCode_ne_effectPerform
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {operation payload : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.effectPerform operation payload : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, _, joinEqEffect, _, _⟩ :=
    RawStep.parStar.effectPerform_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqEffect

/-- A `arrowCode`-headed source and an `eitherCode`-headed target
are not convertible.  Both type-codes (universe-encoded type formers)
but for distinct families: arrow vs sum. -/
theorem Conv.arrowCode_ne_eitherCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.eitherCode leftCode rightCode : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, _, joinEqEither, _, _⟩ :=
    RawStep.parStar.eitherCode_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqEither

/-- A `arrowCode`-headed source and an `equivCode`-headed target
are not convertible.  Both type-codes but for distinct families:
arrow vs equivalence type. -/
theorem Conv.arrowCode_ne_equivCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {leftCode rightCode : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.equivCode leftCode rightCode : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, _, joinEqEquivC, _, _⟩ :=
    RawStep.parStar.equivCode_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqEquivC

/-- A `arrowCode`-headed source and an `equivCompose`-headed target
are not convertible.  Type-code versus equivalence-composition form
— distinct canonical heads at the raw level. -/
theorem Conv.arrowCode_ne_equivCompose
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {firstEquiv secondEquiv : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.equivCompose firstEquiv secondEquiv : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, _, joinEqEquivComp, _, _⟩ :=
    RawStep.parStar.equivCompose_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqEquivComp

/-- A `arrowCode`-headed source and an `equivIntro`-headed target
are not convertible.  Type-code versus equivalence-introduction form
— distinct canonical heads at the raw level. -/
theorem Conv.arrowCode_ne_equivIntro
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {forwardFn inverseFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.equivIntro forwardFn inverseFn : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, _, joinEqEquivIntro, _, _⟩ :=
    RawStep.parStar.equivIntro_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqEquivIntro

/-- A `arrowCode`-headed source and a `glueIntro`-headed target are
not convertible.  Type-code versus cubical-Glue-introduction form —
distinct canonical heads at the raw level. -/
theorem Conv.arrowCode_ne_glueIntro
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {domainCode codomainCode : RawTerm scope}
    {baseValue partialFn : RawTerm scope}
    {sourceTerm : Term context sourceType
      (RawTerm.arrowCode domainCode codomainCode : RawTerm scope)}
    {targetTerm : Term context targetType
      (RawTerm.glueIntro baseValue partialFn : RawTerm scope)} :
    ¬ Conv sourceTerm targetTerm := by
  intro convertibility
  obtain ⟨joinRaw, sourceToJoin, targetToJoin⟩ :=
    Conv.canonicalRaw convertibility
  obtain ⟨_, _, joinEqArrow, _, _⟩ :=
    RawStep.parStar.arrowCode_inv sourceToJoin
  obtain ⟨_, _, joinEqGlue, _, _⟩ :=
    RawStep.parStar.glueIntro_inv targetToJoin
  nomatch joinEqArrow.symm.trans joinEqGlue

end LeanFX2
