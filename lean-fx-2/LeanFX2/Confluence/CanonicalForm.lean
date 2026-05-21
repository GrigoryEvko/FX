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

end LeanFX2
