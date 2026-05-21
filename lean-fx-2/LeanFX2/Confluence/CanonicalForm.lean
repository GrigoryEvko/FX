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

end LeanFX2
