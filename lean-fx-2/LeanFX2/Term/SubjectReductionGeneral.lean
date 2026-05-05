import LeanFX2.Foundation.IsClosedTy
import LeanFX2.Reduction.StepStar

/-! # Term/SubjectReductionGeneral — IsClosedTy-indexed subject reduction

Generalizes the per-type SR cascade (`Step.preserves_ty_unit / bool /
nat`) to arbitrary closed types via the `IsClosedTy` predicate.

## Architecture

This file is the *single source of truth* for closed-type subject
reduction.  `Term/SubjectReduction.lean` re-exports the per-type
specializations (`Step.preserves_ty_unit / bool / nat`) as one-line
corollaries via `IsClosedTy.{unit, bool, nat}` witnesses.

## Building blocks

* `Ty.subst0_raw_invariance_unit / bool / nat` — leaf-case lemmas
  proving `T.subst0 α raw₁ = leafType → T.subst0 α raw₂ = leafType`.
  These are needed in the `unit`/`bool`/`nat` cases of the general
  invariance theorem.

## Headline lemma

`Ty.subst0_raw_invariance_isClosedTy` says: if
`someType.subst0 argType raw1 = closedType` for some `IsClosedTy
closedType`, then `someType.subst0 argType raw2 = closedType` for any
other `raw2`.

Proof: induction on `resultIsClosed`, the `IsClosedTy` witness.

* `unit`/`bool`/`nat` cases dispatch to the per-type invariance
  lemmas defined above.
* `arrow`/`listType`/`optionType`/`eitherType` cases case on
  `someType` (single level), use injectivity to extract inner
  reductions, and recurse via the IH on inner closed witnesses.

## Why induct on `resultIsClosed`, not `someType`

`someType : Ty level (scope + 1)` has a non-variable index (`scope +
1`) which blocks Lean's `induction` tactic per pitfall P-2.
Inducting on `resultIsClosed : IsClosedTy closedType` instead places
the recursion at the closed-witness level — `closedType : Ty level
scope` has free variable indices, so induction works cleanly.  The
IH for inner closed witnesses (e.g., `closedDomain` inside
`IsClosedTy.arrow closedDomain closedCodomain`) is exactly the
inductive-hypothesis form we need for the recursive `Ty.arrow d c`
sub-case.

## Pitfalls + mitigations

* P-1 (match-compiler propext on big inductives): full enumeration
  of `Ty` ctors via `cases someType with | ctor1 => ... | ctor2 =>
  ...` (no wildcards).
* P-2 (multi-Nat-index propext): scope-shifted index sidestepped
  via induction on `resultIsClosed` rather than `someType`.

## Downstream consumers

* `Step.preserves_isClosedTy` (later in this file) — uses the
  invariance lemma in the β-rule case.
* `StepStar.preserves_isClosedTy` — chain extension.
* M06/M07 (#1275/#1276) — closed by `Step.preserves_ty_arrow /
  listType / optionType / eitherType` corollaries.
* `Term/SubjectReduction.lean` — re-exports per-type specializations.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## Substitution invariance for closed-type leaves

These three theorems are the building blocks for the general
`Ty.subst0_raw_invariance_isClosedTy`.  Each handles one leaf
ctor (`unit`, `bool`, `nat`) by case analysis on `someType` — the
result type fixes the ctor uniquely except when `someType` is a
`tyVar 0` looking up to the leaf via the singleton substitution. -/

/-- Substitution-raw-invariance for `Ty.unit`.  If `someType`'s
single-variable substitution reduces to `Ty.unit`, the choice of
raw argument is irrelevant.  Discharged by case analysis on
`someType` — only `Ty.unit` and `Ty.tyVar ⟨0, _⟩` survive the
filter. -/
theorem Ty.subst0_raw_invariance_unit
    {someType : Ty level (scope + 1)} {argType : Ty level scope}
    {raw1 raw2 : RawTerm scope}
    (someTypeReducesToUnit : someType.subst0 argType raw1 = Ty.unit) :
    someType.subst0 argType raw2 = Ty.unit := by
  cases someType with
  | unit => rfl
  | bool => nomatch someTypeReducesToUnit
  | nat => nomatch someTypeReducesToUnit
  | arrow _ _ => nomatch someTypeReducesToUnit
  | piTy _ _ => nomatch someTypeReducesToUnit
  | sigmaTy _ _ => nomatch someTypeReducesToUnit
  | tyVar position =>
    cases position with
    | mk val isLt =>
      cases val with
      | zero => exact someTypeReducesToUnit
      | succ k => nomatch someTypeReducesToUnit
  | id _ _ _ => nomatch someTypeReducesToUnit
  | listType _ => nomatch someTypeReducesToUnit
  | optionType _ => nomatch someTypeReducesToUnit
  | eitherType _ _ => nomatch someTypeReducesToUnit
  | empty => nomatch someTypeReducesToUnit
  | interval => nomatch someTypeReducesToUnit
  | path _ _ _ => nomatch someTypeReducesToUnit
  | glue _ _ => nomatch someTypeReducesToUnit
  | oeq _ _ _ => nomatch someTypeReducesToUnit
  | idStrict _ _ _ => nomatch someTypeReducesToUnit
  | equiv _ _ => nomatch someTypeReducesToUnit
  | refine _ _ => nomatch someTypeReducesToUnit
  | record _ => nomatch someTypeReducesToUnit
  | codata _ _ => nomatch someTypeReducesToUnit
  | session _ => nomatch someTypeReducesToUnit
  | effect _ _ => nomatch someTypeReducesToUnit
  | modal _ _ => nomatch someTypeReducesToUnit
  | «universe» _ _ => nomatch someTypeReducesToUnit

/-- Substitution-raw-invariance for `Ty.bool`. -/
theorem Ty.subst0_raw_invariance_bool
    {someType : Ty level (scope + 1)} {argType : Ty level scope}
    {raw1 raw2 : RawTerm scope}
    (someTypeReducesToBool : someType.subst0 argType raw1 = Ty.bool) :
    someType.subst0 argType raw2 = Ty.bool := by
  cases someType with
  | unit => nomatch someTypeReducesToBool
  | bool => rfl
  | nat => nomatch someTypeReducesToBool
  | arrow _ _ => nomatch someTypeReducesToBool
  | piTy _ _ => nomatch someTypeReducesToBool
  | sigmaTy _ _ => nomatch someTypeReducesToBool
  | tyVar position =>
    cases position with
    | mk val isLt =>
      cases val with
      | zero => exact someTypeReducesToBool
      | succ k => nomatch someTypeReducesToBool
  | id _ _ _ => nomatch someTypeReducesToBool
  | listType _ => nomatch someTypeReducesToBool
  | optionType _ => nomatch someTypeReducesToBool
  | eitherType _ _ => nomatch someTypeReducesToBool
  | empty => nomatch someTypeReducesToBool
  | interval => nomatch someTypeReducesToBool
  | path _ _ _ => nomatch someTypeReducesToBool
  | glue _ _ => nomatch someTypeReducesToBool
  | oeq _ _ _ => nomatch someTypeReducesToBool
  | idStrict _ _ _ => nomatch someTypeReducesToBool
  | equiv _ _ => nomatch someTypeReducesToBool
  | refine _ _ => nomatch someTypeReducesToBool
  | record _ => nomatch someTypeReducesToBool
  | codata _ _ => nomatch someTypeReducesToBool
  | session _ => nomatch someTypeReducesToBool
  | effect _ _ => nomatch someTypeReducesToBool
  | modal _ _ => nomatch someTypeReducesToBool
  | «universe» _ _ => nomatch someTypeReducesToBool

/-- Substitution-raw-invariance for `Ty.nat`. -/
theorem Ty.subst0_raw_invariance_nat
    {someType : Ty level (scope + 1)} {argType : Ty level scope}
    {raw1 raw2 : RawTerm scope}
    (someTypeReducesToNat : someType.subst0 argType raw1 = Ty.nat) :
    someType.subst0 argType raw2 = Ty.nat := by
  cases someType with
  | unit => nomatch someTypeReducesToNat
  | bool => nomatch someTypeReducesToNat
  | nat => rfl
  | arrow _ _ => nomatch someTypeReducesToNat
  | piTy _ _ => nomatch someTypeReducesToNat
  | sigmaTy _ _ => nomatch someTypeReducesToNat
  | tyVar position =>
    cases position with
    | mk val isLt =>
      cases val with
      | zero => exact someTypeReducesToNat
      | succ k => nomatch someTypeReducesToNat
  | id _ _ _ => nomatch someTypeReducesToNat
  | listType _ => nomatch someTypeReducesToNat
  | optionType _ => nomatch someTypeReducesToNat
  | eitherType _ _ => nomatch someTypeReducesToNat
  | empty => nomatch someTypeReducesToNat
  | interval => nomatch someTypeReducesToNat
  | path _ _ _ => nomatch someTypeReducesToNat
  | glue _ _ => nomatch someTypeReducesToNat
  | oeq _ _ _ => nomatch someTypeReducesToNat
  | idStrict _ _ _ => nomatch someTypeReducesToNat
  | equiv _ _ => nomatch someTypeReducesToNat
  | refine _ _ => nomatch someTypeReducesToNat
  | record _ => nomatch someTypeReducesToNat
  | codata _ _ => nomatch someTypeReducesToNat
  | session _ => nomatch someTypeReducesToNat
  | effect _ _ => nomatch someTypeReducesToNat
  | modal _ _ => nomatch someTypeReducesToNat
  | «universe» _ _ => nomatch someTypeReducesToNat

/-- Generalized substitution-raw-invariance.  For any `someType : Ty
level (scope+1)`, if `someType.subst0 argType raw1` equals a closed
type, then `someType.subst0 argType raw2` equals the same closed
type — closed types contain no `Ty.id` endpoints, so the raw
substitution component is irrelevant.

Proof by induction on the closed witness (`resultIsClosed`); the
`someType`-shape cases dispatch via single-level `cases someType`. -/
theorem Ty.subst0_raw_invariance_isClosedTy {level scope : Nat}
    (someType : Ty level (scope + 1))
    (argType : Ty level scope)
    (raw1 raw2 : RawTerm scope)
    {closedType : Ty level scope}
    (resultIsClosed : IsClosedTy closedType)
    (someTypeReduces : someType.subst0 argType raw1 = closedType) :
    someType.subst0 argType raw2 = closedType := by
  induction resultIsClosed generalizing someType raw1 raw2 with
  | unit =>
      exact Ty.subst0_raw_invariance_unit someTypeReduces
  | bool =>
      exact Ty.subst0_raw_invariance_bool someTypeReduces
  | nat =>
      exact Ty.subst0_raw_invariance_nat someTypeReduces
  | arrow closedDomain closedCodomain ihDomain ihCodomain =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow domainSrc codomainSrc =>
          injection someTypeReduces with _ hDomain hCodomain
          have domainInv := ihDomain domainSrc raw1 raw2 hDomain
          have codomainInv := ihCodomain codomainSrc raw1 raw2 hCodomain
          show Ty.arrow (domainSrc.subst0 argType raw2)
                        (codomainSrc.subst0 argType raw2) = _
          rw [domainInv, codomainInv]
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
      | empty => nomatch someTypeReduces
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» _ _ => nomatch someTypeReduces
  | listType closedElement ihElement =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType elementSrc =>
          injection someTypeReduces with _ hElement
          have elementInv := ihElement elementSrc raw1 raw2 hElement
          show Ty.listType (elementSrc.subst0 argType raw2) = _
          rw [elementInv]
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
      | empty => nomatch someTypeReduces
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» _ _ => nomatch someTypeReduces
  | optionType closedElement ihElement =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType elementSrc =>
          injection someTypeReduces with _ hElement
          have elementInv := ihElement elementSrc raw1 raw2 hElement
          show Ty.optionType (elementSrc.subst0 argType raw2) = _
          rw [elementInv]
      | eitherType _ _ => nomatch someTypeReduces
      | empty => nomatch someTypeReduces
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» _ _ => nomatch someTypeReduces
  | eitherType closedLeft closedRight ihLeft ihRight =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType leftSrc rightSrc =>
          injection someTypeReduces with _ hLeft hRight
          have leftInv := ihLeft leftSrc raw1 raw2 hLeft
          have rightInv := ihRight rightSrc raw1 raw2 hRight
          show Ty.eitherType (leftSrc.subst0 argType raw2)
                              (rightSrc.subst0 argType raw2) = _
          rw [leftInv, rightInv]
      | empty => nomatch someTypeReduces
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» _ _ => nomatch someTypeReduces
  -- D1.5 new IsClosedTy ctors — analogous treatment.
  | empty =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
      | empty => rfl
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» _ _ => nomatch someTypeReduces
  | interval =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
      | empty => nomatch someTypeReduces
      | interval => rfl
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» _ _ => nomatch someTypeReduces
  | equiv closedDomain closedCodomain ihDomain ihCodomain =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
      | empty => nomatch someTypeReduces
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv domainSrc codomainSrc =>
          injection someTypeReduces with _ hDomain hCodomain
          have domainInv := ihDomain domainSrc raw1 raw2 hDomain
          have codomainInv := ihCodomain codomainSrc raw1 raw2 hCodomain
          show Ty.equiv (domainSrc.subst0 argType raw2)
                        (codomainSrc.subst0 argType raw2) = _
          rw [domainInv, codomainInv]
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» _ _ => nomatch someTypeReduces
  | record closedSingleField ihSingleField =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
      | empty => nomatch someTypeReduces
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record singleFieldSrc =>
          injection someTypeReduces with _ hSingleField
          have singleFieldInv :=
            ihSingleField singleFieldSrc raw1 raw2 hSingleField
          show Ty.record (singleFieldSrc.subst0 argType raw2) = _
          rw [singleFieldInv]
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» _ _ => nomatch someTypeReduces
  | codata closedState closedOutput ihState ihOutput =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
      | empty => nomatch someTypeReduces
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata stateSrc outputSrc =>
          injection someTypeReduces with _ hState hOutput
          have stateInv := ihState stateSrc raw1 raw2 hState
          have outputInv := ihOutput outputSrc raw1 raw2 hOutput
          show Ty.codata (stateSrc.subst0 argType raw2)
                          (outputSrc.subst0 argType raw2) = _
          rw [stateInv, outputInv]
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» _ _ => nomatch someTypeReduces
  | modal closedCarrier ihCarrier =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
      | empty => nomatch someTypeReduces
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal modalityTagSrc carrierSrc =>
          -- D1.5: Ty.modal injects on (tag, carrier).  After cases, the
          -- tag is unified with modalityTag, leaving carrier as the only
          -- thing to drive via IH.
          cases someTypeReduces
          have carrierInv := ihCarrier carrierSrc raw1 raw2 rfl
          show Ty.modal _ (carrierSrc.subst0 argType raw2) = _
          rw [carrierInv]
      | «universe» _ _ => nomatch someTypeReduces
  | «universe» universeLevel levelLe =>
      cases someType with
      | unit => nomatch someTypeReduces
      | bool => nomatch someTypeReduces
      | nat  => nomatch someTypeReduces
      | tyVar position =>
          cases position with
          | mk val isLt =>
              cases val with
              | zero => exact someTypeReduces
              | succ _ => nomatch someTypeReduces
      | arrow _ _ => nomatch someTypeReduces
      | piTy _ _ => nomatch someTypeReduces
      | sigmaTy _ _ => nomatch someTypeReduces
      | id _ _ _ => nomatch someTypeReduces
      | listType _ => nomatch someTypeReduces
      | optionType _ => nomatch someTypeReduces
      | eitherType _ _ => nomatch someTypeReduces
      | empty => nomatch someTypeReduces
      | interval => nomatch someTypeReduces
      | path _ _ _ => nomatch someTypeReduces
      | glue _ _ => nomatch someTypeReduces
      | oeq _ _ _ => nomatch someTypeReduces
      | idStrict _ _ _ => nomatch someTypeReduces
      | equiv _ _ => nomatch someTypeReduces
      | refine _ _ => nomatch someTypeReduces
      | record _ => nomatch someTypeReduces
      | codata _ _ => nomatch someTypeReduces
      | session _ => nomatch someTypeReduces
      | effect _ _ => nomatch someTypeReduces
      | modal _ _ => nomatch someTypeReduces
      | «universe» universeLevelSrc levelLeSrc =>
          -- D1.2: Ty.universe injects on its UniverseLevel payload (the
          -- propositional-inequality field is irrelevant by Prop subsingleton).
          -- cases unifies universeLevelSrc with universeLevel; subst on
          -- Ty.universe is a no-op so both raw substitutions agree.
          cases someTypeReduces
          rfl

/-! ## Generalized step-preservation theorem

`Step.preserves_isClosedTy` follows the established tactic-combo
pattern from `Step.preserves_ty_unit / bool / nat`: induction on
the Step, dispatch each constructor case via `first` over four
tactic fallbacks.  The 4th fallback uses the new general invariance
lemma. -/

/-- Generalized subject reduction: every `Step` from a closed-typed
source produces a target with the same closed type.  Replaces the
per-type `Step.preserves_ty_unit / bool / nat` cascade with a single
inductive proof parameterized by the closed witness. -/
theorem Step.preserves_isClosedTy
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {closedType : Ty level scope}
    (sourceClosed : IsClosedTy closedType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsClosed : sourceType = closedType) :
    targetType = closedType := by
  induction someStep
  all_goals
    first
      | exact sourceIsClosed
      | (subst sourceIsClosed; rfl)
      | rfl
      | exact Ty.subst0_raw_invariance_isClosedTy _ _ _ _
                sourceClosed sourceIsClosed
      | (subst sourceIsClosed; exact Ty.weaken_subst_singleton _ _ _)
      | -- Fallback for type-changing reductions (Step.eqType, Step.eqArrow)
        -- whose source type (Ty.id, Ty.piTy etc.) is not in IsClosedTy:
        -- substituting the source-equality through `sourceClosed` makes
        -- it contradictory, so `cases sourceClosed` discharges the goal.
        (subst sourceIsClosed; cases sourceClosed)

/-- StepStar lift of `Step.preserves_isClosedTy`: closed-typed
StepStar chains preserve the closed target type.  Trivial chain
induction on the head + tail. -/
theorem StepStar.preserves_isClosedTy
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {closedType : Ty level scope}
    (sourceClosed : IsClosedTy closedType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsClosed : sourceType = closedType) :
    targetType = closedType := by
  induction chain with
  | refl _ => exact sourceIsClosed
  | step head _ tailIH =>
      exact tailIH (Step.preserves_isClosedTy sourceClosed head sourceIsClosed)

/-! ## Generic chain lifter at closed sub-position

`StepStar.lift_at_isClosedTy` is the workhorse for cong rules
that lift a `StepStar` chain on a sub-position (typed at a
closed `closedTy`) to a `StepStar` chain on the wrapped term.
The proof template is identical for every cong ctor: induct on
the chain, dispatch refl + step cases, use
`Step.preserves_isClosedTy` in the step case.  Variable parts
are exactly the wrapper Term function and the Step cong ctor.

Used by: `StepStar.{natSucc, boolElimScrutinee, natElimScrutinee,
natRecScrutinee, idJ_baseCase, optionSomeValue, listConsHead,
listConsTail, eitherInlValue, eitherInrValue}_lift_*`.

Per-ctor lifters specialize this helper at their wrapper +
Step cong ctor — each becomes a 1-step parameterization. -/

/-- Lift a `StepStar` chain at a closed sub-position to a
`StepStar` chain on the wrapped term, given the wrapper Term
function and its Step cong rule.  Proof is by induction on the
chain; the step case bridges the existential intermediate type
back to `closedTy` via `Step.preserves_isClosedTy`. -/
theorem StepStar.lift_at_isClosedTy
    {closedTy resultTy : Ty level scope}
    (closedTyIsClosed : IsClosedTy closedTy)
    {wrapRaw : RawTerm scope → RawTerm scope}
    (wrap : ∀ {raw : RawTerm scope}, Term context closedTy raw →
            Term context resultTy (wrapRaw raw))
    (stepWrap : ∀ {sourceRaw targetRaw : RawTerm scope}
                 {sourceTerm : Term context closedTy sourceRaw}
                 {targetTerm : Term context closedTy targetRaw},
                 Step sourceTerm targetTerm →
                 Step (wrap sourceTerm) (wrap targetTerm))
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsClosed : srcTy = closedTy)
    (tgtIsClosed : tgtTy = closedTy) :
    StepStar (wrap (srcIsClosed ▸ srcTerm))
             (wrap (tgtIsClosed ▸ tgtTerm)) := by
  induction someChain with
  | refl _ =>
      cases srcIsClosed
      cases tgtIsClosed
      exact StepStar.refl _
  | step head _ tailIH =>
      have midIsClosed : _ = closedTy :=
        Step.preserves_isClosedTy closedTyIsClosed head srcIsClosed
      cases srcIsClosed
      cases midIsClosed
      exact StepStar.step (stepWrap head) (tailIH rfl tgtIsClosed)

/-! ## Specialized SR for closed-type families

Closes kernel-sprint M06 (#1275 — SR at arrow types) and M07
(#1276 — SR at parametric types: listType, optionType,
eitherType).  Each is a one-line corollary of
`Step.preserves_isClosedTy` (and StepStar variant), instantiated
at the matching `IsClosedTy` ctor with closed-component
witnesses.

These lemmas only apply when the type's *components* are also
closed.  For `Ty.arrow Ty.nat Ty.bool` this is trivial; for
`Ty.arrow (Ty.tyVar 0) Ty.bool` it is not, and a deeper SR
(general open-types Phase 7.D) is needed.  Most user-visible
arrow types in compiled FX are concrete and fall in scope.
-/

/-- Subject reduction at `Ty.arrow domain codomain` when both
component types are closed.  Closes M06 (#1275). -/
theorem Step.preserves_ty_arrow
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {domainType codomainType : Ty level scope}
    (closedDomain : IsClosedTy domainType)
    (closedCodomain : IsClosedTy codomainType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsArrow : sourceType = Ty.arrow domainType codomainType) :
    targetType = Ty.arrow domainType codomainType :=
  Step.preserves_isClosedTy
    (IsClosedTy.arrow closedDomain closedCodomain) someStep sourceIsArrow

/-- StepStar lift of `Step.preserves_ty_arrow`. -/
theorem StepStar.preserves_ty_arrow
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {domainType codomainType : Ty level scope}
    (closedDomain : IsClosedTy domainType)
    (closedCodomain : IsClosedTy codomainType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsArrow : sourceType = Ty.arrow domainType codomainType) :
    targetType = Ty.arrow domainType codomainType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.arrow closedDomain closedCodomain) chain sourceIsArrow

/-- Subject reduction at `Ty.listType element` when element type
is closed.  First half of M07 (#1276). -/
theorem Step.preserves_ty_listType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsList : sourceType = Ty.listType elementType) :
    targetType = Ty.listType elementType :=
  Step.preserves_isClosedTy
    (IsClosedTy.listType closedElement) someStep sourceIsList

/-- StepStar lift of `Step.preserves_ty_listType`. -/
theorem StepStar.preserves_ty_listType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsList : sourceType = Ty.listType elementType) :
    targetType = Ty.listType elementType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.listType closedElement) chain sourceIsList

/-- Subject reduction at `Ty.optionType element` when element
type is closed.  Second half of M07 (#1276). -/
theorem Step.preserves_ty_optionType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsOption : sourceType = Ty.optionType elementType) :
    targetType = Ty.optionType elementType :=
  Step.preserves_isClosedTy
    (IsClosedTy.optionType closedElement) someStep sourceIsOption

/-- StepStar lift of `Step.preserves_ty_optionType`. -/
theorem StepStar.preserves_ty_optionType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {elementType : Ty level scope}
    (closedElement : IsClosedTy elementType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsOption : sourceType = Ty.optionType elementType) :
    targetType = Ty.optionType elementType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.optionType closedElement) chain sourceIsOption

/-- Subject reduction at `Ty.eitherType left right` when both
component types are closed.  Third half of M07 (#1276). -/
theorem Step.preserves_ty_eitherType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {leftType rightType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    (closedRight : IsClosedTy rightType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsEither : sourceType = Ty.eitherType leftType rightType) :
    targetType = Ty.eitherType leftType rightType :=
  Step.preserves_isClosedTy
    (IsClosedTy.eitherType closedLeft closedRight) someStep sourceIsEither

/-- StepStar lift of `Step.preserves_ty_eitherType`. -/
theorem StepStar.preserves_ty_eitherType
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {leftType rightType : Ty level scope}
    (closedLeft : IsClosedTy leftType)
    (closedRight : IsClosedTy rightType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsEither : sourceType = Ty.eitherType leftType rightType) :
    targetType = Ty.eitherType leftType rightType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.eitherType closedLeft closedRight) chain sourceIsEither

/-! ## D1.5 closed-ctor SR specializations

The general theorem already handles every `IsClosedTy` constructor.
These corollaries expose the newer closed type formers through the
same API shape as arrow/list/option/either, so downstream Day 2
callers do not have to construct the closed witness manually. -/

/-- Subject reduction at `Ty.empty`. -/
theorem Step.preserves_ty_empty
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceIsEmpty : sourceType = Ty.empty) :
    targetType = Ty.empty :=
  Step.preserves_isClosedTy IsClosedTy.empty someStep sourceIsEmpty

/-- StepStar lift of `Step.preserves_ty_empty`. -/
theorem StepStar.preserves_ty_empty
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsEmpty : sourceType = Ty.empty) :
    targetType = Ty.empty :=
  StepStar.preserves_isClosedTy IsClosedTy.empty chain sourceIsEmpty

/-- Subject reduction at `Ty.interval`. -/
theorem Step.preserves_ty_interval
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceIsInterval : sourceType = Ty.interval) :
    targetType = Ty.interval :=
  Step.preserves_isClosedTy IsClosedTy.interval someStep sourceIsInterval

/-- StepStar lift of `Step.preserves_ty_interval`. -/
theorem StepStar.preserves_ty_interval
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsInterval : sourceType = Ty.interval) :
    targetType = Ty.interval :=
  StepStar.preserves_isClosedTy IsClosedTy.interval chain sourceIsInterval

/-- Subject reduction at `Ty.equiv domain codomain` when both component
types are closed. -/
theorem Step.preserves_ty_equiv
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {domainType codomainType : Ty level scope}
    (closedDomain : IsClosedTy domainType)
    (closedCodomain : IsClosedTy codomainType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsEquiv : sourceType = Ty.equiv domainType codomainType) :
    targetType = Ty.equiv domainType codomainType :=
  Step.preserves_isClosedTy
    (IsClosedTy.equiv closedDomain closedCodomain) someStep sourceIsEquiv

/-- StepStar lift of `Step.preserves_ty_equiv`. -/
theorem StepStar.preserves_ty_equiv
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {domainType codomainType : Ty level scope}
    (closedDomain : IsClosedTy domainType)
    (closedCodomain : IsClosedTy codomainType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsEquiv : sourceType = Ty.equiv domainType codomainType) :
    targetType = Ty.equiv domainType codomainType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.equiv closedDomain closedCodomain) chain sourceIsEquiv

/-- Subject reduction at the current single-field `Ty.record` encoding
when the field type is closed.  Completes the record branch of M07. -/
theorem Step.preserves_ty_record
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {singleFieldType : Ty level scope}
    (closedSingleField : IsClosedTy singleFieldType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsRecord : sourceType = Ty.record singleFieldType) :
    targetType = Ty.record singleFieldType :=
  Step.preserves_isClosedTy
    (IsClosedTy.record closedSingleField) someStep sourceIsRecord

/-- StepStar lift of `Step.preserves_ty_record`. -/
theorem StepStar.preserves_ty_record
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {singleFieldType : Ty level scope}
    (closedSingleField : IsClosedTy singleFieldType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsRecord : sourceType = Ty.record singleFieldType) :
    targetType = Ty.record singleFieldType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.record closedSingleField) chain sourceIsRecord

/-- Subject reduction at `Ty.codata state output` when both component
types are closed. -/
theorem Step.preserves_ty_codata
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {stateType outputType : Ty level scope}
    (closedState : IsClosedTy stateType)
    (closedOutput : IsClosedTy outputType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsCodata : sourceType = Ty.codata stateType outputType) :
    targetType = Ty.codata stateType outputType :=
  Step.preserves_isClosedTy
    (IsClosedTy.codata closedState closedOutput) someStep sourceIsCodata

/-- StepStar lift of `Step.preserves_ty_codata`. -/
theorem StepStar.preserves_ty_codata
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {stateType outputType : Ty level scope}
    (closedState : IsClosedTy stateType)
    (closedOutput : IsClosedTy outputType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsCodata : sourceType = Ty.codata stateType outputType) :
    targetType = Ty.codata stateType outputType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.codata closedState closedOutput) chain sourceIsCodata

/-- Subject reduction at `Ty.modal modalityTag carrier` when the carrier
type is closed. -/
theorem Step.preserves_ty_modal
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {modalityTag : Nat}
    {carrierType : Ty level scope}
    (closedCarrier : IsClosedTy carrierType)
    (someStep : Step sourceTerm targetTerm)
    (sourceIsModal : sourceType = Ty.modal modalityTag carrierType) :
    targetType = Ty.modal modalityTag carrierType :=
  Step.preserves_isClosedTy
    (IsClosedTy.modal closedCarrier) someStep sourceIsModal

/-- StepStar lift of `Step.preserves_ty_modal`. -/
theorem StepStar.preserves_ty_modal
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {modalityTag : Nat}
    {carrierType : Ty level scope}
    (closedCarrier : IsClosedTy carrierType)
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsModal : sourceType = Ty.modal modalityTag carrierType) :
    targetType = Ty.modal modalityTag carrierType :=
  StepStar.preserves_isClosedTy
    (IsClosedTy.modal closedCarrier) chain sourceIsModal

/-! ## Conv-level preservation at closed types — DEFERRED

A `Conv.preserves_isClosedTy` corollary would lift SR through
both sides of a Conv: if `Conv source target` and `source` has
a closed type, then `target` has the same closed type.

Naive proof attempt extracts the existential common reduct and
applies `StepStar.preserves_isClosedTy` forward to constrain the
middle's type — but the target side requires REVERSE SR (chain
goes from target to middle; we need to deduce target's type
from middle's type).

Reverse SR for arbitrary `Step` rules is provable but
non-trivial: each Step rule's source/target type relationship
must be inspected.  Most cong rules have `srcType = tgtType`
definitionally (forward = reverse).  βι rules have a propositional
equality (`Ty.weaken_subst_singleton` for βapp, etc.) — reverse
proof mirrors forward.

Deferred to a future structural phase.  Use case-by-case forward
SR via `StepStar.preserves_isClosedTy` at consumer sites (which
is what `Conv.cong_at_isClosedTy` already does for cong rules
via the source-side chain). -/

end LeanFX2
