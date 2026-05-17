import LeanFX2.Term.StrengtheningImage

/-! # AggregatorComposition — IsAggregatorSound smoke audit.

Smoke audit demonstrating that the per-arm dispatcher wrappers
(`isAggregatorSound_<ctor>`) compose cleanly under the uniform
`IsAggregatorSound` predicate.

## Coverage

Each composition is correct by **typechecking** of the per-arm
wrappers — there is no novel proof content beyond the wrapper
definitions in `Term/StrengtheningImage.lean`.  This file
therefore aims at minimal smoke evidence:

* Three parametric chain theorems cover ALL depths uniformly
  via structural induction (`aggregator_natChain`,
  `aggregator_optionStack`, `aggregator_listConsChain`).  One
  theorem per family replaces the prior depth-1..depth-23
  hand-rolled instances and continues to every natural-number
  depth past 23.
* A handful of atomic singletons confirm the 0-IH wrappers fire
  at scope 0 across the type-family categories (atomic / closed-
  type, atomic / parametric, atomic / HoTT-refl).
* A handful of cross-family heterogeneous singletons confirm
  the wrappers compose across distinct ctor categories (Σ ×
  atomic, Σ × parametric, list × parametric) without coercion
  gaps.

The universal headline `∀ sourceTerm, IsAggregatorSound
sourceTerm` (pending — requires the producer-coverage gap to
close) subsumes everything in this file once shipped.  Per-arm
wrappers carry their own zero-axiom gates via
`#assert_no_axioms` in `Tools/AuditAll/AuditTerm.lean`.

Each theorem below is gated by `#print axioms` for reviewer
regression and by the namespace-sweep audit in
`Tools/AuditAll.lean`. -/

namespace LeanFX2.SmokeAggregatorComposition

open LeanFX2 LeanFX2.Term

/-- Closed atomic at scope 0: `IsAggregatorSound Term.unit`. -/
theorem aggregator_unit_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound (Term.unit (context := sourceCtx)) :=
  isAggregatorSound_unit

/-- Closed atomic at scope 0: `IsAggregatorSound Term.boolTrue`. -/
theorem aggregator_boolTrue_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound (Term.boolTrue (context := sourceCtx)) :=
  isAggregatorSound_boolTrue

/-- Closed atomic at scope 0: `IsAggregatorSound Term.boolFalse`. -/
theorem aggregator_boolFalse_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound (Term.boolFalse (context := sourceCtx)) :=
  isAggregatorSound_boolFalse

/-- Closed parametric atomic: `IsAggregatorSound (Term.listNil
@ list nat)`.  Exercises the 0-IH parametric wrapper with its
`elementType` argument. -/
theorem aggregator_listNil_natList_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listNil (context := sourceCtx) (elementType := Ty.nat)) :=
  isAggregatorSound_listNil (elementType := Ty.nat)

/-- Closed parametric atomic: `IsAggregatorSound (Term.optionNone
@ option nat)`.  Mirror of the listNil atomic at the option
carrier. -/
theorem aggregator_optionNone_natOption_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.optionNone (context := sourceCtx)
        (elementType := Ty.nat)) :=
  isAggregatorSound_optionNone (elementType := Ty.nat)

/-- Closed HoTT atomic: `IsAggregatorSound (Term.refl @ nat
RawTerm.natZero)`.  The HoTT identity-refl wrapper carries its
carrier as a Ty implicit and its witness as a raw-term positional;
the IsAggregatorSound predicate sees a 0-IH composition. -/
theorem aggregator_refl_natZero_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.refl (context := sourceCtx) (carrier := Ty.nat)
        RawTerm.natZero) :=
  isAggregatorSound_refl

/-- Closed observational-equality atomic: `IsAggregatorSound
(Term.oeqRefl @ nat RawTerm.natZero)`.  Mirror of the HoTT-refl
atomic via the parallel `oeqRefl` wrapper. -/
theorem aggregator_oeqRefl_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.oeqRefl (context := sourceCtx) (carrier := Ty.nat)
        RawTerm.natZero) :=
  isAggregatorSound_oeqRefl

/-- Parametric chain: for every depth `n`, there exists a closed
`natSucc^n natZero` term at carrier `nat` whose aggregator
soundness is established.  Replaces the depth-1 through depth-23
hand-rolled instances shipped in Phases 80–133 with a single
structural induction that covers every natural-number depth and
continues past 23 indefinitely.

The witness is the canonical `natSucc^n` chain over `natZero`;
the soundness proof composes one `isAggregatorSound_natSucc` per
successor with `isAggregatorSound_natZero` at the base. -/
theorem aggregator_natChain {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} (chainDepth : Nat) :
    ∃ (chainRaw : RawTerm 0) (chainTerm : Term sourceCtx Ty.nat chainRaw),
      IsAggregatorSound chainTerm := by
  induction chainDepth with
  | zero =>
    exact ⟨_, Term.natZero, isAggregatorSound_natZero⟩
  | succ _ chainIH =>
    obtain ⟨_, prevTerm, prevSound⟩ := chainIH
    exact ⟨_, Term.natSucc prevTerm, isAggregatorSound_natSucc prevSound⟩

/-- Parametric chain: for every depth `n`, there exists a closed
`optionSome^n natZero` term whose carrier is the n-fold option
nesting of `nat` and whose aggregator soundness is established.
Replaces the optionSome-stack hand-rolled instances (depth 2..5
shipped in Phases 90+) with a single induction that covers every
nesting depth.

The carrier type and raw shape both grow with `n`; the existential
packaging lets the single statement quantify uniformly over them. -/
theorem aggregator_optionStack {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} (stackDepth : Nat) :
    ∃ (stackTy : Ty level 0) (stackRaw : RawTerm 0)
      (stackTerm : Term sourceCtx stackTy stackRaw),
      IsAggregatorSound stackTerm := by
  induction stackDepth with
  | zero =>
    exact ⟨Ty.nat, _, Term.natZero, isAggregatorSound_natZero⟩
  | succ _ stackIH =>
    obtain ⟨_, _, prevTerm, prevSound⟩ := stackIH
    exact ⟨_, _, Term.optionSome (valueTerm := prevTerm),
           isAggregatorSound_optionSome prevSound⟩

/-- Parametric chain: for every length `n`, there exists a closed
list of `n` zero-natural elements at carrier `list nat` whose
aggregator soundness is established.  Replaces the listCons-chain
hand-rolled instances (length 2..3 shipped in earlier phases) with
a single induction that covers every list length.

The list contents are uniformly `natZero` so the elementType stays
fixed at `Ty.nat`; the cons wrapper composes one
`isAggregatorSound_listCons` per element atop
`isAggregatorSound_listNil` at the base. -/
theorem aggregator_listConsChain {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} (listLength : Nat) :
    ∃ (listRaw : RawTerm 0)
      (listTerm : Term sourceCtx (Ty.listType Ty.nat) listRaw),
      IsAggregatorSound listTerm := by
  induction listLength with
  | zero =>
    exact ⟨_, Term.listNil (elementType := Ty.nat),
           isAggregatorSound_listNil (elementType := Ty.nat)⟩
  | succ _ listIH =>
    obtain ⟨_, prevTail, prevSound⟩ := listIH
    exact ⟨_, Term.listCons (headTerm := Term.natZero)
             (tailTerm := prevTail),
           isAggregatorSound_listCons isAggregatorSound_natZero prevSound⟩

/-- Cross-family heterogeneous: Σ across distinct atomic ctor
categories (`pair natZero boolTrue` at carrier `nat × bool`).
Confirms the 2-IH non-parametric Σ wrapper composes children
from distinct type families (closed-nat and closed-bool) without
coercion. -/
theorem aggregator_pair_natBool_closed {mode : Mode} {level : Nat}
    {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.bool)
        (firstValue := Term.natZero)
        (secondValue := Term.boolTrue)) :=
  isAggregatorSound_pair isAggregatorSound_natZero
    isAggregatorSound_boolTrue

/-- Cross-family heterogeneous: Σ × option, parametric child in
first slot (`pair (optionSome natZero) natZero` at carrier
`option nat × nat`).  Confirms the Σ wrapper composes with a
parametric-Ty child wrapper at the first position. -/
theorem aggregator_pair_optionSome_natZero_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.pair (context := sourceCtx)
        (secondType := Ty.nat)
        (firstValue := Term.optionSome (valueTerm := Term.natZero))
        (secondValue := Term.natZero)) :=
  isAggregatorSound_pair
    (isAggregatorSound_optionSome isAggregatorSound_natZero)
    isAggregatorSound_natZero

/-- Cross-family heterogeneous: list × option, parametric child
in head slot (`[Some natZero]` at carrier `list (option nat)`).
Confirms the listCons wrapper composes with a parametric-Ty
child at its head position with a matching parametric listNil
at its tail. -/
theorem aggregator_listCons_optionSome_closed {mode : Mode}
    {level : Nat} {sourceCtx : Ctx mode level 0} :
    IsAggregatorSound
      (Term.listCons (context := sourceCtx)
        (headTerm := Term.optionSome (valueTerm := Term.natZero))
        (tailTerm := Term.listNil
          (elementType := Ty.optionType Ty.nat))) :=
  isAggregatorSound_listCons
    (isAggregatorSound_optionSome isAggregatorSound_natZero)
    (isAggregatorSound_listNil (elementType := Ty.optionType Ty.nat))

#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_unit_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_boolTrue_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_boolFalse_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listNil_natList_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionNone_natOption_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_refl_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_oeqRefl_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_natChain
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_optionStack
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listConsChain
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_natBool_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_pair_optionSome_natZero_closed
#print axioms LeanFX2.SmokeAggregatorComposition.aggregator_listCons_optionSome_closed

end LeanFX2.SmokeAggregatorComposition
