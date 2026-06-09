import FX1Poly.Core.RecursivePathOrder

/-! # FX1Poly/Core/RecursiveEliminatorTermination
    — #1139 spike: the RECURSIVE-eliminator ι-pattern terminates via the shipped multiset RPO certificate,
    INDEPENDENT of β and of typed-SN (the Leg-3 "β-imported boundary")

The three-ways SN capstone (SN-150) wants strong normalization proved three independent ways: Tait
(critical path, shipped), sconing (candidate bridge), and Makkai word-equality (Leg 3).  Leg 3's `fxSystem`
termination (SN-131) honestly CONSUMES typed-SN — because the `fxSystem` encodes β, and raw β is NOT terminating
(`Ω` is not SN, SN-NECESSITY #950), so the β-rule's termination genuinely imports Tait.  #1139 is about
separating the terminating ι/η fragment from that β boundary: η-SN is already shipped (η-M8h #357), and the ι
fragment must terminate on its OWN — NOT through Tait.

The ι fragment splits by difficulty: the NON-recursive eliminators (`boolElim`, `fst`/`snd`, `optionMatch`-none,
`eitherMatch`) strictly DECREASE term size (a simple well-founded measure).  The hard core is the RECURSIVE
eliminator —

    natElim (natSucc n) z s  ↝  app (app s n) (natElim n z s)

— which reintroduces a `natElim` on a SMALLER scrutinee and may DUPLICATE it.  Size can stay flat or grow, so a
size measure does NOT work; this is exactly what the **multiset (Dershowitz-Manna) RPO** is for.  This file
proves that recursive-duplication pattern terminates via the shipped RPO certificate
(`wellFounded_of_precedenceMultisetMeasure`), on a self-contained model, with NO β and NO typed-SN anywhere — the
genuine technical de-risking of #1139's ι-fragment Leg-3 independence.

## What this ships

  * `RecTerm` / `ElimStep` — a tiny self-contained model: a recursive eliminator `elim k` on a `Nat` scrutinee,
    whose rule `elim (k+1) ↝ branch (elim k) (elim k)` is the natElim-successor shape stripped to its
    termination essence (recursive call on the predecessor, duplicated), plus branch congruence.
  * `recScrutineeMultiset` — the termination measure: the multiset (`List Nat`) of all eliminator scrutinees.
  * `MultisetRedOne.appendRight` / `appendLeft` — the Dershowitz-Manna step is preserved under list-context
    append (the congruence lift); `appendLeft` folds the shipped single-element `underContext`.
  * **`elimStep_decreasesMultiset` (★)** — every `ElimStep` strictly decreases the scrutinee multiset by one
    Dershowitz-Manna step (`fire` replaces `[k+1]` with `[k, k]`, both `< k+1`).
  * **`recursiveEliminatorTerminates` (★)** — the recursive eliminator is strongly normalizing, via the shipped
    `wellFounded_of_precedenceMultisetMeasure` (trivial Unit precedence + the scrutinee multiset over `Nat.lt`).
    INDEPENDENT of β and typed-SN — the whole point of Leg 3.

## Honest scope

This is the de-risking MODEL, not the full FX ι-fragment.  It demonstrates that the genuinely-hard part of
#1139 — the recursive eliminator's duplicating recursive call — terminates via the shipped multiset RPO,
Tait-free.  Lifting this to the real `Step` ι-arms over `RawTerm` (the 194-generator measure, one
`measureDecreases` obligation per ι arm, joined with the easy size-decreasing non-recursive arms and the shipped
η-SN) is the multi-firing follow-on that closes #1139 proper.

## Zero-axiom verification

Structural `cases` on `List.Mem` (not `simp`, which pulls `propext` via `List.mem_cons`); `induction` for the
context-append lift; a propext-free local `listAppendAssoc` (`List.append_assoc` in this Lean core DEPENDS ON
`propext` — `List.cons_append` is clean); the shipped `MultisetRedOne` / `wellFounded_of_precedenceMultisetMeasure`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- A tiny term language capturing the recursive-eliminator essence: a recursive eliminator `elim k` on a `Nat`
scrutinee `k`, plus branch nodes (where the duplicated recursive results land). -/
inductive RecTerm where
  | leaf : RecTerm
  | branch : RecTerm → RecTerm → RecTerm
  | elim : Nat → RecTerm

/-- The recursive-eliminator reduction: `elim (k+1) ↝ branch (elim k) (elim k)` — fire the eliminator on a
successor scrutinee, DUPLICATING the recursive call on the predecessor `k` (the natElim/listElim shape, stripped
to its termination essence) — plus congruence into branches. -/
inductive ElimStep : RecTerm → RecTerm → Prop where
  | fire (scrutinee : Nat) :
      ElimStep (.elim (scrutinee + 1)) (.branch (.elim scrutinee) (.elim scrutinee))
  | branchLeft {leftSource leftTarget rightTerm : RecTerm} :
      ElimStep leftSource leftTarget → ElimStep (.branch leftSource rightTerm) (.branch leftTarget rightTerm)
  | branchRight {leftTerm rightSource rightTarget : RecTerm} :
      ElimStep rightSource rightTarget → ElimStep (.branch leftTerm rightSource) (.branch leftTerm rightTarget)

/-- The termination measure: the multiset (as a `List`) of all eliminator scrutinees in the term. -/
def recScrutineeMultiset : RecTerm → List Nat
  | .leaf => []
  | .branch leftTerm rightTerm => recScrutineeMultiset leftTerm ++ recScrutineeMultiset rightTerm
  | .elim scrutinee => [scrutinee]

/-- Propext-free list-append associativity (the `List.append_assoc` in this Lean core pulls `propext`; this
proof is plain `congrArg` induction, `List.cons_append` being definitional). -/
theorem listAppendAssoc {Elem : Type} (firstList secondList thirdList : List Elem) :
    (firstList ++ secondList) ++ thirdList = firstList ++ (secondList ++ thirdList) := by
  induction firstList with
  | nil => rfl
  | cons headElem _restList ih => exact congrArg (headElem :: ·) ih

/-- A single Dershowitz-Manna step is preserved under appending a context list on the RIGHT. -/
theorem MultisetRedOne.appendRight {Elem : Type} (baseRel : Elem → Elem → Prop)
    {smallList bigList : List Elem} (contextList : List Elem)
    (step : MultisetRedOne baseRel smallList bigList) :
    MultisetRedOne baseRel (smallList ++ contextList) (bigList ++ contextList) := by
  obtain ⟨removed, prefixList, suffixList, addedList, bigEq, smallEq, smaller⟩ := step
  refine ⟨removed, prefixList, suffixList ++ contextList, addedList, ?_, ?_, smaller⟩
  · rw [bigEq]; exact listAppendAssoc prefixList (removed :: suffixList) contextList
  · rw [smallEq]; exact listAppendAssoc (prefixList ++ addedList) suffixList contextList

/-- A single Dershowitz-Manna step is preserved under appending a context list on the LEFT — by induction on the
context, folding the shipped single-element `underContext`. -/
theorem MultisetRedOne.appendLeft {Elem : Type} (baseRel : Elem → Elem → Prop)
    {smallList bigList : List Elem} (contextList : List Elem)
    (step : MultisetRedOne baseRel smallList bigList) :
    MultisetRedOne baseRel (contextList ++ smallList) (contextList ++ bigList) := by
  induction contextList with
  | nil => exact step
  | cons headElem restList ih => exact MultisetRedOne.underContext baseRel headElem ih

/-- **★ Every recursive-eliminator step strictly decreases the scrutinee multiset by one Dershowitz-Manna step.**
The `fire` arm replaces `[k+1]` with `[k, k]` (both `< k+1`); the congruence arms lift the inner decrease through
the branch's left/right context.  This is the termination engine — independent of β and of typed-SN. -/
theorem elimStep_decreasesMultiset {source target : RecTerm} (step : ElimStep source target) :
    MultisetRedOne Nat.lt (recScrutineeMultiset target) (recScrutineeMultiset source) := by
  induction step with
  | fire scrutinee =>
      refine MultisetRedOne.replaceHead Nat.lt (scrutinee + 1) [scrutinee, scrutinee] [] ?_
      intro element membership
      cases membership with
      | head => exact Nat.lt_succ_self _
      | tail _ membershipTail =>
          cases membershipTail with
          | head => exact Nat.lt_succ_self _
          | tail _ membershipEmpty => nomatch membershipEmpty
  | branchLeft _innerStep ih =>
      exact MultisetRedOne.appendRight Nat.lt _ ih
  | branchRight _innerStep ih =>
      exact MultisetRedOne.appendLeft Nat.lt _ ih

/-- **★ The recursive-eliminator rewrite is strongly normalizing — INDEPENDENT of β and typed-SN.**  Via the
shipped RPO certificate `wellFounded_of_precedenceMultisetMeasure` with a trivial (Unit) precedence and the
scrutinee-multiset measure over `Nat.lt`.  The recursive eliminator's duplicating recursive call on a smaller
scrutinee is exactly the Dershowitz-Manna decrease — the hard core of the ι-fragment's Leg-3 independent
termination, proved here on the self-contained model. -/
theorem recursiveEliminatorTerminates :
    WellFounded (fun target source => ElimStep source target) :=
  wellFounded_of_precedenceMultisetMeasure
    (precedenceRank := fun _ => ())
    (argumentMeasure := recScrutineeMultiset)
    (precedenceRel := fun _ _ => False)
    (baseRel := Nat.lt)
    (WellFounded.intro fun unitValue => Acc.intro unitValue fun _ falseStep => falseStep.elim)
    Nat.lt_wfRel.wf
    (fun _source _target step => Or.inr ⟨rfl, elimStep_decreasesMultiset step⟩)

/-- Non-vacuity smoke: `elim 2` is accessible (terminating) — its reduction `elim 2 ↝ branch (elim 1)(elim 1) ↝
…` cannot go forever. -/
theorem recursiveEliminatorTerminates.smoke :
    Acc (fun target source => ElimStep source target) (.elim 2) :=
  recursiveEliminatorTerminates.apply (.elim 2)

end FX1Poly.Core
