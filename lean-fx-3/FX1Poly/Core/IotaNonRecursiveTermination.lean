import FX1Poly.Core.StrongNormalizationEta

/-! # FX1Poly/Core/IotaNonRecursiveTermination
    — #1139 (Leg 3): the NON-RECURSIVE ι fragment of the REAL kernel terminates by `RawTerm.size`,
    INDEPENDENT of β and of typed-SN

The three-ways SN capstone (SN-150) wants strong normalization proved three independent ways: Tait
(critical path, shipped), sconing (candidate bridge), and Makkai word-equality (Leg 3).  Leg 3's
`fxSystem` termination (SN-131) honestly CONSUMES typed-SN — because the `fxSystem` encodes β, and raw β
is NOT terminating (`Ω` is not SN, SN-NECESSITY #950), so the β-rule's termination genuinely imports
Tait.  #1139 is about separating the terminating ι/η fragment from that β boundary: η-SN is already
shipped (η-M8h #357, `Step.etaStar.hasStrongNormalization`), and the ι fragment must terminate on its
OWN — NOT through Tait.

The ι fragment splits by difficulty.  The RECURSIVE eliminators (`natElim`/`natRec` on `natSucc`,
`listElim` on `listCons`) reintroduce the eliminator on a SMALLER scrutinee and may DUPLICATE it, so
`size` can stay flat or grow — they need the multiset (Dershowitz-Manna) RPO, de-risked on a
self-contained model in `RecursiveEliminatorTermination` (#1139 spike).  This file handles the OTHER
half: the **13 NON-recursive ι arms**, whose reduct is either a direct subterm of the redex
(branch-selection: bool/nat/list/option-none; projection: fst/snd; identity base: idJ/idStrictRec) or a
small `app(branch, value)` of two subterms (applied-branch: optionSome/eitherInl/eitherInr).  Every one
strictly DECREASES `RawTerm.size`, so the fragment is strongly normalizing by exactly the shipped η-SN
recipe (`Subrelation.wf` + `InvImage.wf RawTerm.size`), with NO β and NO typed-SN anywhere.

## What this ships

  * `IotaNonRecursiveStep` — a sibling inductive (mirroring `Step.eta`'s head-only shape) enumerating the
    13 non-recursive ι reductions over the ACTUAL `Step` redex/reduct cell shapes.
  * **`IotaNonRecursiveStep.toStep`** — soundness: every arm is a genuine `Step` of the real kernel.
    This ties the fragment to the live reduction relation — it is NOT a toy model like the recursive
    `RecTerm` spike; these are real `RawTerm` reductions.
  * **`IotaNonRecursiveStep.size_decreases` (★)** — every arm strictly decreases `RawTerm.size`
    (structural `size_lt_childCons` chains for the 10 subterm-reduct arms; a propext-free explicit-`rw`
    AC-normalization for the 3 applied-branch arms).
  * **`iotaNonRecursiveStep_wellFounded` (★)** — the fragment is strongly normalizing, via
    `Subrelation.wf` + `InvImage.wf RawTerm.size`, the EXACT shape of the shipped η-SN
    `Step.etaStar.etaSuccessor_wellFounded`.  INDEPENDENT of β and typed-SN.

## Honest scope

This is the genuinely-terminating half of the ι fragment over the REAL kernel.  Combined with the
shipped η-SN (`Step.etaStar`) and the recursive-eliminator RPO model
(`RecursiveEliminatorTermination`), it covers the full Leg-3 ι/η termination story — the recursive ι
arms over real `RawTerm` (a real multiset measure on the actual cells) being the remaining lift.  The β
boundary stays honestly Tait-imported (the whole point of Leg 3).

## Zero-axiom verification

Structural `size_lt_childCons_head/tail` chains with the binder-shift pinned to `0`; defeq-collapse of
the reduct/redex `RawTerm.size` to a Nat normal form; explicit `Nat.add_right_comm`/`Nat.add_comm`
rewrites for the applied-branch AC equality (`simp`-AC and `ac_rfl` both LEAK `propext`; explicit
`add_assoc`/`add_right_comm` are clean — banked finding).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- The non-recursive ι head reductions: the 13 ι arms of `Step` whose reduct is structurally
smaller than the redex.  Excludes the 3 recursive eliminators (natElimSucc / natRecSucc /
listElimCons), whose reduct re-introduces the eliminator on a smaller scrutinee (the multiset-RPO
territory of `RecursiveEliminatorTermination`). -/
inductive IotaNonRecursiveStep : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  | iotaBoolTrue {scope : Nat} {motive : RawTerm (scope + 1)}
      {thenBranch elseBranch : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_boolElim () (.childCons motive
          (.childCons thenBranch (.childCons elseBranch
            (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil))))) thenBranch
  | iotaBoolFalse {scope : Nat} {motive : RawTerm (scope + 1)}
      {thenBranch elseBranch : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_boolElim () (.childCons motive
          (.childCons thenBranch (.childCons elseBranch
            (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil))))) elseBranch
  | iotaFstPair {scope : Nat} {firstValue secondValue : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_fst () (.childCons (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil))) .childNil)) firstValue
  | iotaSndPair {scope : Nat} {firstValue secondValue : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_snd () (.childCons (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil))) .childNil)) secondValue
  | iotaNatElimZero {scope : Nat} {motive : RawTerm (scope + 1)}
      {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
      IotaNonRecursiveStep
        (.mkGen .gen_natElim () (.childCons motive
          (.childCons zeroBranch (.childCons succBranch
            (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))) zeroBranch
  | iotaNatRecZero {scope : Nat} {motive : RawTerm (scope + 1)}
      {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
      IotaNonRecursiveStep
        (.mkGen .gen_natRec () (.childCons motive
          (.childCons zeroBranch (.childCons succBranch
            (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))) zeroBranch
  | iotaListElimNil {scope : Nat} {motive : RawTerm (scope + 1)}
      {nilBranch consBranch : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_listElim () (.childCons motive
          (.childCons nilBranch (.childCons consBranch
            (.childCons (.mkGen .gen_listNil () .childNil) .childNil))))) nilBranch
  | iotaOptionMatchNone {scope : Nat} {motive : RawTerm (scope + 1)}
      {noneBranch someBranch : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_optionMatch () (.childCons motive
          (.childCons noneBranch (.childCons someBranch
            (.childCons (.mkGen .gen_optionNone () .childNil) .childNil))))) noneBranch
  | iotaOptionMatchSome {scope : Nat} {motive : RawTerm (scope + 1)}
      {value noneBranch someBranch : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_optionMatch () (.childCons motive
          (.childCons noneBranch (.childCons someBranch
            (.childCons (.mkGen .gen_optionSome () (.childCons value .childNil))
              .childNil)))))
        (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil)))
  | iotaEitherMatchInl {scope : Nat} {motive : RawTerm (scope + 1)}
      {value leftBranch rightBranch : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_eitherMatch () (.childCons motive
          (.childCons leftBranch (.childCons rightBranch
            (.childCons (.mkGen .gen_eitherInl () (.childCons value .childNil))
              .childNil)))))
        (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil)))
  | iotaEitherMatchInr {scope : Nat} {motive : RawTerm (scope + 1)}
      {value leftBranch rightBranch : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_eitherMatch () (.childCons motive
          (.childCons leftBranch (.childCons rightBranch
            (.childCons (.mkGen .gen_eitherInr () (.childCons value .childNil))
              .childNil)))))
        (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil)))
  | iotaIdJRefl {scope : Nat} {baseCase rawWitness : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_idJ () (.childCons baseCase
          (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))) baseCase
  | iotaIdStrictRecRefl {scope : Nat} {baseCase rawWitness : RawTerm scope} :
      IotaNonRecursiveStep
        (.mkGen .gen_idStrictRec () (.childCons baseCase
          (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))) baseCase

/-- Soundness: every non-recursive ι step is a genuine `Step` of the real kernel — this fragment is a
sub-relation of the live reduction relation, not a toy model. -/
theorem IotaNonRecursiveStep.toStep {scope : Nat} {source target : RawTerm scope}
    (step : IotaNonRecursiveStep source target) : Step source target := by
  cases step with
  | iotaBoolTrue => exact Step.iotaBoolTrue
  | iotaBoolFalse => exact Step.iotaBoolFalse
  | iotaFstPair => exact Step.iotaFstPair
  | iotaSndPair => exact Step.iotaSndPair
  | iotaNatElimZero => exact Step.iotaNatElimZero
  | iotaNatRecZero => exact Step.iotaNatRecZero
  | iotaListElimNil => exact Step.iotaListElimNil
  | iotaOptionMatchNone => exact Step.iotaOptionMatchNone
  | iotaOptionMatchSome => exact Step.iotaOptionMatchSome
  | iotaEitherMatchInl => exact Step.iotaEitherMatchInl
  | iotaEitherMatchInr => exact Step.iotaEitherMatchInr
  | iotaIdJRefl => exact Step.iotaIdJRefl
  | iotaIdStrictRecRefl => exact Step.iotaIdStrictRecRefl

/-- Shape C: fst projection — reduct is the first pair component (defeq-front, then trailing pad). -/
private theorem iotaSizeShapeFstProjection (firstSize secondSize : Nat) :
    firstSize < firstSize + (secondSize + 0 + 1) + 1 + 1 + 0 + 1 + 1 :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right firstSize (secondSize + 0 + 1)))
    (Nat.le_add_right (firstSize + (secondSize + 0 + 1) + 1) (1 + 0 + 1 + 1))

/-- Shape D: snd projection — reduct is the second pair component (front padding before the reduct). -/
private theorem iotaSizeShapeSndProjection (secondSize firstSize : Nat) :
    secondSize < firstSize + (secondSize + 0 + 1) + 1 + 1 + 0 + 1 + 1 :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right secondSize 0))
    (Nat.le_trans (Nat.le_add_left (secondSize + 0 + 1) firstSize)
      (Nat.le_add_right (firstSize + (secondSize + 0 + 1)) (1 + 1 + 0 + 1 + 1)))

/-- Applied-branch size helper: applied branch is the SECOND (tail) branch (optionMatchSome /
eitherMatchInr).  The reduct `app(branch, value)` size collapses by defeq to `(branchSize + valueSize) +
3`; the redex side AC-normalizes (explicit `Nat.add_right_comm`/`add_comm`, propext-free — `simp`-AC and
`ac_rfl` both leak `propext`) to `(branchSize + valueSize) + (otherSize + 6)`, then `Nat.add_lt_add_left`
on the shared `branchSize + valueSize` prefix. -/
private theorem iotaSizeShapeAppliedSecond (branchSize valueSize otherSize : Nat) :
    branchSize + (valueSize + 0 + 1) + 1 + 1 <
      valueSize + 0 + 1 + 1 + (otherSize + (branchSize + 0 + 1) + 1) + 1 + 1 := by
  have redexEq :
      valueSize + 0 + 1 + 1 + (otherSize + (branchSize + 0 + 1) + 1) + 1 + 1
        = branchSize + valueSize + (otherSize + 6) := by
    show valueSize + 2 + (otherSize + branchSize) + 4 = branchSize + valueSize + (otherSize + 6)
    rw [← Nat.add_assoc (valueSize + 2) otherSize branchSize,
        ← Nat.add_assoc (branchSize + valueSize) otherSize 6,
        Nat.add_comm branchSize valueSize,
        Nat.add_right_comm valueSize branchSize otherSize,
        Nat.add_right_comm (valueSize + 2) otherSize branchSize,
        Nat.add_right_comm (valueSize + 2) branchSize otherSize,
        Nat.add_right_comm valueSize 2 otherSize,
        Nat.add_right_comm (valueSize + otherSize) 2 branchSize]
  rw [redexEq]
  exact Nat.add_lt_add_left
    (Nat.lt_of_lt_of_le (show (3 : Nat) < 6 by decide) (Nat.le_add_left 6 otherSize))
    (branchSize + valueSize)

/-- Applied-branch size helper: applied branch is the FIRST branch (eitherMatchInl).  Twin of
`iotaSizeShapeAppliedSecond` with the dropped branch and the carried value swapped in the redex spine. -/
private theorem iotaSizeShapeAppliedFirst (branchSize valueSize otherSize : Nat) :
    branchSize + (valueSize + 0 + 1) + 1 + 1 <
      valueSize + 0 + 1 + 1 + (branchSize + (otherSize + 0 + 1) + 1) + 1 + 1 := by
  have redexEq :
      valueSize + 0 + 1 + 1 + (branchSize + (otherSize + 0 + 1) + 1) + 1 + 1
        = branchSize + valueSize + (otherSize + 6) := by
    show valueSize + 2 + (branchSize + otherSize) + 4 = branchSize + valueSize + (otherSize + 6)
    rw [← Nat.add_assoc (valueSize + 2) branchSize otherSize,
        ← Nat.add_assoc (branchSize + valueSize) otherSize 6,
        Nat.add_comm branchSize valueSize,
        Nat.add_right_comm valueSize branchSize otherSize,
        Nat.add_right_comm (valueSize + 2) branchSize otherSize,
        Nat.add_right_comm valueSize 2 otherSize,
        Nat.add_right_comm (valueSize + otherSize) 2 branchSize]
  rw [redexEq]
  exact Nat.add_lt_add_left
    (Nat.lt_of_lt_of_le (show (3 : Nat) < 6 by decide) (Nat.le_add_left 6 otherSize))
    (branchSize + valueSize)

/-- The reduct `app(branch, value)` size collapses by defeq to
`branchSize + valueSize + 3`.  Shared by both Phase-Z applied-branch helpers. -/
private theorem appliedReductSizeEq (branchSize valueSize : Nat) :
    branchSize + (valueSize + 0 + 1) + 1 + 1 = branchSize + valueSize + 3 := by
  show branchSize + (valueSize + 1) + 1 + 1 = branchSize + valueSize + 3
  rw [← Nat.add_assoc branchSize valueSize 1,
      Nat.add_assoc (branchSize + valueSize) 1 1,
      Nat.add_assoc (branchSize + valueSize) 2 1]

/-- The innermost two-branch span `branch + (value + 0 + 1 + 1 + 0 + 1) + 1`
collapses by defeq to `branchSize + valueSize + 4` — the scrutinee `optionSome`/
`eitherIn_` wraps the value with two extra levels.  Both applied-branch redexes
contain this span. -/
private theorem appliedSpanSizeEq (branchSize valueSize : Nat) :
    branchSize + (valueSize + 0 + 1 + 1 + 0 + 1) + 1 = branchSize + valueSize + 4 := by
  show branchSize + (valueSize + 3) + 1 = branchSize + valueSize + 4
  rw [← Nat.add_assoc branchSize valueSize 3,
      Nat.add_assoc (branchSize + valueSize) 3 1]

/-- Phase-Z applied-branch size helper, applied branch SECOND
(optionMatchSome / eitherMatchInr).  The Phase-Z 4-child redex spine
`[motive, otherBranch, appliedBranch, scrutinee]` carries the extra `motiveSize`
on the outside and the scrutinee LAST.  The reduct collapses to
`branchSize + valueSize + 3`, the redex strictly dominates by the
`branchSize + valueSize + 4` applied span plus the surrounding padding —
proved by monotone `Nat.le_add_*` bounds (no AC normalization). -/
private theorem iotaSizeShapeAppliedSecondWithMotive
    (branchSize valueSize otherSize motiveSize : Nat) :
    branchSize + (valueSize + 0 + 1) + 1 + 1 <
      motiveSize +
        (otherSize + (branchSize + (valueSize + 0 + 1 + 1 + 0 + 1) + 1) + 1) + 1 + 1 := by
  rw [appliedReductSizeEq, appliedSpanSizeEq]
  -- Goal: branchSize + valueSize + 3 < motiveSize + (otherSize + (branchSize + valueSize + 4) + 1) + 1 + 1
  refine Nat.lt_of_lt_of_le
    (Nat.lt_succ_of_le (Nat.le_refl (branchSize + valueSize + 3))) ?_
  -- branchSize + valueSize + 4 ≤ redex
  refine Nat.le_trans (Nat.le_add_left (branchSize + valueSize + 4) otherSize) ?_
  refine Nat.le_trans (Nat.le_add_right (otherSize + (branchSize + valueSize + 4)) 1) ?_
  refine Nat.le_trans (Nat.le_add_left
    (otherSize + (branchSize + valueSize + 4) + 1) motiveSize) ?_
  refine Nat.le_trans (Nat.le_add_right
    (motiveSize + (otherSize + (branchSize + valueSize + 4) + 1)) 1) ?_
  exact Nat.le_add_right
    (motiveSize + (otherSize + (branchSize + valueSize + 4) + 1) + 1) 1

/-- Phase-Z applied-branch size helper, applied branch FIRST (eitherMatchInl).
Twin of `iotaSizeShapeAppliedSecondWithMotive` with the dropped branch and the
carried branch swapped in the Phase-Z 4-child redex spine. -/
private theorem iotaSizeShapeAppliedFirstWithMotive
    (branchSize valueSize otherSize motiveSize : Nat) :
    branchSize + (valueSize + 0 + 1) + 1 + 1 <
      motiveSize +
        (branchSize + (otherSize + (valueSize + 0 + 1 + 1 + 0 + 1) + 1) + 1) + 1 + 1 := by
  rw [appliedReductSizeEq, appliedSpanSizeEq]
  -- Goal: branchSize + valueSize + 3 < motiveSize + (branchSize + (otherSize + valueSize + 4) + 1) + 1 + 1
  have payloadBound : valueSize + 3 < otherSize + valueSize + 4 :=
    Nat.lt_succ_of_le (Nat.add_le_add_right (Nat.le_add_left valueSize otherSize) 3)
  have reductBelowSpan :
      branchSize + valueSize + 3 < branchSize + (otherSize + valueSize + 4) :=
    Nat.add_lt_add_left payloadBound branchSize
  exact Nat.lt_of_lt_of_le reductBelowSpan
    (Nat.le_trans (Nat.le_succ (branchSize + (otherSize + valueSize + 4)))
      (Nat.le_trans
        (Nat.le_add_left (branchSize + (otherSize + valueSize + 4) + 1) motiveSize)
        (Nat.le_add_right
          (motiveSize + (branchSize + (otherSize + valueSize + 4) + 1)) 2)))

/-- **★ Every non-recursive ι step strictly decreases `RawTerm.size`.**  The 10 subterm-reduct arms
(branch-selection bool/nat/list/option-none, fst/snd projection, idJ/idStrictRec base) close by the
structural `size_lt_childCons` chains; the 3 applied-branch arms (optionSome/eitherInl/eitherInr) close
by the AC-normalized helpers.  This is the termination engine — independent of β and of typed-SN. -/
theorem IotaNonRecursiveStep.size_decreases {scope : Nat} {source target : RawTerm scope}
    (step : IotaNonRecursiveStep source target) : target.size < source.size := by
  cases step with
  | iotaBoolTrue =>
      -- Phase-Z 4-child spine `[motive, thenBranch, elseBranch, boolTrue]`:
      -- thenBranch is at position 1, so skip ONE head (the motive, at shift 1)
      -- after projecting thenBranch as the head of the tail spine.
      dsimp only [RawTerm.size]
      exact Nat.lt_trans (Nat.lt_trans
        (RawTermChildren.size_lt_childCons_head (shift := 0) _ _)
        (RawTermChildren.size_lt_childCons_tail (shift := 1) _ _)) (Nat.lt_succ_self _)
  | iotaBoolFalse =>
      -- Phase-Z 4-child spine: elseBranch is at position 2, so skip the motive
      -- (shift 1) then the thenBranch (shift 0) after projecting elseBranch.
      dsimp only [RawTerm.size]
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
        (RawTermChildren.size_lt_childCons_head (shift := 0) _ _)
        (RawTermChildren.size_lt_childCons_tail (shift := 0) _ _))
        (RawTermChildren.size_lt_childCons_tail (shift := 1) _ _)) (Nat.lt_succ_self _)
  | iotaFstPair =>
      dsimp only [RawTerm.size, RawTermChildren.size]; exact iotaSizeShapeFstProjection _ _
  | iotaSndPair =>
      dsimp only [RawTerm.size, RawTermChildren.size]; exact iotaSizeShapeSndProjection _ _
  | iotaNatElimZero =>
      -- Phase-Z 4-child spine `[motive, zeroBranch, succBranch, natZero]`:
      -- zeroBranch is at position 1, so skip ONE head (the motive, at shift 1)
      -- after projecting zeroBranch as the head of the tail spine — mirrors the
      -- `iotaListElimNil` arm exactly (the nilBranch also sits at position 1).
      dsimp only [RawTerm.size]
      exact Nat.lt_trans (Nat.lt_trans
        (RawTermChildren.size_lt_childCons_head (shift := 0) _ _)
        (RawTermChildren.size_lt_childCons_tail (shift := 1) _ _)) (Nat.lt_succ_self _)
  | iotaNatRecZero =>
      -- Phase-Z 4-child spine `[motive, zeroBranch, succBranch, natZero]`: same as
      -- `iotaNatElimZero` (zeroBranch at position 1, motive head at shift 1).
      dsimp only [RawTerm.size]
      exact Nat.lt_trans (Nat.lt_trans
        (RawTermChildren.size_lt_childCons_head (shift := 0) _ _)
        (RawTermChildren.size_lt_childCons_tail (shift := 1) _ _)) (Nat.lt_succ_self _)
  | iotaListElimNil =>
      -- Phase-Z 4-child spine `[motive, nilBranch, consBranch, listNil]`:
      -- nilBranch is at position 1, so skip ONE head (the motive, at shift 1)
      -- after projecting nilBranch as the head of the tail spine.
      dsimp only [RawTerm.size]
      exact Nat.lt_trans (Nat.lt_trans
        (RawTermChildren.size_lt_childCons_head (shift := 0) _ _)
        (RawTermChildren.size_lt_childCons_tail (shift := 1) _ _)) (Nat.lt_succ_self _)
  | iotaOptionMatchNone =>
      -- Phase-Z 4-child spine `[motive, noneBranch, someBranch, optionNone]`:
      -- noneBranch is at position 1, so skip ONE head (the motive, at shift 1)
      -- after projecting noneBranch as the head of the tail spine — mirrors the
      -- `iotaListElimNil` arm exactly.
      dsimp only [RawTerm.size]
      exact Nat.lt_trans (Nat.lt_trans
        (RawTermChildren.size_lt_childCons_head (shift := 0) _ _)
        (RawTermChildren.size_lt_childCons_tail (shift := 1) _ _)) (Nat.lt_succ_self _)
  | iotaOptionMatchSome =>
      dsimp only [RawTerm.size, RawTermChildren.size]
      exact iotaSizeShapeAppliedSecondWithMotive _ _ _ _
  | iotaEitherMatchInl =>
      dsimp only [RawTerm.size, RawTermChildren.size]
      exact iotaSizeShapeAppliedFirstWithMotive _ _ _ _
  | iotaEitherMatchInr =>
      dsimp only [RawTerm.size, RawTermChildren.size]
      exact iotaSizeShapeAppliedSecondWithMotive _ _ _ _
  | iotaIdJRefl =>
      dsimp only [RawTerm.size]
      exact Nat.lt_trans
        (RawTermChildren.size_lt_childCons_head (shift := 0) _ _) (Nat.lt_succ_self _)
  | iotaIdStrictRecRefl =>
      dsimp only [RawTerm.size]
      exact Nat.lt_trans
        (RawTermChildren.size_lt_childCons_head (shift := 0) _ _) (Nat.lt_succ_self _)

/-- Accessibility successor: `laterTerm` is below `earlierTerm` when `earlierTerm` contracts by one
non-recursive ι step (mirrors `Step.etaSuccessor`). -/
def IotaNonRecursiveStep.successor {scope : Nat} (laterTerm earlierTerm : RawTerm scope) : Prop :=
  IotaNonRecursiveStep earlierTerm laterTerm

/-- **★ The non-recursive ι fragment of the real kernel is strongly normalizing — INDEPENDENT of β and
of typed-SN.**  Via `Subrelation.wf` + `InvImage.wf RawTerm.size` (every step strictly decreases size),
the EXACT shape of the shipped η-SN `Step.etaStar.etaSuccessor_wellFounded`.  Leg 3's terminating ι half
over the real kernel, Tait-free. -/
theorem iotaNonRecursiveStep_wellFounded {scope : Nat} :
    WellFounded (IotaNonRecursiveStep.successor (scope := scope)) :=
  Subrelation.wf
    (r := InvImage (fun leftSize rightSize : Nat => leftSize < rightSize) RawTerm.size)
    (fun step => IotaNonRecursiveStep.size_decreases step)
    (InvImage.wf RawTerm.size
      (Nat.lt_wfRel.wf : WellFounded (fun leftSize rightSize : Nat => leftSize < rightSize)))

/-- Every raw term is non-recursive-ι strongly normalizing (accessible). -/
theorem IotaNonRecursiveStep.isStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Acc IotaNonRecursiveStep.successor sourceTerm :=
  iotaNonRecursiveStep_wellFounded.apply sourceTerm

/-- Non-vacuity smoke: a concrete `boolElim motive unit unit boolTrue` (which `iotaBoolTrue`-reduces to
its then-branch) is accessible — its non-recursive ι reductions cannot go forever.  Phase-Z motive shape:
the motive is `var 0 : RawTerm 1` (under one binder), the scrutinee `boolTrue` is the last child. -/
theorem IotaNonRecursiveStep.isStronglyNormalizing.smoke :
    Acc (IotaNonRecursiveStep.successor (scope := 0))
      (.mkGen .gen_boolElim ()
        (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
          (.childCons (.mkGen .gen_unit () .childNil)
            (.childCons (.mkGen .gen_unit () .childNil)
              (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil))))) :=
  IotaNonRecursiveStep.isStronglyNormalizing _

end FX1Poly.Core
