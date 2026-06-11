import FX1Poly.Core.OneStepReductsComplete
import FX1Poly.Core.NormalizeCost

/-! # FX1Poly/Core/CostBound
    — the kernel WORST-CASE cost bound: sound for EVERY strategy (COST-3 brick 4)

The COST-1 worst-case recipe at the 198-generator kernel, folding over
the brick-2/3 characterized enumeration (`step_iff_mem_oneStepReducts`):

  * `RawTerm.costBoundOverReducts` — the soundness-threaded cost fold
    over a reduct list: one unit plus the recursive bound per listed
    reduct, summed.  Threading the soundness through the recursion keeps
    every recursive call justified by a genuine `Step` witness (no
    `List.attach`).
  * `costBoundOverReducts_boundsElement` — each listed reduct's
    contribution is bounded by the fold (the propext-free SUM-bound
    discipline: `Nat.le_add_right`/`Nat.le_add_left`; `Nat.le_max_*`
    would leak `propext` — the sum dominates the max, soundness at the
    price of slack).
  * ★ `RawTerm.costBound` — **the computable worst-case cost**: by
    `Acc.rec` on strong normalization (constant `Nat` motive), the
    soundness-threaded sum over all one-step reducts.
  * ★ `RawTerm.costBound_isSound` — EVERY counted reduction chain
    (`StepStarN`) from a strongly-normalizing kernel term — under ANY
    strategy — has length at most `costBound`.  The head step's
    membership comes from brick-3 COMPLETENESS; the fold contribution
    from `boundsElement`; the recursive bounds line up by Acc proof
    irrelevance.
  * `RawTerm.normalizeCost_le_costBound` — the sandwich: the canonical
    strategy's exact cost (brick 1) never exceeds the worst-case bound.
  * Non-vacuity: `costBound unit = 0` by kernel evaluation through the
    concrete `Acc.intro` witness; the identity-β fixture's bound is
    POSITIVE (soundness applied to its concrete 1-step chain, with the
    fixture's accessibility hand-built from brick-3 completeness +
    brick-2's computed enumeration).

The typed packaging (`HasTypeDescPi` ⟹ calculable worst-case cost via
the shipped typed-SN theorems) is the next brick.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open Foundation

/-! ## The soundness-threaded cost fold -/

/-- The soundness-threaded cost fold: for each listed reduct (with its
`Step` witness threaded), one unit plus its recursive cost, all summed.
Threading the soundness through the recursion avoids `List.attach` and
keeps every recursive call justified by a genuine `Step` witness. -/
def RawTerm.costBoundOverReducts {scope : Nat} (source : RawTerm scope)
    (recurse : (reduct : RawTerm scope) → Step source reduct → Nat) :
    (reducts : List (RawTerm scope)) →
      ((listed : RawTerm scope) → listed ∈ reducts → Step source listed) → Nat
  | [], _ => 0
  | reduct :: rest, soundAll =>
      (1 + recurse reduct (soundAll reduct (List.Mem.head rest)))
        + RawTerm.costBoundOverReducts source recurse rest
            (fun listed mem => soundAll listed (List.Mem.tail reduct mem))

/-- Each listed reduct's contribution is bounded by the fold — the
propext-free SUM-bound discipline (`Nat.le_add_right`/`Nat.le_add_left`;
`Nat.le_max_*` would leak `propext`). -/
theorem RawTerm.costBoundOverReducts_boundsElement {scope : Nat} (source : RawTerm scope)
    (recurse : (reduct : RawTerm scope) → Step source reduct → Nat) :
    {reducts : List (RawTerm scope)} →
    (soundAll : (listed : RawTerm scope) → listed ∈ reducts → Step source listed) →
    {middle : RawTerm scope} → (mem : middle ∈ reducts) →
      1 + recurse middle (soundAll middle mem)
        ≤ RawTerm.costBoundOverReducts source recurse reducts soundAll := by
  intro reducts
  induction reducts with
  | nil => intro _ _ mem; cases mem
  | cons reduct rest ih =>
      intro soundAll middle mem
      cases mem with
      | head => exact Nat.le_add_right _ _
      | tail _ memRest =>
          have tailBound :=
            ih (fun listed innerMem => soundAll listed (List.Mem.tail reduct innerMem)) memRest
          exact Nat.le_trans tailBound (Nat.le_add_left _ _)

/-! ## ★ The computable worst-case cost bound -/

/-- ★ **The computable worst-case kernel cost bound**: by `Acc.rec` on
strong normalization (constant `Nat` motive — the propext-free recipe),
the soundness-threaded sum over all one-step reducts of the brick-2
enumeration.  Sound for EVERY reduction strategy
(`costBound_isSound`). -/
def RawTerm.costBound {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) : Nat :=
  Acc.rec (motive := fun _candidate _acc => Nat)
    (fun candidate _accStep boundRec =>
      RawTerm.costBoundOverReducts candidate
        (fun reduct step => boundRec reduct step)
        (RawTerm.oneStepReducts candidate)
        (fun _listed mem => RawTerm.oneStepReducts_sound candidate mem))
    accessible

/-- ★ **Worst-case soundness (the kernel complexity-calculation
theorem)**: EVERY counted reduction chain from a strongly-normalizing
kernel term — under ANY strategy — has length at most `costBound`.
Induction over the accessibility; each head step's tail bound lifts
through the sum via `costBoundOverReducts_boundsElement` at the brick-3
completeness membership (recursive bounds line up by Acc proof
irrelevance). -/
theorem RawTerm.costBound_isSound {scope : Nat} {term : RawTerm scope}
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    ∀ {steps : Nat} {target : RawTerm scope},
      StepStarN steps term target → steps ≤ RawTerm.costBound term accessible := by
  induction accessible with
  | intro candidate accStep ih =>
      intro steps target chain
      cases chain with
      | reflN _ => exact Nat.zero_le _
      | transN firstStep rest =>
          have restBound := ih _ firstStep rest
          have elementBound :=
            RawTerm.costBoundOverReducts_boundsElement candidate
              (fun reduct step => RawTerm.costBound reduct (accStep reduct step))
              (fun _listed mem => RawTerm.oneStepReducts_sound candidate mem)
              (RawTerm.oneStepReducts_complete firstStep)
          have liftedBound := Nat.succ_le_succ restBound
          rw [Nat.add_comm 1 _] at elementBound
          exact Nat.le_trans liftedBound elementBound

/-- **The sandwich**: the canonical strategy's exact cost (brick 1's
`normalizeCost`) never exceeds the worst-case bound. -/
theorem RawTerm.normalizeCost_le_costBound {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    RawTerm.normalizeCost term accessible ≤ RawTerm.costBound term accessible :=
  RawTerm.costBound_isSound accessible (RawTerm.normalizeCost_isExact term accessible)

/-! ## Non-vacuity — the bound computes and is attained -/

/-- **The bound computes**: the normal form `unit` has worst-case cost
exactly zero — the fold evaluates over the empty enumeration through the
concrete `Acc.intro` witness by kernel computation. -/
theorem RawTerm.costBound_unit_isZero :
    RawTerm.costBound unitNormalFormFixture unitNormalFormFixture_accessible = 0 := rfl

/-- The identity-β fixture steps to `unit` (read off the brick-2
computed enumeration via soundness). -/
theorem identityBetaFixture_stepsToUnit :
    Step identityBetaFixture unitNormalFormFixture :=
  RawTerm.oneStepReducts_sound identityBetaFixture (List.Mem.head [])

/-- Accessibility of the identity-β fixture, hand-built from brick-3
COMPLETENESS over the brick-2 computed enumeration: every one-step
reduct is a member of `[unit]`, and `unit` is accessible. -/
def identityBetaFixture_accessible :
    Acc (@StepStar.StepSuccessor 0) identityBetaFixture :=
  Acc.intro identityBetaFixture
    (fun later laterStep => by
      have memListed : later ∈ RawTerm.oneStepReducts identityBetaFixture :=
        RawTerm.oneStepReducts_complete laterStep
      rw [identityBetaFixture_oneStepReducts] at memListed
      cases memListed with
      | head => exact unitNormalFormFixture_accessible
      | tail _ memEmpty => exact nomatch memEmpty)

/-- **The bound is honest on a genuine redex**: the identity-β fixture's
worst-case bound is positive — soundness applied to its concrete 1-step
chain. -/
theorem identityBetaFixture_costBound_isPositive :
    1 ≤ RawTerm.costBound identityBetaFixture identityBetaFixture_accessible :=
  RawTerm.costBound_isSound identityBetaFixture_accessible
    (StepStarN.transN identityBetaFixture_stepsToUnit
      (StepStarN.reflN unitNormalFormFixture))

end FX1Poly.Core
