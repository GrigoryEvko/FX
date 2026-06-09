import FX1Poly.Core.RawIotaEtaFullStepSN
import FX1Poly.Typed.UnboundedGrowthNotStronglyNormalizing

/-! # FX1Poly/Typed/RawIotaEtaOperationalSN
    — #1139 / #1140: the OPERATIONAL strong normalization of the ι∪η fragment, Tait-free

`RawIotaEtaFullStepSN` (firing-77) proved `iotaEtaFullStep_wellFounded : WellFounded
IotaEtaStep.successor` — the abstract well-foundedness of the full ι∪η reduction, by one recursive path
order over `eraseToRose`, independent of β and of typed-SN.  This file harvests its OPERATIONAL content:
the concrete "no infinite reduction" / "no cycle" statements that an SN endpoint of the parity matrix
(#1140) consumes.

Everything reuses the generic, relation-polymorphic `Acc` machinery shipped with the untyped-divergence
corpus (`accessibleElementHasNoInfiniteChain` / `accessibleElementNotSelfRelated`, both pure `Acc.rec`,
propext-free).  Because `IotaEtaStep.isStronglyNormalizing` supplies `Acc IotaEtaStep.successor t` for
EVERY raw term `t` — with NO typing hypothesis — these operational facts hold UNCONDITIONALLY on the
ι∪η fragment.  This is the sharp contrast with β: the untyped-divergence corpus exhibits Ω (a β self-loop)
and the tripler (β unbounded growth) as raw β terms that DO violate these very statements; the ι∪η fragment
admits no such pathology without any typing restriction.

## What this ships

  * `iotaEta_noInfiniteReduction` (★) — no infinite ι∪η reduction sequence `t₀ ⟶ t₁ ⟶ t₂ ⟶ …`.
  * `IotaEtaStep.irreflexive` — no self-loop (`¬ IotaEtaStep t t`), the 1-cycle case.
  * `alternatingSequence` / `alternatingSequence_steps` — the role-swapping `a, b, a, b, …` chain
    (structural recursion, no parity arithmetic).
  * `IotaEtaStep.no_two_cycle` — no 2-cycle `a ⟷ b`, witnessed by feeding the alternating chain to the
    no-infinite-reduction lemma (a genuine construction, not a bare instantiation).

## Zero-axiom verification

The two generic `Acc` lemmas are direct `Acc.rec`; `alternatingSequence_steps` is structural recursion on
the index (the `index+1` goal reduces definitionally to the argument-swapped instance).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated.
-/

namespace FX1Poly.Core
open FX1Poly.Typed

/-- **★ The operational SN of the ι∪η fragment: NO infinite ι∪η reduction sequence**, Tait-free.  Any
infinite chain `reductionSequence 0 ⟶ reductionSequence 1 ⟶ …` of `IotaEtaStep`s is impossible, because
`IotaEtaStep.successor` is well-founded (firing-77) so `reductionSequence 0` is accessible and admits no
infinite descending chain.  Holds for EVERY raw term, with no typing hypothesis. -/
theorem iotaEta_noInfiniteReduction {scope : Nat}
    (reductionSequence : Nat → RawTerm scope)
    (eachStepsToNext :
      ∀ index, IotaEtaStep (reductionSequence index) (reductionSequence (index + 1))) :
    False :=
  accessibleElementHasNoInfiniteChain (reductionSequence 0)
    (IotaEtaStep.isStronglyNormalizing (reductionSequence 0))
    reductionSequence rfl eachStepsToNext

/-- No self-loop: a term never ι∪η-steps to itself (irreflexivity, the 1-cycle case).  The sharp contrast
with β's Ω, which DOES self-step (`Step Ω Ω`) — but Ω is not in the ι∪η fragment. -/
theorem IotaEtaStep.irreflexive {scope : Nat} (term : RawTerm scope)
    (selfStep : IotaEtaStep term term) : False :=
  accessibleElementNotSelfRelated (IotaEtaStep.isStronglyNormalizing term) selfStep

/-- The alternating sequence `a, b, a, b, …` (role-swapping recursion — no parity arithmetic, hence no
`omega`/`decide`). -/
def alternatingSequence {scope : Nat} (firstTerm secondTerm : RawTerm scope) :
    Nat → RawTerm scope
  | 0 => firstTerm
  | index + 1 => alternatingSequence secondTerm firstTerm index

/-- Every term in the alternating sequence ι∪η-steps to the next, given the two-cycle witnesses.
Structural recursion on the index with SWAPPED arguments: the `index+1` goal reduces definitionally to the
swapped instance at `index` (`alternatingSequence a b (index+1) = alternatingSequence b a index`). -/
theorem alternatingSequence_steps {scope : Nat} (firstTerm secondTerm : RawTerm scope)
    (forwardStep : IotaEtaStep firstTerm secondTerm)
    (backwardStep : IotaEtaStep secondTerm firstTerm) :
    ∀ index, IotaEtaStep (alternatingSequence firstTerm secondTerm index)
      (alternatingSequence firstTerm secondTerm (index + 1))
  | 0 => forwardStep
  | index + 1 =>
    alternatingSequence_steps secondTerm firstTerm backwardStep forwardStep index

/-- No 2-cycle: there is no pair `a ⟷ b` of mutual ι∪η steps.  Witnessed by feeding the alternating
infinite chain `a, b, a, b, …` to `iotaEta_noInfiniteReduction` (a genuine chain construction, not a bare
instantiation).  Generalises `irreflexive` from the 1-cycle to the 2-cycle. -/
theorem IotaEtaStep.no_two_cycle {scope : Nat} (firstTerm secondTerm : RawTerm scope)
    (forwardStep : IotaEtaStep firstTerm secondTerm)
    (backwardStep : IotaEtaStep secondTerm firstTerm) : False :=
  iotaEta_noInfiniteReduction (alternatingSequence firstTerm secondTerm)
    (alternatingSequence_steps firstTerm secondTerm forwardStep backwardStep)

end FX1Poly.Core
