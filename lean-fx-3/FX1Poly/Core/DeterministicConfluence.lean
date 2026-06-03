import FX1Poly.Core.Newman
import FX1Poly.Core.WeakHeadStepDeterministic

/-! # FX1Poly/Core/DeterministicConfluence
    — a deterministic relation is confluent, with weak-head reduction as the concrete payoff

The fourth and simplest abstract confluence route, after `Newman.lean` (terminating + weakly confluent),
`DiamondConfluence.lean` (the diamond), and `CommutationConfluence.lean` (commuting union).  A DETERMINISTIC
(functional) relation — each source has at most one reduct — is automatically confluent: its reflexive-
transitive reducts from a common source are linearly ordered, so one reduction is a prefix of the other.

Note determinism does NOT give the strict `DiamondProperty` (`DiamondConfluence`): the diamond demands a
common SINGLE-STEP reduct of two divergent steps, which a normal form breaks (no further step exists).
Determinism is the stronger property and yields confluence by its own linear-chain induction, not through the
diamond.  This is the route for deterministic reduction STRATEGIES — weak-head reduction here, and the
deterministic NbE evaluator (M12) downstream — where confluence of the strategy's reduction sequences is the
fact one wants.

## What is proved

* `IsDeterministic` — each source has at most one reduct (the relation is a partial function).
* `confluentOfDeterministicAux` / `confluentOfDeterministic` — **a deterministic relation is confluent**
  (induct on the left chain; in the head/head case, determinism equates the two first reducts, then the
  induction hypothesis joins the remainders; right chain kept quantified for the induction).
* `WeakHeadStep.hasConfluence` — **weak-head reduction is confluent** (the concrete payoff): `WeakHeadStep`
  is deterministic (`WeakHeadStep.deterministic`), hence Church-Rosser over its reflexive-transitive closure.

## Zero-axiom verification

The core is a structural induction over `ReflTransClosure` with `cases` on the right chain and a `subst` on
the determinism equation; the instantiation is a direct application of the shipped `WeakHeadStep.deterministic`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Carrier : Type carrierUniverse}

/-- A relation is **deterministic** (functional) when each source has at most one reduct. -/
def IsDeterministic (rel : Carrier → Carrier → Prop) : Prop :=
  ∀ {source firstReduct secondReduct : Carrier},
    rel source firstReduct → rel source secondReduct → firstReduct = secondReduct

/-- Confluence core for a deterministic relation: the reflexive-transitive reducts from a common source are
linearly ordered, so one chain is a prefix of the other.  Induct on the left chain with the right chain kept
quantified; in the head/head case determinism equates the two first reducts and the induction hypothesis joins
the remainders. -/
theorem confluentOfDeterministicAux {rel : Carrier → Carrier → Prop} (det : IsDeterministic rel)
    {source leftReduct : Carrier} (leftChain : ReflTransClosure rel source leftReduct) :
    ∀ {rightReduct : Carrier}, ReflTransClosure rel source rightReduct →
      Joinable rel leftReduct rightReduct := by
  induction leftChain with
  | refl point =>
      intro rightReduct rightChain
      exact ⟨rightReduct, rightChain, ReflTransClosure.refl rightReduct⟩
  | head firstStep restChain ihRest =>
      intro rightReduct rightChain
      cases rightChain with
      | refl =>
          exact ⟨_, ReflTransClosure.refl _, ReflTransClosure.head firstStep restChain⟩
      | head rightFirst rightRest =>
          have middleEq := det firstStep rightFirst
          subst middleEq
          exact ihRest rightRest

/-- **A deterministic relation is confluent.**  The simplest confluence route: no termination, no diamond
(determinism is strictly stronger than the diamond, which a normal form would break). -/
theorem confluentOfDeterministic {rel : Carrier → Carrier → Prop}
    (det : IsDeterministic rel) : Confluent rel := by
  intro source leftReduct rightReduct leftChain rightChain
  exact confluentOfDeterministicAux (rel := rel) det leftChain rightChain

/-- **Weak-head reduction is confluent** (the concrete payoff).  `WeakHeadStep` has at most one reduct per term
(`WeakHeadStep.deterministic`), so its reflexive-transitive closure is Church-Rosser. -/
theorem WeakHeadStep.hasConfluence {scope : Nat} :
    Confluent (@WeakHeadStep scope) :=
  confluentOfDeterministic (rel := @WeakHeadStep scope)
    (fun firstStep secondStep => WeakHeadStep.deterministic firstStep secondStep)

end FX1Poly.Core
