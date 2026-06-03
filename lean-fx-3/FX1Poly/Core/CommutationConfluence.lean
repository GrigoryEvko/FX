import FX1Poly.Core.DiamondConfluence

/-! # FX1Poly/Core/CommutationConfluence
    — Hindley-Rosen via the diamond: commuting diamonds give a confluent union (abstract toolkit)

The third abstract confluence route, after `Newman.lean` (terminating + weakly confluent) and
`DiamondConfluence.lean` (diamond, no termination).  This one is MODULAR: instead of proving a single
monolithic parallel reduction confluent, it combines TWO separately-confluent relations whose diamonds
COMMUTE into a confluent union — the Hindley-Rosen "commutative union" lemma, proved here through the
diamond method rather than through termination.

The intended FX use is the beta/iota decomposition: the FX raw step relation is beta-reduction together
with the iota (eliminator-on-constructor) family.  Rather than build one parallel reduction over all 20
`Step` constructors and prove its diamond directly, one can build a beta parallel reduction and an iota
parallel reduction separately (each smaller, each orthogonal in its own family), prove each has the
diamond, prove they strongly commute (beta and iota fire at disjoint head positions, so a beta-step and
an iota-step from the same source never interfere), and combine with `confluentUnionOfParallelDiamonds`.

## What is proved

* `StronglyCommutes` — a single R-step and a single S-step from the same source reconverge in a single
  S-step and a single R-step (the commuting diamond between two relations).
* `DiamondProperty.union` — two relations with the diamond that strongly commute have a union with the
  diamond (four-way case split: R/R via R's diamond, S/S via S's diamond, the mixed R/S and S/R via
  commutation).
* `confluentOfUnionDiamonds` — **Hindley-Rosen via the diamond**: commuting diamonds give a confluent
  union (immediate from `DiamondProperty.union` and `diamondConfluence`).
* `confluentUnionOfParallelDiamonds` — **the modular union recipe**: two single-step relations, each
  simulated by a parallel relation with the diamond, whose parallel relations strongly commute, have a
  confluent union.  This is the two-relation generalization of `confluentOfDiamondSimulation`.

## Zero-axiom verification

All proofs are `rcases` over the union disjunction plus `obtain` on the diamond/commutation existentials,
delegating to the shipped `diamondConfluence` / `confluentOfDiamondSimulation`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Carrier : Type carrierUniverse}

/-- Two relations **strongly commute** when a single `relR`-step and a single `relS`-step from the same
source reconverge in a single `relS`-step and a single `relR`-step. -/
def StronglyCommutes (relR relS : Carrier → Carrier → Prop) : Prop :=
  ∀ {source rStep sStep : Carrier},
    relR source rStep → relS source sStep →
      ∃ joinPoint, relS rStep joinPoint ∧ relR sStep joinPoint

/-- The union of two relations with the diamond property that strongly commute itself has the diamond.
Four-way case split on which relation supplied each of the two divergent steps: like/like reconverges by
that relation's own diamond, mixed reconverges by strong commutation. -/
theorem DiamondProperty.union {relR relS : Carrier → Carrier → Prop}
    (diamondR : DiamondProperty relR) (diamondS : DiamondProperty relS)
    (commute : StronglyCommutes relR relS) :
    DiamondProperty (fun a b => relR a b ∨ relS a b) := by
  intro source leftStep rightStep leftOr rightOr
  rcases leftOr with leftR | leftS
  · rcases rightOr with rightR | rightS
    · obtain ⟨joinPoint, leftToJoin, rightToJoin⟩ := diamondR leftR rightR
      exact ⟨joinPoint, Or.inl leftToJoin, Or.inl rightToJoin⟩
    · obtain ⟨joinPoint, leftToJoin, rightToJoin⟩ := commute leftR rightS
      exact ⟨joinPoint, Or.inr leftToJoin, Or.inl rightToJoin⟩
  · rcases rightOr with rightR | rightS
    · obtain ⟨joinPoint, rightToJoin, leftToJoin⟩ := commute rightR leftS
      exact ⟨joinPoint, Or.inl leftToJoin, Or.inr rightToJoin⟩
    · obtain ⟨joinPoint, leftToJoin, rightToJoin⟩ := diamondS leftS rightS
      exact ⟨joinPoint, Or.inr leftToJoin, Or.inr rightToJoin⟩

/-- **Hindley-Rosen via the diamond.**  Two relations, each with the diamond property, that strongly
commute have a confluent union — no termination needed. -/
theorem confluentOfUnionDiamonds {relR relS : Carrier → Carrier → Prop}
    (diamondR : DiamondProperty relR) (diamondS : DiamondProperty relS)
    (commute : StronglyCommutes relR relS) :
    Confluent (fun a b => relR a b ∨ relS a b) :=
  diamondConfluence (DiamondProperty.union diamondR diamondS commute)

/-- **The modular union recipe.**  Two single-step relations `relR`, `relS`, each simulated by a parallel
relation (`relR ⊆ parR`, `relS ⊆ parS`, and each parallel relation collapses into the union's
reflexive-transitive closure) with the diamond, whose parallel relations strongly commute, have a
confluent union.  The two-relation generalization of `confluentOfDiamondSimulation`: it lets confluence of
`relR ∪ relS` be assembled from a `parR` diamond, a `parS` diamond, and their commutation, rather than
from one monolithic parallel reduction over the combined system. -/
theorem confluentUnionOfParallelDiamonds {relR relS parR parS : Carrier → Carrier → Prop}
    (rToParR : ∀ {a b : Carrier}, relR a b → parR a b)
    (sToParS : ∀ {a b : Carrier}, relS a b → parS a b)
    (parRToRel : ∀ {a b : Carrier}, parR a b → ReflTransClosure (fun x y => relR x y ∨ relS x y) a b)
    (parSToRel : ∀ {a b : Carrier}, parS a b → ReflTransClosure (fun x y => relR x y ∨ relS x y) a b)
    (diamondParR : DiamondProperty parR) (diamondParS : DiamondProperty parS)
    (commute : StronglyCommutes parR parS) :
    Confluent (fun a b => relR a b ∨ relS a b) := by
  refine confluentOfDiamondSimulation
    (parRel := fun a b => parR a b ∨ parS a b)
    (fun {_ _} stepOr => ?_)
    (fun {_ _} parOr => ?_)
    (DiamondProperty.union diamondParR diamondParS commute)
  · rcases stepOr with stepR | stepS
    · exact Or.inl (rToParR stepR)
    · exact Or.inr (sToParS stepS)
  · rcases parOr with parRWitness | parSWitness
    · exact parRToRel parRWitness
    · exact parSToRel parSWitness

end FX1Poly.Core
