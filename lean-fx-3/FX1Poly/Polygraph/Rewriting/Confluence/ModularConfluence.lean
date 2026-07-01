import FX1Poly.Polygraph.Rewriting.Confluence.CommutationConfluence

/-! # Core/Rewriting/Confluence — modular confluence: the textbook Hindley-Rosen / Toyama engine

`CommutationConfluence.lean` ships `confluentOfUnionDiamonds` — the DIAMOND form of Hindley-Rosen (two
relations, each with the single-step diamond property, that strongly commute, have a confluent union).
This file lifts it to the textbook CLOSURE form recognizable as the abstract engine of Toyama's
confluence-modularity theorem: if `relR` and `relS` are each CONFLUENT (Church-Rosser) and their
reflexive-transitive CLOSURES strongly commute, then the union `relR ∪ relS` is confluent.

## The lift (no propositional extensionality)

KEY OBSERVATION: `Confluent relR` is, by definition, `DiamondProperty (ReflTransClosure relR)` — a peak of
two many-step `relR`-reductions joins.  So each side's confluence IS the diamond of its closure, and
`confluentOfUnionDiamonds` applies AT THE CLOSURES, giving `Confluent (R* ∪ S*)`.  Since the union and the
union-of-closures generate the same reflexive-transitive closure — `(R ∪ S)* = (R* ∪ S*)*`, by the mutual
`ReflTransClosure.monotone` (forward) and `ReflTransClosure.collapse` (back) inclusions — confluence
transports to `Confluent (R ∪ S)`.  No `propext` is needed: the transport pushes each reduction along an
inclusion pointwise rather than rewriting the relation.

## What this is and is not

This is the abstract core of TOYAMA'S CONFLUENCE-MODULARITY theorem: for a disjoint union of term rewriting
systems, the disjoint signatures supply the closure-commutation, and modular confluence follows.  The
disjoint-signature ⟹ commute layer (the rank/layer analysis specific to first-order terms) is NOT here —
only the abstract Hindley-Rosen engine, over arbitrary relations.

CAVEAT (the asymmetry that makes Toyama's CONFLUENCE result interesting): confluence is modular, but strong
normalization is famously NOT — Toyama's counterexample shows `SN(R)` and `SN(S)` do not give `SN(R ∪ S)`.
That is why the modular-SN companion `accUnion` carries an explicit quasi-commutation hypothesis, while
this confluence engine needs only commutation of the closures.

## Zero-axiom verification

All proofs are `Or.elim` / `ReflTransClosure.monotone` / `ReflTransClosure.collapse` over the shipped
abstract confluence layer, plus the `Confluent ≡ DiamondProperty ∘ ReflTransClosure` definitional identity.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditCoreTerminationOrders.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Carrier : Type carrierUniverse}

/-- ★ **The textbook Hindley-Rosen / Toyama confluence engine.**  If `relR` and `relS` are each confluent
and their reflexive-transitive closures strongly commute, the union `relR ∪ relS` is confluent.

`Confluent relR` IS `DiamondProperty (ReflTransClosure relR)`, so `confluentOfUnionDiamonds` yields
`Confluent (R* ∪ S*)`; the result transports across `(R ∪ S)* = (R* ∪ S*)*` — `monotone` forward (each
union step is a one-step closure of its side), `collapse` back (each closure step is a union reduction). -/
theorem confluentOfCommutingConfluent {relR relS : Carrier → Carrier → Prop}
    (confluentR : Confluent relR) (confluentS : Confluent relS)
    (commuteClosures :
      StronglyCommutes (ReflTransClosure relR) (ReflTransClosure relS)) :
    Confluent (fun source target => relR source target ∨ relS source target) := by
  have unionClosureConfluent :
      Confluent (fun source target =>
        ReflTransClosure relR source target ∨ ReflTransClosure relS source target) :=
    confluentOfUnionDiamonds
      (relR := ReflTransClosure relR) (relS := ReflTransClosure relS)
      confluentR confluentS commuteClosures
  intro source leftReduct rightReduct leftChain rightChain
  -- forward: every (relR ∪ relS) step is a one-step closure of its side
  have stepIntoClosureUnion : ∀ {first second : Carrier},
      (relR first second ∨ relS first second)
        → (ReflTransClosure relR first second ∨ ReflTransClosure relS first second) :=
    fun stepOr => stepOr.elim
      (fun stepR => Or.inl (ReflTransClosure.single stepR))
      (fun stepS => Or.inr (ReflTransClosure.single stepS))
  -- back: every (R* ∪ S*) step is a (relR ∪ relS) reduction (map each side's chain into the union)
  have closureUnionIntoUnionChain : ∀ {first second : Carrier},
      (ReflTransClosure relR first second ∨ ReflTransClosure relS first second)
        → ReflTransClosure (fun a b => relR a b ∨ relS a b) first second :=
    fun closureOr => closureOr.elim
      (fun chainR => ReflTransClosure.monotone (fun stepR => Or.inl stepR) chainR)
      (fun chainS => ReflTransClosure.monotone (fun stepS => Or.inr stepS) chainS)
  obtain ⟨commonReduct, leftToCommon, rightToCommon⟩ :=
    unionClosureConfluent
      (ReflTransClosure.monotone stepIntoClosureUnion leftChain)
      (ReflTransClosure.monotone stepIntoClosureUnion rightChain)
  exact ⟨commonReduct,
    ReflTransClosure.collapse closureUnionIntoUnionChain leftToCommon,
    ReflTransClosure.collapse closureUnionIntoUnionChain rightToCommon⟩

/-! ## A concrete witness — the modular-confluence criterion is non-vacuous -/

/-- The **complete relation** on `Bool` (everything reduces to everything in one step) — a concrete
confluent reduction with genuine steps (`completeReduction true false` holds). -/
def completeReduction : Bool → Bool → Prop := fun _ _ => True

/-- The complete relation is confluent: any two reducts join, since everything reduces to anything. -/
theorem completeReduction_isConfluent : Confluent completeReduction := by
  intro _source leftReduct rightReduct _leftChain _rightChain
  exact ⟨leftReduct, ReflTransClosure.refl leftReduct, ReflTransClosure.single True.intro⟩

/-- The complete relation's reflexive-transitive closure strongly commutes with itself. -/
theorem completeReduction_closuresCommute :
    StronglyCommutes (ReflTransClosure completeReduction) (ReflTransClosure completeReduction) := by
  intro _source rStep _sStep _rChain _sChain
  exact ⟨rStep, ReflTransClosure.refl rStep, ReflTransClosure.single True.intro⟩

/-- ★ **The modular-confluence criterion is NON-VACUOUS.**  Two confluent reductions (here both the complete
relation, which has real steps) whose closures commute yield a confluent union — the modular engine
`confluentOfCommutingConfluent` fires and produces a genuine `Confluent` witness. -/
theorem completeModularConfluence :
    Confluent (fun source target =>
      completeReduction source target ∨ completeReduction source target) :=
  confluentOfCommutingConfluent completeReduction_isConfluent completeReduction_isConfluent
    completeReduction_closuresCommute

end FX1Poly.Core
