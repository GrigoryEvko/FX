import FX1Poly.Core.Newman

/-! # FX1Poly/Core/DiamondConfluence
    — the diamond ⟹ confluence route (strip lemma + parallel-reduction recipe)

The SECOND abstract route to confluence, complementing Newman (`Newman.lean`).  Newman derives confluence from
TERMINATION + weak confluence; this file derives it from the DIAMOND PROPERTY alone — no termination needed.  It
is the Tait/Martin-Löf/Takahashi method: single-step reduction rarely has the diamond (one β-redex can duplicate
another), but PARALLEL reduction (contract any set of redexes at once) does, and parallel reduction is sandwiched
between single-step and its closure — so the single-step relation is confluent.  This is the generic core of
raw confluence: the table lane (`TableTakahashiTriangle`) exhibits the parallel-reduction diamond over the iota
table, and `confluentOfDiamondSimulation` / `diamondConfluence` turn it into raw confluence.

Reuses the `ReflTransClosure` / `Joinable` / `Confluent` vocabulary from `Newman.lean`.

## What is proved

* `ReflTransClosure.monotone` / `collapse` — reflexive-transitive closure is monotone in the relation, and
  collapses a closure-of-`rel` into a closure-of-`base` when every `rel` step is a `base` closure (the sandwich
  glue).
* `DiamondProperty` — divergent single steps reconverge in single steps.
* `stripLemma` — a single step strips against a many-step reduction (the diamond, lifted to single-vs-many).
* `diamondConfluenceAux` / `diamondConfluence` — **diamond ⟹ confluence**: a relation with the diamond property
  has confluent reflexive-transitive closure (strip on each left first step against the whole right chain).
* `confluentOfDiamondSimulation` — **the parallel-reduction recipe**: if `rel ⊆ parRel ⊆ ReflTransClosure rel`
  and `parRel` has the diamond, then `rel` is confluent (lift both chains to `parRel`, confluence there, collapse
  back).

## Zero-axiom verification

All proofs are structural inductions over `ReflTransClosure` (propext-clean: free-variable indices) plus
`obtain` on the diamond / `Joinable` existentials.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Carrier : Type carrierUniverse}

/-- The reflexive-transitive closure is monotone in the underlying relation. -/
theorem ReflTransClosure.monotone {rel1 rel2 : Carrier → Carrier → Prop}
    (sub : ∀ {a b : Carrier}, rel1 a b → rel2 a b)
    {source target : Carrier} (chain : ReflTransClosure rel1 source target) :
    ReflTransClosure rel2 source target := by
  induction chain with
  | refl point => exact ReflTransClosure.refl point
  | head first _rest inductionHypothesis =>
      exact ReflTransClosure.head (sub first) inductionHypothesis

/-- If every `rel` step is a `base` reflexive-transitive chain, a `rel`-closure collapses into a `base`-closure. -/
theorem ReflTransClosure.collapse {rel base : Carrier → Carrier → Prop}
    (sub : ∀ {a b : Carrier}, rel a b → ReflTransClosure base a b)
    {source target : Carrier} (chain : ReflTransClosure rel source target) :
    ReflTransClosure base source target := by
  induction chain with
  | refl point => exact ReflTransClosure.refl point
  | head first _rest inductionHypothesis => exact (sub first).trans inductionHypothesis

/-- The **diamond property**: divergent single steps reconverge in single steps. -/
def DiamondProperty (rel : Carrier → Carrier → Prop) : Prop :=
  ∀ {source leftStep rightStep : Carrier},
    rel source leftStep → rel source rightStep →
      ∃ joinPoint, rel leftStep joinPoint ∧ rel rightStep joinPoint

/-- **Strip lemma**: a single step strips against a many-step reduction.  By induction on the many chain, the
diamond property closes each first step, then the induction hypothesis strips the remainder. -/
theorem stripLemma {rel : Carrier → Carrier → Prop} (diamond : DiamondProperty rel)
    {source manyTarget : Carrier} (manyChain : ReflTransClosure rel source manyTarget) :
    ∀ {oneTarget : Carrier}, rel source oneTarget →
      ∃ joinPoint,
        ReflTransClosure rel oneTarget joinPoint ∧ ReflTransClosure rel manyTarget joinPoint := by
  induction manyChain with
  | refl point =>
      intro oneTarget oneStep
      exact ⟨oneTarget, ReflTransClosure.refl oneTarget, ReflTransClosure.single oneStep⟩
  | head firstStep _rest ihRest =>
      intro oneTarget oneStep
      obtain ⟨diamondMeet, oneToMeet, midToMeet⟩ := diamond oneStep firstStep
      obtain ⟨finalMeet, meetToFinal, manyToFinal⟩ := ihRest midToMeet
      exact ⟨finalMeet, (ReflTransClosure.single oneToMeet).trans meetToFinal, manyToFinal⟩

/-- The confluence core (right chain kept quantified so the induction hypothesis ranges over all right targets):
strip each left first step against the whole right chain, recurse on the left remainder, compose. -/
theorem diamondConfluenceAux {rel : Carrier → Carrier → Prop} (diamond : DiamondProperty rel)
    {source leftReduct : Carrier} (leftChain : ReflTransClosure rel source leftReduct) :
    ∀ {rightReduct : Carrier}, ReflTransClosure rel source rightReduct →
      Joinable rel leftReduct rightReduct := by
  induction leftChain with
  | refl point =>
      intro rightReduct rightChain
      exact ⟨rightReduct, rightChain, ReflTransClosure.refl rightReduct⟩
  | head firstStep _leftRest ihLeftRest =>
      intro rightReduct rightChain
      obtain ⟨stripMeet, midToStrip, rightToStrip⟩ := stripLemma diamond rightChain firstStep
      obtain ⟨finalMeet, leftToFinal, stripToFinal⟩ := ihLeftRest midToStrip
      exact ⟨finalMeet, leftToFinal, rightToStrip.trans stripToFinal⟩

/-- **Diamond ⟹ confluence**: a relation with the diamond property has confluent reflexive-transitive closure
(no termination needed). -/
theorem diamondConfluence {rel : Carrier → Carrier → Prop}
    (diamond : DiamondProperty rel) : Confluent rel := by
  intro source leftReduct rightReduct leftChain rightChain
  exact diamondConfluenceAux diamond leftChain rightChain

/-- **The parallel-reduction confluence recipe**: if `rel` is sandwiched by a relation `parRel` that has the
diamond property (`rel ⊆ parRel ⊆ ReflTransClosure rel`), then `rel` is confluent.  Lift both reductions to
`parRel`, apply diamond-confluence there, collapse the joins back to `rel`.  This is how single-step β-reduction
(which lacks the diamond) is proved confluent through parallel reduction. -/
theorem confluentOfDiamondSimulation {rel parRel : Carrier → Carrier → Prop}
    (relToPar : ∀ {a b : Carrier}, rel a b → parRel a b)
    (parToRel : ∀ {a b : Carrier}, parRel a b → ReflTransClosure rel a b)
    (diamond : DiamondProperty parRel) : Confluent rel := by
  intro source leftReduct rightReduct leftChain rightChain
  obtain ⟨meet, leftToMeet, rightToMeet⟩ :=
    diamondConfluence diamond (leftChain.monotone relToPar) (rightChain.monotone relToPar)
  exact ⟨meet, leftToMeet.collapse parToRel, rightToMeet.collapse parToRel⟩

end FX1Poly.Core
