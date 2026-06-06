/-! # FX1Poly/Core/Newman
    — the abstract Newman's lemma: terminating + weakly confluent ⟹ confluent

Newman's lemma is the confluence analogue of the termination orders: a generic, reusable
metatheorem — a TERMINATING (strongly-normalizing), WEAKLY (locally) confluent relation is CONFLUENT
(Church-Rosser).  It is the abstract core the confluence arc instantiates: the typed
fragment applies it (SN + local CR ⟹ global CR, gated on typed SN); the FX word system `fxSystem` applies it too.

The relation is abstract (`Carrier → Carrier → Prop`), so this single proof serves every instantiation.  The
existing confluence vocabulary in the codebase is system-specific (`StepStar.Join` over `RawTerm`, OmegacE
`Joinable` over `OmegacEWord`); this is the generic version over an arbitrary relation, with its own
reflexive-transitive closure (`Relation.ReflTransGen` is Mathlib-only, not `Init`).

## What is proved

* `ReflTransClosure` — the reflexive-transitive closure of a relation (head-extension form), with `single`
  (one step) and `trans` (composition).
* `Joinable` / `WeaklyConfluent` / `Confluent` — the confluence vocabulary (common reduct; divergent single
  steps join; divergent many-step reductions join).
* `newmanAux` — the confluence core, by well-founded induction on the terminating source (the classic tiling:
  weak confluence on the two first steps, then the induction hypothesis at each reduct, composed).
* `newman` — **Newman's lemma**: `WellFounded (flip rel)` (termination) + `WeaklyConfluent rel` ⟹ `Confluent rel`.

## Zero-axiom verification

The closure is a plain inductive; `cases` on it is propext-clean (its indices are free variables, NOT
constructor patterns — unlike a cons/succ index); `trans` and the tiling are structural inductions / `obtain`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Carrier : Type carrierUniverse}

/-- Reflexive-transitive closure of a relation (head-extension form: one step, then the rest). -/
inductive ReflTransClosure (rel : Carrier → Carrier → Prop) : Carrier → Carrier → Prop where
  /-- Zero steps. -/
  | refl (point : Carrier) : ReflTransClosure rel point point
  /-- One step, then a shorter chain. -/
  | head {source middle target : Carrier}
      (first : rel source middle) (rest : ReflTransClosure rel middle target) :
      ReflTransClosure rel source target

/-- A single step is a reflexive-transitive chain. -/
theorem ReflTransClosure.single {rel : Carrier → Carrier → Prop} {source target : Carrier}
    (step : rel source target) : ReflTransClosure rel source target :=
  ReflTransClosure.head step (ReflTransClosure.refl target)

/-- Reflexive-transitive chains compose. -/
theorem ReflTransClosure.trans {rel : Carrier → Carrier → Prop} {source middle target : Carrier}
    (firstChain : ReflTransClosure rel source middle)
    (secondChain : ReflTransClosure rel middle target) :
    ReflTransClosure rel source target := by
  induction firstChain with
  | refl _ => exact secondChain
  | head first _rest inductionHypothesis =>
      exact ReflTransClosure.head first (inductionHypothesis secondChain)

/-- Two elements **join** when they reduce to a common reduct. -/
def Joinable (rel : Carrier → Carrier → Prop) (leftValue rightValue : Carrier) : Prop :=
  ∃ commonReduct,
    ReflTransClosure rel leftValue commonReduct ∧ ReflTransClosure rel rightValue commonReduct

/-- **Weak (local) confluence**: divergent single steps join. -/
def WeaklyConfluent (rel : Carrier → Carrier → Prop) : Prop :=
  ∀ {source leftStep rightStep : Carrier},
    rel source leftStep → rel source rightStep → Joinable rel leftStep rightStep

/-- **Confluence (Church-Rosser)**: divergent many-step reductions join. -/
def Confluent (rel : Carrier → Carrier → Prop) : Prop :=
  ∀ {source leftReduct rightReduct : Carrier},
    ReflTransClosure rel source leftReduct → ReflTransClosure rel source rightReduct →
      Joinable rel leftReduct rightReduct

/-- The confluence core, by well-founded induction on the (terminating) source.  In the head/head case: weak
confluence joins the two first steps at `joinStep`; the induction hypothesis at `sourceLeft` joins the left reduct
and `joinStep` at `leftMeet`; the induction hypothesis at `sourceRight` joins the right reduct and (the chain to)
`leftMeet` at `finalMeet`; the two outer chains compose to a common reduct. -/
theorem newmanAux {rel : Carrier → Carrier → Prop}
    (weaklyConfluent : WeaklyConfluent rel) (source : Carrier)
    (accSource : Acc (fun reduct origin => rel origin reduct) source) :
    ∀ {leftReduct rightReduct : Carrier},
      ReflTransClosure rel source leftReduct → ReflTransClosure rel source rightReduct →
        Joinable rel leftReduct rightReduct := by
  induction accSource with
  | intro source _accPred ihSource =>
    intro leftReduct rightReduct leftChain rightChain
    cases leftChain with
    | refl => exact ⟨rightReduct, rightChain, ReflTransClosure.refl rightReduct⟩
    | head sourceLeft leftRest =>
      cases rightChain with
      | refl =>
          exact ⟨leftReduct, ReflTransClosure.refl leftReduct,
            ReflTransClosure.head sourceLeft leftRest⟩
      | head sourceRight rightRest =>
        obtain ⟨joinStep, leftStepToJoin, rightStepToJoin⟩ :=
          weaklyConfluent sourceLeft sourceRight
        obtain ⟨leftMeet, leftToMeet, joinToMeet⟩ :=
          ihSource _ sourceLeft leftRest leftStepToJoin
        obtain ⟨finalMeet, rightToFinal, leftMeetToFinal⟩ :=
          ihSource _ sourceRight rightRest (rightStepToJoin.trans joinToMeet)
        exact ⟨finalMeet, leftToMeet.trans leftMeetToFinal, rightToFinal⟩

/-- **Newman's lemma**: a terminating (`WellFounded` of the flipped relation), weakly-confluent relation is
confluent. -/
theorem newman {rel : Carrier → Carrier → Prop}
    (terminating : WellFounded (fun reduct origin => rel origin reduct))
    (weaklyConfluent : WeaklyConfluent rel) : Confluent rel := by
  intro source leftReduct rightReduct leftChain rightChain
  exact newmanAux weaklyConfluent source (terminating.apply source) leftChain rightChain

end FX1Poly.Core
