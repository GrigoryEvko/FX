import FX1Poly.Core.Rewriting.Confluence.KnuthBendixCompletion

/-! # FX1Poly/Core/Rewriting/Confluence/ConvergentNormalizerOfReducer
    — the GENERIC normalizer builder: any sound+complete deterministic reducer over a strongly-normalizing
      relation yields a `ConvergentNormalizer`, hence (with confluence) decidable conversion

`KnuthBendixCompletion.lean` ships the abstract decision engine: a `ConvergentNormalizer rel` (a `normalize`
function + reach + normal-form facts) plus `Confluent rel` and `DecidableEq Carrier` DECIDE the equational
theory `⟷*` (`ConvergentNormalizer.decidableEquationalTheory`).  But it leaves the `normalize` function as
DATA — "termination would PRODUCE such a function by well-founded recursion, but `WellFounded.fix` is
unavailable zero-axiom".

This file closes that gap GENERICALLY.  The kernel's `RawTerm.normalize` already builds the function for the
beta/iota `Step` relation by `Acc.rec` over the strong-normalization witness (large-eliminating the
`Prop`-valued `Acc` into the `Type`-valued carrier — axiom-free, unlike `WellFounded.fix`).  That
construction is entirely relation-agnostic: it only needs a deterministic one-step reducer that is SOUND
(each fired step is a real `rel`-step, so the successor stays accessible — the descent) and COMPLETE (it
halts exactly at terms with no outgoing step — the right place to stop), plus the accessibility witness.

So this file lifts the recipe to an ABSTRACT relation:

  * `reducerNormalize` — the `Acc.rec` iterator (fire the reducer until it halts), with `reducerNormalize_unfold`
    by `rfl`.
  * `reducerNormalize_reducesTo` / `reducerNormalize_isNormalForm` — reach + normality, by `Acc`-induction +
    `split`.
  * **`ConvergentNormalizer.ofReducer` (★)** — bundle them: a sound+complete deterministic reducer over an
    SN relation IS a `ConvergentNormalizer`.
  * **`decidableEquationalTheoryOfReducerSN` (★)** — the end-to-end payoff: SN + confluence + a
    sound+complete reducer + `DecidableEq` ⟹ `Decidable (EquationalTheory rel a b)`.  The reusable engine
    that turns any convergent row (definitional univalence, cost optimization, any future extension) into a
    decision procedure once its reducer is supplied.

## Zero-axiom verification

`Acc.rec` (a recursor, axiom-free — NOT `WellFounded.fix`), `Acc`-induction, `split` on the reducer result,
and the abstract `ConvergentNormalizer` engine.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Carrier : Type carrierUniverse}

/-- **The abstract normalizer.**  Fire the deterministic reducer `reduceStep` along the accessibility witness
until it halts; the result is the normal form of `value`.  Written with `Acc.rec` (the well-founded recursion
PRIMITIVE that large-eliminates the `Prop`-valued `Acc` into the `Type`-valued carrier) because the descent
shrinks the accessibility proof, not the value — the reducer need not decrease any structural measure. -/
def reducerNormalize {rel : Carrier → Carrier → Prop} (reduceStep : Carrier → Option Carrier)
    (reduceStep_sound : ∀ {origin reduct : Carrier}, reduceStep origin = some reduct → rel origin reduct)
    (value : Carrier) (accessible : Acc (fun reduct origin => rel origin reduct) value) : Carrier :=
  Acc.rec
    (motive := fun _currentValue _acc => Carrier)
    (fun currentValue _accStep normalizeRec =>
      match hReduce : reduceStep currentValue with
      | none => currentValue
      | some reduct => normalizeRec reduct (reduceStep_sound hReduce))
    accessible

/-- One-step unfolding of `reducerNormalize` at an `Acc.intro` witness (holds by `rfl` via the `Acc.rec`
computation rule — the proof handle for the correctness theorems). -/
theorem reducerNormalize_unfold {rel : Carrier → Carrier → Prop} (reduceStep : Carrier → Option Carrier)
    (reduceStep_sound : ∀ {origin reduct : Carrier}, reduceStep origin = some reduct → rel origin reduct)
    (value : Carrier)
    (accStep : ∀ later, (fun reduct origin => rel origin reduct) later value →
      Acc (fun reduct origin => rel origin reduct) later) :
    reducerNormalize reduceStep reduceStep_sound value (Acc.intro value accStep) =
      (match hReduce : reduceStep value with
        | none => value
        | some reduct =>
            reducerNormalize reduceStep reduceStep_sound reduct (accStep reduct (reduceStep_sound hReduce))) :=
  rfl

/-- **The abstract normalizer reaches its output by a reduction chain.**  By `Acc`-induction: a halted step is
the reflexive chain; a fired step prepends `reduceStep_sound` to the inductive chain. -/
theorem reducerNormalize_reducesTo {rel : Carrier → Carrier → Prop} (reduceStep : Carrier → Option Carrier)
    (reduceStep_sound : ∀ {origin reduct : Carrier}, reduceStep origin = some reduct → rel origin reduct)
    (value : Carrier) (accessible : Acc (fun reduct origin => rel origin reduct) value) :
    ReflTransClosure rel value (reducerNormalize reduceStep reduceStep_sound value accessible) := by
  induction accessible with
  | intro currentValue accStep ih =>
      rw [reducerNormalize_unfold reduceStep reduceStep_sound currentValue accStep]
      split
      · exact ReflTransClosure.refl _
      · next reduct hReduce =>
          exact ReflTransClosure.head (reduceStep_sound hReduce) (ih reduct (reduceStep_sound hReduce))

/-- **The abstract normalizer's output has no outgoing step.**  By `Acc`-induction: a halted step gives
normality by `reduceStep_complete`; a fired step defers to the inductive hypothesis. -/
theorem reducerNormalize_isNormalForm {rel : Carrier → Carrier → Prop} (reduceStep : Carrier → Option Carrier)
    (reduceStep_sound : ∀ {origin reduct : Carrier}, reduceStep origin = some reduct → rel origin reduct)
    (reduceStep_complete : ∀ {origin : Carrier}, reduceStep origin = none → ∀ next, ¬ rel origin next)
    (value : Carrier) (accessible : Acc (fun reduct origin => rel origin reduct) value) :
    ∀ next, ¬ rel (reducerNormalize reduceStep reduceStep_sound value accessible) next := by
  induction accessible with
  | intro currentValue accStep ih =>
      rw [reducerNormalize_unfold reduceStep reduceStep_sound currentValue accStep]
      split
      · next hReduce => exact reduceStep_complete hReduce
      · next reduct hReduce => exact ih reduct (reduceStep_sound hReduce)

/-- **★ A sound+complete deterministic reducer over an SN relation IS a `ConvergentNormalizer`.**  Bundles
`reducerNormalize` with its reach + normal-form facts — the generic construction of the normalizer that the
abstract Knuth-Bendix engine takes as data.  Reusable across every convergent row (definitional univalence,
cost optimization, any future extension): supply the reducer and the SN witness, get the normal-form
function. -/
def ConvergentNormalizer.ofReducer {rel : Carrier → Carrier → Prop} (reduceStep : Carrier → Option Carrier)
    (reduceStep_sound : ∀ {origin reduct : Carrier}, reduceStep origin = some reduct → rel origin reduct)
    (reduceStep_complete : ∀ {origin : Carrier}, reduceStep origin = none → ∀ next, ¬ rel origin next)
    (terminating : ∀ value, Acc (fun reduct origin => rel origin reduct) value) :
    ConvergentNormalizer rel where
  normalize value := reducerNormalize reduceStep reduceStep_sound value (terminating value)
  reducesToNormalForm value :=
    reducerNormalize_reducesTo reduceStep reduceStep_sound value (terminating value)
  normalFormIsNormal value :=
    reducerNormalize_isNormalForm reduceStep reduceStep_sound reduceStep_complete value (terminating value)

/-- **★ The end-to-end decision engine.**  A CONFLUENT, strongly-normalizing relation equipped with a
sound+complete deterministic reducer DECIDES its equational theory (decide `a ⟷* b` by normalizing both and
comparing) — assuming the carrier has decidable equality.  The reusable bridge from "convergent rewrite
system + computable reducer" to a real decision procedure, with the normalizer built by `Acc.rec` (no
`WellFounded.fix`, no axioms). -/
def decidableEquationalTheoryOfReducerSN {rel : Carrier → Carrier → Prop} [DecidableEq Carrier]
    (reduceStep : Carrier → Option Carrier)
    (reduceStep_sound : ∀ {origin reduct : Carrier}, reduceStep origin = some reduct → rel origin reduct)
    (reduceStep_complete : ∀ {origin : Carrier}, reduceStep origin = none → ∀ next, ¬ rel origin next)
    (terminating : ∀ value, Acc (fun reduct origin => rel origin reduct) value)
    (confluent : Confluent rel) (leftValue rightValue : Carrier) :
    Decidable (EquationalTheory rel leftValue rightValue) :=
  (ConvergentNormalizer.ofReducer reduceStep reduceStep_sound reduceStep_complete terminating).decidableEquationalTheory
    confluent leftValue rightValue

end FX1Poly.Core
