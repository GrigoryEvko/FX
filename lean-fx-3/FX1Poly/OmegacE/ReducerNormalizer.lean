import FX1Poly.OmegacE.WordProblem

/-! # FX1Poly/OmegacE/ReducerNormalizer
    — a normalizer from termination + a searchable reducer; the full convergent-presentation decidability

`WordProblem.lean` decided convertibility from a `WordNormalizer` + confluence, and `Confluence.lean`'s
`newman` discharges confluence from local confluence + termination.  The remaining piece is BUILDING a
`WordNormalizer` from termination — this file does it, the word analog of the term-layer `RawTerm.normalize`
(`FX1Poly/Core/Normalize.lean`).

* `WordReducer system` — a sound + complete one-step reducer (`reduceOnce : Word → Option Word`); the
  searchable engine a concrete system provides (decidable rule-matching).
* `WordReducer.normalize` — iterate `reduceOnce` along the termination accessibility witness (`Acc.rec`,
  axiom-free; the descent shrinks the accessibility proof, not the word).
* `normalize_reaches` / `normalize_blocksStep` — its correctness (reaches its output; the output is normal).
* `WordReducer.toNormalizer` — termination + a reducer ⟹ a `WordNormalizer`.
* `decidableConvertibleModulo_ofConvergent` — THE convergent-presentation decidability: **local confluence +
  termination + a searchable reducer ⟹ decidable word problem** (compose `newman` → `toNormalizer` →
  `decidableOfNormalizer`).  Every hypothesis is checkable for a concrete system, so this fully reduces the
  Makkai word problem to: provide a reducer, a termination measure, and a critical-pair (local-confluence)
  check.

## Honest scope

The three inputs are exactly the standard convergent-rewriting obligations a CONCRETE system discharges (a
length measure for termination, a rule-matcher for the reducer, critical-pair analysis for local confluence).
This file packages them into the decision; it does not exhibit a non-trivial concrete system (the next
Path-B atom) nor bridge to the FX `Step` relation.

## Zero-axiom verification

`Acc.rec` (a recursor) + `Acc`-induction + `split` on the reducer result + the reducer's soundness/completeness
+ `RewritesMany.step`/`refl`, composed with the shipped `newman` / `decidableOfNormalizer`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- A **sound + complete one-step reducer** for a rule system: `reduceOnce` fires a real rewrite when it
returns `some`, and reports a normal form (no possible rewrite) when it returns `none`.  The searchable engine
a concrete system supplies (decidable rule matching). -/
structure WordReducer {dimension : Nat} (system : OmegacERewriteRule dimension → Prop) where
  /-- Fire one rewrite step if any applies. -/
  reduceOnce : OmegacEWord dimension → Option (OmegacEWord dimension)
  /-- A produced reduct is a genuine one-step rewrite. -/
  reduceOnce_sound : ∀ {word reduct : OmegacEWord dimension},
    reduceOnce word = some reduct → OmegacEWord.RewritesOneStep system word reduct
  /-- A `none` result means the word is a normal form. -/
  reduceOnce_complete : ∀ {word : OmegacEWord dimension},
    reduceOnce word = none → ∀ reduct, ¬ OmegacEWord.RewritesOneStep system word reduct

/-- **The normalizer** driven by a reducer along a termination accessibility witness: iterate `reduceOnce`
until it halts.  `Acc.rec` because the descent shrinks the accessibility proof, not the word. -/
def WordReducer.normalize {dimension : Nat} {system : OmegacERewriteRule dimension → Prop}
    (reducer : WordReducer system) (word : OmegacEWord dimension)
    (accessible : Acc (fun reduct source => OmegacEWord.RewritesOneStep system source reduct) word) :
    OmegacEWord dimension :=
  Acc.rec
    (motive := fun _currentWord _acc => OmegacEWord dimension)
    (fun currentWord _accStep normalizeRec =>
      match hReduce : reducer.reduceOnce currentWord with
      | none => currentWord
      | some reduct => normalizeRec reduct (reducer.reduceOnce_sound hReduce))
    accessible

/-- One-step unfolding of `normalize` at an `Acc.intro` witness (the `rfl` proof handle for the correctness
theorems). -/
theorem WordReducer.normalize_unfold {dimension : Nat} {system : OmegacERewriteRule dimension → Prop}
    (reducer : WordReducer system) (word : OmegacEWord dimension)
    (accStep : ∀ later,
      (fun reduct source => OmegacEWord.RewritesOneStep system source reduct) later word →
        Acc (fun reduct source => OmegacEWord.RewritesOneStep system source reduct) later) :
    reducer.normalize word (Acc.intro word accStep) =
      (match hReduce : reducer.reduceOnce word with
        | none => word
        | some reduct =>
            reducer.normalize reduct (accStep reduct (reducer.reduceOnce_sound hReduce))) := rfl

/-- **The normalizer reaches its output by a reduction chain.**  By `Acc`-induction: a halted step is the
reflexive chain; a fired step prepends `reduceOnce_sound` to the inductive chain. -/
theorem WordReducer.normalize_reaches {dimension : Nat} {system : OmegacERewriteRule dimension → Prop}
    (reducer : WordReducer system) (word : OmegacEWord dimension)
    (accessible : Acc (fun reduct source => OmegacEWord.RewritesOneStep system source reduct) word) :
    OmegacEWord.RewritesMany system word (reducer.normalize word accessible) := by
  induction accessible with
  | intro currentWord accStep ih =>
      rw [reducer.normalize_unfold currentWord accStep]
      split
      · exact OmegacEWord.RewritesMany.refl _
      · next reduct hReduce =>
          exact OmegacEWord.RewritesMany.step (reducer.reduceOnce_sound hReduce)
            (ih reduct (reducer.reduceOnce_sound hReduce))

/-- **The normalizer's output admits no one-step rewrite.**  By `Acc`-induction: a halted step gives a normal
form by `reduceOnce_complete`; a fired step defers to the inductive hypothesis. -/
theorem WordReducer.normalize_blocksStep {dimension : Nat} {system : OmegacERewriteRule dimension → Prop}
    (reducer : WordReducer system) (word : OmegacEWord dimension)
    (accessible : Acc (fun reduct source => OmegacEWord.RewritesOneStep system source reduct) word) :
    ∀ reduct, ¬ OmegacEWord.RewritesOneStep system (reducer.normalize word accessible) reduct := by
  induction accessible with
  | intro currentWord accStep ih =>
      rw [reducer.normalize_unfold currentWord accStep]
      split
      · next hNone => exact reducer.reduceOnce_complete hNone
      · next reduct hReduce => exact ih reduct (reducer.reduceOnce_sound hReduce)

/-- **A terminating system with a sound+complete reducer has a normalizer** — the word analog of the
term-layer `RawTerm.normalize`, drives `reduceOnce` along the termination accessibility. -/
def WordReducer.toNormalizer {dimension : Nat} {system : OmegacERewriteRule dimension → Prop}
    (reducer : WordReducer system) (terminating : IsTerminating system) :
    WordNormalizer system where
  normalize := fun word => reducer.normalize word (terminating word)
  reaches := fun word => reducer.normalize_reaches word (terminating word)
  blocksStep := fun word reduct => reducer.normalize_blocksStep word (terminating word) reduct

/-- **The convergent-presentation decidability** (capstone): local confluence + termination + a searchable
reducer ⟹ the word problem is decidable.  Composes `newman` (local confluence + termination ⟹ confluence),
`toNormalizer` (termination + reducer ⟹ normalizer), and `decidableOfNormalizer` (confluence + normalizer ⟹
decision).  Every hypothesis is checkable for a concrete system — the Makkai word problem fully reduced to the
standard convergent-rewriting obligations. -/
def decidableConvertibleModulo_ofConvergent {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (localConfluence : HasLocalConfluence system) (terminating : IsTerminating system)
    (reducer : WordReducer system)
    (firstWord secondWord : OmegacEWord dimension) :
    Decidable (OmegacEWord.ConvertibleModulo system firstWord secondWord) :=
  OmegacEWord.ConvertibleModulo.decidableOfNormalizer
    (newman localConfluence terminating) (reducer.toNormalizer terminating) firstWord secondWord

end FX1Poly.OmegacE
