/-! # Axis/Term — copattern coverage checking (term-15)

The DUAL of `term-11` (pattern unification).  Where a PATTERN destructures inductive data on the left (match
on constructors), a COPATTERN specifies a coinductive value by its OBSERVATIONS — its projections /
destructors (Abel-Pientka-Thibodeau-Setzer, POPL 2013): a stream is defined by its `.head` and `.tail`
copatterns, a function by `.apply x`.  COVERAGE CHECKING is the dual of pattern-match exhaustiveness: a set
of copattern clauses COVERS iff every legal observation context is handled by exactly one clause (no gap, no
overlap) — completeness of the observation tree.

This file ships the genuine core (each zero-axiom):

  * **`CopatternTrie`** — the copattern decision structure (dual of a pattern decision tree): a `clause`
    leaf (a body covering all deeper observations), an exhaustive `split` over the destructors
    (`Fin destructorCount → trie`), or `undefined` — a coverage GAP.
  * **`CopatternTrie.isCovering`** — the decidable COVERAGE CHECKER (`Bool`): no `undefined` is reachable,
    every split exhaustive (`allCovering` over `Fin destructorCount`, via the bounded structural fold
    `allCoveringBelow` + soundness `allCovering_sound`).
  * **`covering_resolves_without_gap`** — ★ completeness: a covering trie resolves EVERY observation path
    without hitting a gap (`resolve path ≠ hitGap`).  The dual of "an exhaustive match never gets stuck."
  * **`DependentCoveringTree`** — coverage WITH DEPENDENT INDICES: a covering tree where the available
    observations and their count depend on the current index (`Fin (destructorsAt index)`, and observing
    moves to `nextIndex index observation`).  Splits are exhaustive over the index-valid observations, so
    coverage is structural; `resolveDependent` never gaps (there is no `undefined` constructor).

## Honest scope

The coverage CHECKER (uniform trie + decidable `isCovering` + completeness) + the dependent covering-tree
structure (index-dependent exhaustiveness, covered by construction).  DEFERRED: the full Abel-Pientka
coverage ALGORITHM that BUILDS the splitting tree from clauses WITH dependent index UNIFICATION (refining the
index at each split, pruning impossible observations); the productivity/totality semantics tying a covering
definition to a defined codata value (`term-14`'s `corec`/`corec_unique` is the uniform-stream instance).

## Zero-axiom verification

`allCoveringBelow` is a bounded structural `Bool` fold (no `decide`, no `Fin.cases`); its soundness and the
completeness theorem are inductions with `Nat`/`Fin` order lemmas and `Bool` case analysis (no
`Bool.and_eq_true` propext leak — `cases` on the `Bool` value); the dependent tree uses `Fin`-indexed
children.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditAxisTermCopatternCoverage.lean`.
-/

namespace FX1Poly.Core

/-! ## The copattern trie + the coverage checker -/

/-- A **copattern decision trie** over `destructorCount` observations: a `clause` body (covering all deeper
observations from here), an exhaustive `split` dispatching on the next observation, or `undefined` — a
COVERAGE GAP (an observation context no clause handles). -/
inductive CopatternTrie (destructorCount : Nat) where
  | undefined : CopatternTrie destructorCount
  | clause : CopatternTrie destructorCount
  | split : (Fin destructorCount → CopatternTrie destructorCount) → CopatternTrie destructorCount

/-- Bounded structural check that a predicate holds at every observation below `bound`. -/
def CopatternTrie.allCoveringBelow {destructorCount : Nat} (predicate : Fin destructorCount → Bool) :
    (bound : Nat) → bound ≤ destructorCount → Bool
  | 0, _ => true
  | priorBound + 1, hbound =>
      predicate ⟨priorBound, Nat.lt_of_lt_of_le (Nat.lt_succ_self priorBound) hbound⟩
        && CopatternTrie.allCoveringBelow predicate priorBound (Nat.le_of_succ_le hbound)

/-- A predicate holds at EVERY observation. -/
def CopatternTrie.allCovering {destructorCount : Nat} (predicate : Fin destructorCount → Bool) : Bool :=
  CopatternTrie.allCoveringBelow predicate destructorCount (Nat.le_refl destructorCount)

/-- Soundness of the bounded fold: if it returns `true`, the predicate holds at every observation below the
bound. -/
theorem CopatternTrie.allCoveringBelow_sound {destructorCount : Nat} (predicate : Fin destructorCount → Bool) :
    ∀ (bound : Nat) (hbound : bound ≤ destructorCount),
      CopatternTrie.allCoveringBelow predicate bound hbound = true →
      ∀ (index : Fin destructorCount), index.val < bound → predicate index = true := by
  intro bound
  induction bound with
  | zero => intro _ _ index indexBelowZero; exact absurd indexBelowZero (Nat.not_lt_zero index.val)
  | succ priorBound inductionHypothesis =>
      intro hbound allTrue index indexBelowSucc
      simp only [CopatternTrie.allCoveringBelow] at allTrue
      cases hHead : predicate ⟨priorBound, Nat.lt_of_lt_of_le (Nat.lt_succ_self priorBound) hbound⟩ with
      | false => rw [hHead] at allTrue; nomatch allTrue
      | true =>
          rw [hHead] at allTrue
          by_cases hIndexAtTop : index.val = priorBound
          · have indexIsTop : index =
                ⟨priorBound, Nat.lt_of_lt_of_le (Nat.lt_succ_self priorBound) hbound⟩ :=
              Fin.eq_of_val_eq hIndexAtTop
            rw [indexIsTop]; exact hHead
          · exact inductionHypothesis (Nat.le_of_succ_le hbound) allTrue index
              (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ indexBelowSucc) hIndexAtTop)

/-- If the full fold returns `true`, the predicate holds at every observation. -/
theorem CopatternTrie.allCovering_sound {destructorCount : Nat} (predicate : Fin destructorCount → Bool)
    (allTrue : CopatternTrie.allCovering predicate = true) (index : Fin destructorCount) :
    predicate index = true :=
  CopatternTrie.allCoveringBelow_sound predicate destructorCount (Nat.le_refl destructorCount) allTrue
    index index.isLt

/-- ★ **The coverage CHECKER** (`Bool`, hence decidable): a trie covers iff it has no reachable `undefined`
gap — every `split` exhaustive over all observations, bottoming out in `clause` leaves. -/
def CopatternTrie.isCovering {destructorCount : Nat} : CopatternTrie destructorCount → Bool
  | .undefined => false
  | .clause => true
  | .split subtries => CopatternTrie.allCovering (fun observation => (subtries observation).isCovering)

/-- The outcome of resolving an observation path against a trie. -/
inductive CoverageResult where
  | reachedClause : CoverageResult
  | stillObserving : CoverageResult
  | hitGap : CoverageResult

/-- Resolve an observation path against a trie: reach a `clause` (covered), run out of observations at a
`split` (still observable — fine for codata), or hit an `undefined` GAP. -/
def CopatternTrie.resolve {destructorCount : Nat} :
    CopatternTrie destructorCount → List (Fin destructorCount) → CoverageResult
  | .undefined, _ => CoverageResult.hitGap
  | .clause, _ => CoverageResult.reachedClause
  | .split _, [] => CoverageResult.stillObserving
  | .split subtries, observation :: rest => (subtries observation).resolve rest

/-- ★ **Coverage completeness** — a covering trie never leaves an observation stuck: every observation path
resolves to a clause or stays inside the tree, never hitting a gap.  The dual of "an exhaustive pattern
match is never stuck." -/
theorem covering_resolves_without_gap {destructorCount : Nat} (trie : CopatternTrie destructorCount) :
    trie.isCovering = true →
      ∀ (path : List (Fin destructorCount)), trie.resolve path ≠ CoverageResult.hitGap := by
  induction trie with
  | undefined => intro covering _; simp only [CopatternTrie.isCovering] at covering; nomatch covering
  | clause => intro _ _ resolvesToGap; nomatch resolvesToGap
  | split subtries subtriesInductionHypothesis =>
      intro covering path
      cases path with
      | nil => intro resolvesToGap; nomatch resolvesToGap
      | cons observation rest =>
          have observationCovering : (subtries observation).isCovering = true :=
            CopatternTrie.allCovering_sound (fun obs => (subtries obs).isCovering) covering observation
          exact subtriesInductionHypothesis observation observationCovering rest

/-! ## Coverage with dependent indices -/

/-- A **dependent covering tree**: a covering tree where the available observations depend on the current
index — at `index` one may observe `Fin (destructorsAt index)`, and observing `obs` moves to
`nextIndex index obs`.  A `split` is exhaustive over the index-valid observations, so coverage is structural
(there is no `undefined` constructor — a dependent covering tree has no gaps). -/
inductive DependentCoveringTree (Index : Type) (destructorsAt : Index → Nat)
    (nextIndex : (index : Index) → Fin (destructorsAt index) → Index) : Index → Type where
  | leaf (index : Index) : DependentCoveringTree Index destructorsAt nextIndex index
  | split (index : Index)
      (subtrees : (observation : Fin (destructorsAt index)) →
        DependentCoveringTree Index destructorsAt nextIndex (nextIndex index observation)) :
      DependentCoveringTree Index destructorsAt nextIndex index

/-- An index-respecting observation path: each step observes an index-valid destructor and advances the
index. -/
inductive DependentObservation (Index : Type) (destructorsAt : Index → Nat)
    (nextIndex : (index : Index) → Fin (destructorsAt index) → Index) : Index → Type where
  | stop (index : Index) : DependentObservation Index destructorsAt nextIndex index
  | step (index : Index) (observation : Fin (destructorsAt index))
      (rest : DependentObservation Index destructorsAt nextIndex (nextIndex index observation)) :
      DependentObservation Index destructorsAt nextIndex index

/-- Resolve a dependent observation against a dependent covering tree — does it reach a leaf?  By
construction it NEVER gaps (no `undefined` constructor); structural recursion on the observation. -/
def DependentCoveringTree.resolveDependent {Index : Type} {destructorsAt : Index → Nat}
    {nextIndex : (index : Index) → Fin (destructorsAt index) → Index} :
    {index : Index} → DependentCoveringTree Index destructorsAt nextIndex index →
      DependentObservation Index destructorsAt nextIndex index → Bool
  | _, .leaf _, _ => true
  | _, .split _ _, .stop _ => false
  | _, .split _ subtrees, .step _ observation rest => (subtrees observation).resolveDependent rest

/-- ★ **Dependent coverage is structural**: every dependent covering tree is a `leaf` or an EXHAUSTIVE
`split` — there is no gap constructor, so coverage over the index-dependent observations is by construction.
This is the dual of dependent-pattern coverage: the index determines which observations must be covered. -/
theorem dependentCoverage_leafOrExhaustiveSplit {Index : Type} {destructorsAt : Index → Nat}
    {nextIndex : (index : Index) → Fin (destructorsAt index) → Index} {index : Index}
    (tree : DependentCoveringTree Index destructorsAt nextIndex index) :
    (tree = DependentCoveringTree.leaf index)
      ∨ (∃ subtrees, tree = DependentCoveringTree.split index subtrees) := by
  cases tree with
  | leaf _ => exact Or.inl rfl
  | split _ subtrees => exact Or.inr ⟨subtrees, rfl⟩

/-! ## Concrete witnesses -/

/-- The STREAM covering trie (2 observations — `head` and `tail`): both lead to clauses, so it covers. -/
def streamCoveringTrie : CopatternTrie 2 :=
  CopatternTrie.split (fun _observation => CopatternTrie.clause)

/-- The stream trie covers (the coverage checker accepts it). -/
theorem streamCoveringTrie_isCovering : streamCoveringTrie.isCovering = true := rfl

/-- An INCOMPLETE stream definition — only `head` (observation `0`) handled, `tail` (observation `1`) left
`undefined` — is rejected by the checker. -/
def incompleteStreamTrie : CopatternTrie 2 :=
  CopatternTrie.split (fun observation =>
    match observation with
    | ⟨0, _⟩ => CopatternTrie.clause
    | ⟨_ + 1, _⟩ => CopatternTrie.undefined)

/-- The incomplete trie is rejected — coverage checking catches the missing `tail` clause. -/
theorem incompleteStreamTrie_notCovering : incompleteStreamTrie.isCovering = false := rfl

end FX1Poly.Core
