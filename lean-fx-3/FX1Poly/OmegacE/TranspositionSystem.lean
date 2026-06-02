import FX1Poly.OmegacE.Rewrite

/-! # FX1Poly/OmegacE/TranspositionSystem
    — the first CONCRETE LENGTH-PRESERVING presentation: the adjacent-transposition rule `[a,b] → [b,a]`

`IdempotentSystem.lean` shipped the first concrete genuinely-rewriting system — but a LENGTH-REDUCING one
(`[c,c] → [c]`), whose termination is the easy length-measure shortcut (`IsTerminating_of_lengthReducing`).
This file opens the complementary class: a LENGTH-PRESERVING system, the simplest convergent class for which
length is NOT a termination measure (`Rewrite.lean`'s `IsLengthPreservingSystem` docstring: "bounded search
over equal-length words decides such a system's word problem").  The atom is the single adjacent-transposition
rule `[a,b] → [b,a]` on the scaffold words of two fixed cells — the generator of an adjacent-sorting
(bubble-sort) presentation.

* `transpositionRule a b` — the rule `[a,b] → [b,a]` (the two sides are permutations of each other, so
  equal length).
* `transpositionSystem a b` — the single-rule system `{ [a,b] → [b,a] }` (predicate `· = transpositionRule a b`).
* `transpositionRule_fires` — the **non-vacuity witness**: the system genuinely rewrites `[a,b] → [b,a]`
  (`RewritesOneStep.fire`, membership `rfl`).
* `transpositionSystem_isLengthPreserving` — the headline: every rule has `|lhs| = |rhs| = 2`
  (`IsLengthPreservingSystem`), the length-PRESERVING analogue of the idempotent system's length-REDUCING
  certificate.  This is exactly the hypothesis the shipped length-invariance lemmas consume.
* `transpositionSystem_rewritesOneStep_length_preserved` / `…_rewritesMany_length_preserved` /
  `…_convertibleModulo_length_preserved` — length is invariant under one-step, many-step, and full
  convertibility for this system (instantiating the shipped `RewritesOneStep.length_preserved` /
  `RewritesMany.length_preserved` / `ConvertibleModulo.length_preserved`).  The convertibility invariant is
  the key structural fact making the word problem BOUNDED-SEARCH decidable: every word convertible to `w`
  lies in the FINITE set of words of length `|w|`, so reachability is a finite BFS.

## Honest scope

This ships the length-PRESERVING SYSTEM + its length invariants + non-vacuity, NOT yet termination,
confluence, or the decision.  The three deferred subsequent atoms:

  1. TERMINATION (via an INVERSION measure, NOT length): under the hypothesis `a ≠ b`, the rule strictly
     decreases the count of `a`-before-`b` adjacencies/inversions, a well-founded `Nat` measure — the genuine
     non-length termination certificate (the analogue of `IsTerminating_of_lengthReducing` for the
     length-preserving class).  Distinctness `a ≠ b` is REQUIRED: with `a = b` the rule is `[a,a] → [a,a]`, a
     self-loop, so the system is NOT terminating.
  2. LOCAL CONFLUENCE (orthogonality): the single rule `[a,b]` cannot overlap itself — an overlap at position
     `i, i+1` would need `w[i] = a ∧ w[i+1] = b` and `w[i+1] = a ∧ w[i+2] = b`, forcing `a = b`; so for
     `a ≠ b` there are NO critical pairs and divergences are disjoint (commuting) redexes, joinable by the
     context congruences.  With `newman` (local confluence + termination ⟹ confluence) this completes the
     convergent presentation.
  3. BOUNDED-SEARCH DECIDABILITY: with convergence, `decidableConvertibleModulo_ofConvergent` (or the
     finite same-length BFS the length invariant here underwrites) decides the word problem.

The richer FAMILY version — the full adjacent-sorting system `{ [a,b] → [b,a] : slotValue a > slotValue b }`,
which DOES have genuine critical pairs (the `[a,b,c]` overlap, resolved by joining to the sorted word, a real
`newman` application) — is the natural follow-up; this single-rule atom is the orthogonal base case.

## Zero-axiom verification

`transpositionRule_fires` is the bare `fire` constructor (`rfl` membership); `isLengthPreserving` is `subst`
+ `rfl` (both sides are length-2 lists, `|[a,b]| = 2 = |[b,a]|` definitionally); the three invariants
directly instantiate the shipped length-preservation lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega` (verified by `#print axioms` in scratch before landing).
Per-declaration gated in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- The **adjacent-transposition rule** `[a,b] → [b,a]` on the scaffold words of two fixed cells — the
generator of an adjacent-sorting presentation.  The two sides are permutations, hence equal length: the
simplest genuinely length-PRESERVING rewrite (contrast the length-REDUCING idempotent rule `[c,c] → [c]`). -/
def transpositionRule {dimension : Nat} (firstCell secondCell : OmegacECell dimension) :
    OmegacERewriteRule dimension where
  leftHandSide := { cells := [firstCell, secondCell] }
  rightHandSide := { cells := [secondCell, firstCell] }

/-- The **single-rule transposition system** `{ [a,b] → [b,a] }`, as the membership predicate
`· = transpositionRule a b`. -/
def transpositionSystem {dimension : Nat} (firstCell secondCell : OmegacECell dimension) :
    OmegacERewriteRule dimension → Prop :=
  fun rule => rule = transpositionRule firstCell secondCell

/-- **The transposition system genuinely rewrites**: `[a,b] → [b,a]` is a one-step rewrite (`fire` of the
rule, membership `rfl`).  The non-vacuity witness for the length-preserving class. -/
theorem transpositionRule_fires {dimension : Nat} (firstCell secondCell : OmegacECell dimension) :
    OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell)
      { cells := [firstCell, secondCell] } { cells := [secondCell, firstCell] } :=
  OmegacEWord.RewritesOneStep.fire (transpositionRule firstCell secondCell) rfl

/-- **The transposition system is length-preserving**: its one rule has `|[a,b]| = 2 = |[b,a]|`.  The
length-PRESERVING certificate (the headline; the complement of the idempotent system's length-REDUCING
certificate), and the hypothesis the length-invariance lemmas consume. -/
theorem transpositionSystem_isLengthPreserving {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) :
    IsLengthPreservingSystem (transpositionSystem firstCell secondCell) := by
  intro rule isInSystem
  have ruleEq : rule = transpositionRule firstCell secondCell := isInSystem
  subst ruleEq
  rfl

/-- **One-step rewriting preserves length** for the transposition system (instantiating the shipped
`RewritesOneStep.length_preserved` at the length-preserving certificate). -/
theorem transpositionSystem_rewritesOneStep_length_preserved {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell)
      sourceWord targetWord) :
    sourceWord.length = targetWord.length :=
  step.length_preserved (transpositionSystem_isLengthPreserving firstCell secondCell)

/-- **Many-step rewriting preserves length** for the transposition system.  Hence the whole reduction graph
of a word `w` stays within the finite set of words of length `|w|` — the structural fact underwriting
bounded-search decidability of this length-preserving system's word problem. -/
theorem transpositionSystem_rewritesMany_length_preserved {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (many : OmegacEWord.RewritesMany (transpositionSystem firstCell secondCell)
      sourceWord targetWord) :
    sourceWord.length = targetWord.length :=
  many.length_preserved (transpositionSystem_isLengthPreserving firstCell secondCell)

/-- **Convertibility preserves length** for the transposition system: any two words convertible modulo the
system have the same length, so the convertibility class of `w` is a subset of the FINITE same-length word
set — the decision problem is a bounded search. -/
theorem transpositionSystem_convertibleModulo_length_preserved {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (conv : OmegacEWord.ConvertibleModulo (transpositionSystem firstCell secondCell)
      sourceWord targetWord) :
    sourceWord.length = targetWord.length :=
  conv.length_preserved (transpositionSystem_isLengthPreserving firstCell secondCell)

end FX1Poly.OmegacE
