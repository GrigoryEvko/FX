import FX1Poly.OmegacE.Confluence

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

/-! ## Termination measure: the inversion count

The transposition system is length-PRESERVING, so length is NOT a termination measure.  The correct measure
is the INVERSION COUNT: the number of `(firstCell-before-secondCell)` ordered pairs.  A swap `[a,b] → [b,a]`
removes exactly one such inversion (the adjacent `a` moves right past the `b`; relative to every other cell
both keep their order), so the count strictly decreases by one — a well-founded `ℕ` measure (the genuine
non-length termination certificate, the analogue of `IsTerminating_of_lengthReducing` for this class).

This subsection ships the MEASURE + its append-homomorphism, then the full termination chain:
`countOccurrences_preserved_by_step` (a rewrite preserves the cell multiset) →
`aBeforeBInversions_decreases` (a swap strictly decreases the inversion count — `a ≠ b` in the `fire` case,
count-preservation + the append homomorphism in the context cases) → `transpositionSystem_isTerminating` (via
`Subrelation` into `InvImage (· < ·) measure`, mirroring `IsTerminating_of_lengthReducing`).  TERMINATION is
thus complete — the genuine non-length certificate for the length-preserving class.  Remaining SN-118 atoms:
orthogonal local confluence (no self-overlap ⟹ `newman`) + bounded-search decidability.

REUSABLE ZERO-AXIOM FINDING: `Nat.add_mul` leaks `propext` (verified by `#print axioms`); use
`Nat.add_comm 1 d` + `Nat.succ_mul` to distribute `(1 + d) * b` instead.  `ac_rfl` leaks `propext + Quot.sound`;
do the additive AC by explicit `Nat.add_assoc` / `Nat.add_left_comm` rewrites to a canonical form. -/

/-- Count the occurrences of a fixed `target` cell in a word's cell list. -/
def countOccurrences {dimension : Nat} (target : OmegacECell dimension) :
    List (OmegacECell dimension) → Nat
  | [] => 0
  | head :: tail => (if head = target then 1 else 0) + countOccurrences target tail

/-- The inversion measure: the number of ordered `(firstCell-before-secondCell)` pairs in a cell list — the
positions `i < j` with cell `i = firstCell` and cell `j = secondCell` (counted via `countOccurrences` of
`secondCell` in each suffix following a `firstCell`).  Strictly decreased by every `[a,b] → [b,a]` swap. -/
def aBeforeBInversions {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) :
    List (OmegacECell dimension) → Nat
  | [] => 0
  | head :: tail =>
      (if head = firstCell then countOccurrences secondCell tail else 0)
        + aBeforeBInversions firstCell secondCell tail

/-- `countOccurrences` is a monoid homomorphism from list append to `ℕ` addition. -/
theorem countOccurrences_append {dimension : Nat} (target : OmegacECell dimension)
    (leftCells rightCells : List (OmegacECell dimension)) :
    countOccurrences target (leftCells ++ rightCells)
      = countOccurrences target leftCells + countOccurrences target rightCells := by
  induction leftCells with
  | nil =>
      show countOccurrences target rightCells = 0 + countOccurrences target rightCells
      rw [Nat.zero_add]
  | cons head tail ih =>
      show (if head = target then 1 else 0) + countOccurrences target (tail ++ rightCells)
        = ((if head = target then 1 else 0) + countOccurrences target tail)
          + countOccurrences target rightCells
      rw [ih, Nat.add_assoc]

/-- **Inversion count over an append**: the inversions of `left ++ right` are the inversions within `left`,
plus the inversions within `right`, plus the CROSS inversions (each `firstCell` in `left` pairs with each
`secondCell` in `right`) — the count-product `countOccurrences firstCell left * countOccurrences secondCell
right`.  The key structural law behind the strict-decrease proof's context cases (a rewrite inside a context
preserves the cross term, since it preserves the cell multiset, leaving only the inner measure to decrease). -/
theorem aBeforeBInversions_append {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension)
    (leftCells rightCells : List (OmegacECell dimension)) :
    aBeforeBInversions firstCell secondCell (leftCells ++ rightCells)
      = aBeforeBInversions firstCell secondCell leftCells
        + countOccurrences firstCell leftCells * countOccurrences secondCell rightCells
        + aBeforeBInversions firstCell secondCell rightCells := by
  induction leftCells with
  | nil =>
      show aBeforeBInversions firstCell secondCell rightCells
        = 0 + 0 * countOccurrences secondCell rightCells
          + aBeforeBInversions firstCell secondCell rightCells
      rw [Nat.zero_mul, Nat.add_zero, Nat.zero_add]
  | cons head tail ih =>
      show (if head = firstCell then countOccurrences secondCell (tail ++ rightCells) else 0)
          + aBeforeBInversions firstCell secondCell (tail ++ rightCells)
        = ((if head = firstCell then countOccurrences secondCell tail else 0)
            + aBeforeBInversions firstCell secondCell tail)
          + ((if head = firstCell then 1 else 0) + countOccurrences firstCell tail)
            * countOccurrences secondCell rightCells
          + aBeforeBInversions firstCell secondCell rightCells
      rw [countOccurrences_append, ih]
      by_cases headIsFirst : head = firstCell
      · rw [if_pos headIsFirst, if_pos headIsFirst, if_pos headIsFirst,
          Nat.add_comm 1 (countOccurrences firstCell tail), Nat.succ_mul]
        generalize countOccurrences secondCell rightCells = termB
        generalize countOccurrences secondCell tail = termA
        generalize aBeforeBInversions firstCell secondCell tail = termC
        generalize aBeforeBInversions firstCell secondCell rightCells = termE
        generalize countOccurrences firstCell tail * termB = termP
        rw [Nat.add_comm termP termB,
            Nat.add_assoc termA termB ((termC + termP) + termE),
            Nat.add_assoc termC termP termE,
            Nat.add_assoc (termA + termC) (termB + termP) termE,
            Nat.add_assoc termA termC ((termB + termP) + termE),
            Nat.add_assoc termB termP termE,
            Nat.add_left_comm termC termB (termP + termE)]
      · rw [if_neg headIsFirst, if_neg headIsFirst, if_neg headIsFirst,
          Nat.zero_add, Nat.zero_add, Nat.zero_add]

/-- **A rewrite preserves the cell multiset**: a transposition step leaves every cell's occurrence count
unchanged.  `fire` swaps `[a,b] ↦ [b,a]` (same two cells, equal counts by `add_comm`); context cases add
`countOccurrences_append` to the inner IH.  This makes the inversion-measure cross terms invariant under a
rewrite-in-context — the bridge between the append homomorphism and the strict decrease. -/
theorem countOccurrences_preserved_by_step {dimension : Nat}
    (firstCell secondCell probe : OmegacECell dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell)
      sourceWord targetWord) :
    countOccurrences probe sourceWord.cells = countOccurrences probe targetWord.cells := by
  induction step with
  | fire rule isInSystem =>
      have ruleEq : rule = transpositionRule firstCell secondCell := isInSystem
      subst ruleEq
      show (if firstCell = probe then 1 else 0) + ((if secondCell = probe then 1 else 0) + 0)
        = (if secondCell = probe then 1 else 0) + ((if firstCell = probe then 1 else 0) + 0)
      rw [Nat.add_zero, Nat.add_zero, Nat.add_comm]
  | underLeftContext prefixWord _inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [countOccurrences_append, countOccurrences_append, innerIH]
  | underRightContext suffixWord _inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [countOccurrences_append, countOccurrences_append, innerIH]

/-- **A transposition step strictly decreases the inversion measure** (requires `firstCell ≠ secondCell`).
`fire` swaps `[a,b] ↦ [b,a]`, removing the one `a`-before-`b` inversion (`measure = 1 ↦ 0`, the `a ≠ b` killing
the spurious `if b = a` branch).  Context cases: the append homomorphism splits the measure, count-preservation
makes the cross terms equal, and the inner IH gives the strict decrease on the rewritten factor, lifted by
`Nat.add_lt_add_left` / `Nat.add_lt_add_right`. -/
theorem aBeforeBInversions_decreases {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension)
    (distinct : firstCell ≠ secondCell)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell)
      sourceWord targetWord) :
    aBeforeBInversions firstCell secondCell targetWord.cells
      < aBeforeBInversions firstCell secondCell sourceWord.cells := by
  have notSF : secondCell = firstCell → False := fun h => distinct h.symm
  induction step with
  | fire rule isInSystem =>
      have ruleEq : rule = transpositionRule firstCell secondCell := isInSystem
      subst ruleEq
      have targetZero : aBeforeBInversions firstCell secondCell [secondCell, firstCell] = 0 := by
        show (if secondCell = firstCell then countOccurrences secondCell [firstCell] else 0)
             + aBeforeBInversions firstCell secondCell [firstCell] = 0
        rw [if_neg notSF, Nat.zero_add]
        show (if firstCell = firstCell then countOccurrences secondCell [] else 0)
             + aBeforeBInversions firstCell secondCell [] = 0
        rw [if_pos rfl]
        rfl
      have sourceOne : aBeforeBInversions firstCell secondCell [firstCell, secondCell] = 1 := by
        show (if firstCell = firstCell then countOccurrences secondCell [secondCell] else 0)
             + aBeforeBInversions firstCell secondCell [secondCell] = 1
        rw [if_pos rfl]
        have countOne : countOccurrences secondCell [secondCell] = 1 := by
          show (if secondCell = secondCell then 1 else 0) + countOccurrences secondCell [] = 1
          rw [if_pos rfl]
          rfl
        have invZero : aBeforeBInversions firstCell secondCell [secondCell] = 0 := by
          show (if secondCell = firstCell then countOccurrences secondCell [] else 0)
               + aBeforeBInversions firstCell secondCell [] = 0
          rw [if_neg notSF]
          rfl
        rw [countOne, invZero]
      show aBeforeBInversions firstCell secondCell [secondCell, firstCell]
        < aBeforeBInversions firstCell secondCell [firstCell, secondCell]
      rw [targetZero, sourceOne]
      exact Nat.zero_lt_one
  | underLeftContext prefixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [aBeforeBInversions_append, aBeforeBInversions_append,
          countOccurrences_preserved_by_step firstCell secondCell secondCell inner]
      exact Nat.add_lt_add_left innerIH _
  | underRightContext suffixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [aBeforeBInversions_append, aBeforeBInversions_append,
          countOccurrences_preserved_by_step firstCell secondCell firstCell inner]
      exact Nat.add_lt_add_right (Nat.add_lt_add_right innerIH _) _

/-- **The transposition system is terminating** (requires `firstCell ≠ secondCell`) — the SN-118 headline.
The inversion measure embeds reduction into `<` on `ℕ` (pulled back along the measure), which is well-founded,
so every word is accessible.  This is the genuine NON-LENGTH termination certificate for the length-preserving
class (the complement of the idempotent system's `IsTerminating_of_lengthReducing`), discharging the
`IsTerminating` premise of `newman` / `decidableConvertibleModulo_ofConvergent` for this system. -/
theorem transpositionSystem_isTerminating {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension)
    (distinct : firstCell ≠ secondCell) :
    IsTerminating (transpositionSystem firstCell secondCell) := by
  intro word
  have subrel :
      Subrelation
        (fun reduct source =>
          OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell) source reduct)
        (InvImage (· < ·)
          (fun candidate => aBeforeBInversions firstCell secondCell candidate.cells)) := by
    intro smaller larger hStep
    exact aBeforeBInversions_decreases firstCell secondCell distinct hStep
  exact subrel.accessible
    ((InvImage.wf (fun candidate => aBeforeBInversions firstCell secondCell candidate.cells)
      Nat.lt_wfRel.wf).apply word)

end FX1Poly.OmegacE
