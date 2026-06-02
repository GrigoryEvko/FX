import FX1Poly.OmegacE.Confluence

/-! # FX1Poly/OmegacE/IdempotentSystem
    — the first CONCRETE NON-EMPTY terminating presentation: the idempotent rule `[c,c] → [c]`

`EmptySystem.lean` discharged the convergent-presentation machinery on the EMPTY rule set — a real but
DEGENERATE instance (nothing rewrites, the normalizer is the identity, confluence is vacuous).  Its docstring
names the next concrete atom: "a non-trivial length-reducing system."  This file is that atom's TERMINATION
half — the simplest genuinely-rewriting system: a single idempotence rule `[c,c] → [c]` on the scaffold word
of one fixed cell `c`.  It is the first concrete system that actually FIRES (so the rewriting relation is
non-vacuous) and is proved terminating from the length measure.

* `idempotentRule c` — the rule `[c,c] → [c]` (right-hand side strictly shorter than the left).
* `idempotentSystem c` — the single-rule system `{ [c,c] → [c] }` (as the predicate `· = idempotentRule c`).
* `idempotentRule_fires` — the **non-vacuity witness**: the system genuinely rewrites `[c,c] → [c]`
  (`RewritesOneStep.fire`).  The honest CONTRAST to `rewritesOneStep_emptySystem_absurd`, which proved the
  empty system rewrites NOTHING — together they bracket the spectrum (no rules vs one real rule).
* `idempotentSystem_isLengthReducing` — every rule strictly shortens (`|[c]| = 1 < 2 = |[c,c]|`); the
  termination certificate this concrete system supplies to `IsLengthReducingSystem`.
* `idempotentSystem_isTerminating` — the payoff: the idempotent system is TERMINATING, via the shipped
  `IsTerminating_of_lengthReducing` (length-reducing ⟹ well-founded reduction).  The first NON-trivial
  discharge of `IsTerminating` — validating that the abstract length-measure termination machinery runs on a
  system that actually reduces words.

## Honest scope

This ships TERMINATION + non-vacuity for the idempotent system, NOT yet its decidable word problem.  The full
decision (`decidableConvertibleModulo_ofConvergent`) needs two further inputs this atom defers:

  1. a `WordReducer (idempotentSystem c)` — a decidable rule-matcher `reduceOnce` (scan for an adjacent
     `[c,c]`, splice to `[c]`) with soundness (a hit IS a `RewritesOneStep`) and completeness (a miss means no
     `RewritesOneStep` — the structural inversion of one-step rewriting for this system); combined with the
     termination here, `WordReducer.toNormalizer` yields a real terminating normalizer;
  2. `HasLocalConfluence (idempotentSystem c)` — the critical-pair check.  The only overlap is `[c,c,c]`, and
     BOTH firings (the left pair under right context `[c]`, the right pair under left context `[c]`) reduce to
     `[c,c]`, so the critical pair is joinable AT `[c,c]` by reflexivity; disjoint redexes commute.  With
     `newman` (local confluence + the termination here ⟹ confluence) this completes the convergent
     presentation, and `decidableConvertibleModulo_ofConvergent` decides the word problem.

Those are the next two Path-B atoms; this one is complete in itself (a real non-empty terminating system).

## Zero-axiom verification

`idempotentRule_fires` is the bare `fire` constructor (`rfl` membership); `isLengthReducing` is `subst` +
`Nat.lt_succ_self` (no `omega`); `isTerminating` is the shipped `IsTerminating_of_lengthReducing`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- The **idempotent rule** `[c,c] → [c]` on the scaffold words of one fixed cell `c` — the simplest genuinely
length-reducing rewrite (collapse a doubled cell to a single one). -/
def idempotentRule {dimension : Nat} (cell : OmegacECell dimension) : OmegacERewriteRule dimension where
  leftHandSide := { cells := [cell, cell] }
  rightHandSide := { cells := [cell] }

/-- The **single-rule idempotent system** `{ [c,c] → [c] }`, as the membership predicate `· = idempotentRule c`. -/
def idempotentSystem {dimension : Nat} (cell : OmegacECell dimension) :
    OmegacERewriteRule dimension → Prop :=
  fun rule => rule = idempotentRule cell

/-- **The idempotent system genuinely rewrites**: `[c,c] → [c]` is a one-step rewrite (`fire` of the rule,
whose membership is `rfl`).  The non-vacuity witness — the honest contrast to the empty system's
`rewritesOneStep_emptySystem_absurd` (which rewrites nothing). -/
theorem idempotentRule_fires {dimension : Nat} (cell : OmegacECell dimension) :
    OmegacEWord.RewritesOneStep (idempotentSystem cell)
      { cells := [cell, cell] } { cells := [cell] } :=
  OmegacEWord.RewritesOneStep.fire (idempotentRule cell) rfl

/-- **The idempotent system is length-reducing**: its one rule strictly shortens (`|[c]| = 1 < 2 = |[c,c]|`).
The termination certificate fed to `IsTerminating_of_lengthReducing`. -/
theorem idempotentSystem_isLengthReducing {dimension : Nat} (cell : OmegacECell dimension) :
    IsLengthReducingSystem (idempotentSystem cell) := by
  intro rule isInSystem
  have ruleEq : rule = idempotentRule cell := isInSystem
  subst ruleEq
  exact Nat.lt_succ_self 1

/-- **The idempotent system is terminating** — the first NON-trivial discharge of `IsTerminating` (the empty
system was vacuous).  Length-reducing ⟹ well-founded reduction via the shipped `IsTerminating_of_lengthReducing`. -/
theorem idempotentSystem_isTerminating {dimension : Nat} (cell : OmegacECell dimension) :
    IsTerminating (idempotentSystem cell) :=
  IsTerminating_of_lengthReducing (idempotentSystem_isLengthReducing cell)

end FX1Poly.OmegacE
