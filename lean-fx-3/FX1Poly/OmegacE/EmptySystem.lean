import FX1Poly.OmegacE.WordProblem

/-! # FX1Poly/OmegacE/EmptySystem
    — the first CONCRETE convergent presentation: the empty (free-monoid) rule system

`WordProblem.lean` decided convertibility CONDITIONALLY on `HasConfluence` + a `WordNormalizer`.  This file
discharges BOTH hypotheses for the simplest concrete system — the EMPTY rule set (no relations), i.e. the free
monoid presentation — validating that the abstract dim-2 machinery is non-vacuous and runs end-to-end.

* `emptyRewriteSystem` — no rules (`fun _ => False`).
* `rewritesOneStep_emptySystem_absurd` — no word rewrites (the `fire` premise is `False`; congruence cases
  recurse to it).
* `emptyWordNormalizer` — the identity normalizer (every word is already normal).
* `emptyHasConfluence` — vacuous confluence (every reduction is `refl`, so any two reducts coincide).
* `convertibleModulo_emptySystem_iff_eq` — the payoff: the empty presentation's word problem is exactly
  SYNTACTIC EQUALITY (`ConvertibleModulo (emptyRewriteSystem _) w1 w2 ↔ w1 = w2`), via the abstract
  `ConvertibleModulo.iff_normalize_eq` with the identity normalizer (the normal-form comparison is defeq to
  word equality).  Reconnects dim-2 (convertibility) to dim-1 (free-monoid equality, `Word.lean`'s derived
  `DecidableEq`).
* `decidableConvertibleModulo_emptySystem` — its decidability, via the convergent-presentation decision.

This is the dim-2 analog of the closed-SN smoke corpus: a concrete instance proving the abstract theory holds
of something real.  The next concrete Path-B atom is a NON-trivial system (e.g. a length-reducing rule set
with a terminating normalizer via well-founded recursion + a real confluence proof).

## Zero-axiom verification

The hypotheses are discharged structurally (`rewritesMany_eq_of_blocksStep` + the no-rewrite absurdity); the
word-problem characterization reuses the abstract `iff_normalize_eq`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- The **empty rule system**: no rewrite rules — the free-monoid presentation (generators, no relations). -/
def emptyRewriteSystem (dimension : Nat) : OmegacERewriteRule dimension → Prop :=
  fun _rule => False

/-- **No word rewrites under the empty system.**  The `fire` premise is the system membership, which is
`False`; the congruence cases recurse to the inner step's absurdity. -/
theorem rewritesOneStep_emptySystem_absurd {dimension : Nat}
    {firstWord secondWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (emptyRewriteSystem dimension) firstWord secondWord) :
    False := by
  induction step with
  | fire _rule isInSystem => exact isInSystem
  | underLeftContext _prefixWord _inner innerIH => exact innerIH
  | underRightContext _suffixWord _inner innerIH => exact innerIH

/-- **The identity normalizer for the empty system** — every word is already a normal form. -/
def emptyWordNormalizer (dimension : Nat) : WordNormalizer (emptyRewriteSystem dimension) where
  normalize := fun word => word
  reaches := fun word => OmegacEWord.RewritesMany.refl word
  blocksStep := fun _word _reduct step => rewritesOneStep_emptySystem_absurd step

/-- **The empty system is confluent** (vacuously): no word reduces anywhere but to itself, so any two reducts
of a common source coincide and are trivially joinable. -/
def emptyHasConfluence (dimension : Nat) : HasConfluence (emptyRewriteSystem dimension) := by
  intro sourceWord firstReduct secondReduct sourceToFirst sourceToSecond
  have firstEq : sourceWord = firstReduct :=
    OmegacEWord.rewritesMany_eq_of_blocksStep
      (fun _reduct step => rewritesOneStep_emptySystem_absurd step) sourceToFirst
  have secondEq : sourceWord = secondReduct :=
    OmegacEWord.rewritesMany_eq_of_blocksStep
      (fun _reduct step => rewritesOneStep_emptySystem_absurd step) sourceToSecond
  have reductsEq : firstReduct = secondReduct := firstEq.symm.trans secondEq
  rw [← reductsEq]
  exact OmegacEWord.Joinable.refl firstReduct

/-- **The empty presentation's word problem is syntactic equality.**  Convertibility modulo no rules is just
word equality — the first concrete word-problem characterization, validating the abstract chain
(`ConvertibleModulo.iff_normalize_eq`) on a real system; the identity normalizer makes the normal-form
comparison defeq to word equality.  Reconnects dim-2 convertibility to dim-1 free-monoid equality. -/
theorem convertibleModulo_emptySystem_iff_eq {dimension : Nat}
    {firstWord secondWord : OmegacEWord dimension} :
    OmegacEWord.ConvertibleModulo (emptyRewriteSystem dimension) firstWord secondWord ↔
      firstWord = secondWord :=
  OmegacEWord.ConvertibleModulo.iff_normalize_eq (emptyHasConfluence dimension)
    (emptyWordNormalizer dimension)

/-- **The empty presentation's word problem is decidable** — via the convergent-presentation decision applied
to the discharged confluence + identity normalizer. -/
def decidableConvertibleModulo_emptySystem {dimension : Nat}
    (firstWord secondWord : OmegacEWord dimension) :
    Decidable (OmegacEWord.ConvertibleModulo (emptyRewriteSystem dimension) firstWord secondWord) :=
  OmegacEWord.ConvertibleModulo.decidableOfNormalizer (emptyHasConfluence dimension)
    (emptyWordNormalizer dimension) firstWord secondWord

end FX1Poly.OmegacE
