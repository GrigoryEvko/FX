import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrientedSN

/-! # DefUnivSnResolution — the DEFUNIV-SN (#1412) verdict, machine-checked

A make-or-break spike (#1412) asked whether the definitional-univalence
Id-computation rules need a bespoke `lex(level, size)` type-complexity
strong-normalization measure.  The verdict, pinned here as `rfl`:

  **NO new measure.**  The univalence-shaped rule
  `Id(Type@l) lhs rhs ↝ Equiv lhs rhs` (`univalenceShapedDemoRule`, the
  IOTA-T10 demonstrator) reassembles its reduct ENTIRELY from the
  immediate scrutinee subterms `lhs` / `rhs` and DROPS the `universeCode`
  scrutinee.  Its reduct is therefore strictly SMALLER, not growing — so
  it passes BOTH Tier-2 legs (`isStructurallyRecursive` and
  `hasSubstitutionFreeReduct`) and is `isRpoOrientable`: already
  SN-dominated by the shipped oriented-table machinery (IOTA-T8), with no
  new termination proof.

A `lex(level, size)` measure would have been the WRONG tool regardless:
the universe-classification well-foundedness is itself size-derived
(`subjectSizeLtClassifier`), so a level-then-size product collapses to
size and could not dominate a (hypothetical) term-GROWING rule.  Where a
future def-univ rule genuinely grows its reduct — e.g. by semantically
UNFOLDING `equivCode` into its Σ / `isEquiv` structure — it is built from
the same subterms under a fixed finite former template and is dominated
by the shipped RPO FORMER-PRECEDENCE (SN-117), not a Nat measure; and any
rule escaping both syntactic tiers rides the semantic sconing / STC SN
route (SN-101/110).

So the genuine open def-univ risk is NOT a syntactic SN measure at all —
it is ORTHOGONALITY / CONFLUENCE of the type-directed Id rows with βιη
once they land (DEFUNIV-CONFLUENCE #1422, the `WfIotaTable` crux).  That
is where the def-univ keystone migrates.

Zero-axiom; audit-gated in
`FX1PolyAudit/AuditDefUnivSnResolution.lean`. -/

namespace FX1Poly.Core

/-- The univalence-shaped demo rule reassembles structurally: its
recursive slots are fed only immediate scrutinee-child projections. -/
theorem univalenceShapedDemoRule_isStructurallyRecursive :
    univalenceShapedDemoRule.isStructurallyRecursive = true := rfl

/-- Its reduct template contains no substitution node — substitution-free. -/
theorem univalenceShapedDemoRule_avoidsSubstitution :
    univalenceShapedDemoRule.hasSubstitutionFreeReduct = true := rfl

/-- Hence the univalence-shaped rule is RPO-orientable: it joins the
shipped oriented sub-table and inherits strong normalization with no new
measure — the DEFUNIV-SN (#1412) verdict. -/
theorem univalenceShapedDemoRule_isRpoOrientable :
    univalenceShapedDemoRule.isRpoOrientable = true := rfl

end FX1Poly.Core
