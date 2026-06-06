import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.ReducibilityCandidateArrow

/-! # FX1Poly/Typed/HasTypeDescPiConsistency — import anchor (table-generic root-classification lives in HasTypeDescPiRootGeneric)

The table-generic root-classification lemmas live in `FX1Poly.Typed.HasTypeDescPiRootGeneric`:

  * `HasTypeDesc.subjectRootGeneratorGeneric` / `HasTypeDescPi.subjectRootGeneratorGeneric` — root is a
    non-former head (`var` / `universeCode` [/ `lam` / `app`]) OR carries a formation rule
    (`∃ rule, typingRuleDescOf root = some rule`), generic over the WHOLE table.
  * `HasTypeDescPi.closedSubjectRootGeneratorGeneric` — the empty-context twin (drops the `gen_var` disjunct).
  * `HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded` — the future-proof untyped-head refutation.

These survive arbitrary formation-table growth, avoiding the "metatheory hard-codes the table" trap
(polycell.md §2.1/§3.16.19, the cascade-death principle): hard-coded root-classification would enumerate
`gen_piTyCode` / `gen_sigmaTyCode` in both statement and proof, so a new formation row would falsify the
statement and break the `typingRuleDescOf = none`-for-everything-else proof.  This file is a stable import
anchor (it re-exports `HasTypeDescPi` + `ReducibilityCandidateArrow`).
-/
