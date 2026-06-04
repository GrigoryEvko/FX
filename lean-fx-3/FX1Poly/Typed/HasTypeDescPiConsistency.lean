import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.ReducibilityCandidateArrow

/-! # FX1Poly/Typed/HasTypeDescPiConsistency — RETIRED (table-generic successors live in HasTypeDescPiRootGeneric)

This file used to hold the hard-coded grown/formation root-classification lemmas
`HasTypeDesc.subjectRootGenerator`, `HasTypeDescPi.subjectRootGenerator`, and
`HasTypeDescPi.closedSubjectRootGenerator`.  Each ENUMERATED the formation table (`gen_piTyCode` /
`gen_sigmaTyCode`) in both its statement and its `genFormation`/`genFormationPi` arm — so a new formation row
would make the statement false AND break the `typingRuleDescOf = none`-for-everything-else proof.  That is
the "the metatheory hard-codes the table" trap (polycell.md §2.1/§3.16.19, the cascade-death principle).

They have been **retired** in favour of the table-generic successors in `FX1Poly.Typed.HasTypeDescPiRootGeneric`:

  * `HasTypeDesc.subjectRootGeneratorGeneric` / `HasTypeDescPi.subjectRootGeneratorGeneric` — root is a
    non-former head (`var` / `universeCode` [/ `lam` / `app`]) OR carries a formation rule
    (`∃ rule, typingRuleDescOf root = some rule`), generic over the WHOLE table.
  * `HasTypeDescPi.closedSubjectRootGeneratorGeneric` — the empty-context twin (drops the `gen_var` disjunct).
  * `HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded` — the future-proof untyped-head refutation.

All survive arbitrary formation-table growth.  This file is retained only as a stable import anchor (it
re-exports `HasTypeDescPi` + `ReducibilityCandidateArrow`); its content moved to the generic family.
-/
