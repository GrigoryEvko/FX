import LeanFX2.Confluence.RawCd

/-! Phase 6.A zero-axiom audit — raw-side complete development.

`RawTerm.cd` is the workhorse for raw-side confluence.  It must be
zero-axiom because every cd_lemma case eventually case-splits on
the developed scrutinee — if cd's match leaks propext, the cd_lemma
chain inherits.

Per `feedback_lean_zero_axiom_match.md`: full enumeration over a
non-dependent inductive (RawTerm is Nat-indexed) keeps the match
compiler from emitting `propext`.  This file gates the contract. -/

#print axioms LeanFX2.RawTerm.cd
