import LeanFX2.Term.Bridge

/-! Phase 2 zero-axiom audit — Term projection bridge lemmas.

These four `rfl` lemmas demonstrate the architectural payoff of
raw-aware Term: the projection commutes with rename / subst / weaken
/ subst0 by construction.  No structural induction required; in
lean-fx the analogous `Term.toRaw_rename` was a 50+ line theorem. -/

#print axioms LeanFX2.Term.toRaw_rename
#print axioms LeanFX2.Term.toRaw_subst
#print axioms LeanFX2.Term.toRaw_weaken
#print axioms LeanFX2.Term.toRaw_subst0
