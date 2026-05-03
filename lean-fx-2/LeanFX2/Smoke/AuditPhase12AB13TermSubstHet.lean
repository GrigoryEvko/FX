import LeanFX2.Term.SubstHet

/-! # AuditPhase12AB13TermSubstHet — heterogeneous typed Term substitution audit

Phase 12.A.B1.3-finish: Term.substHet + TermSubstHet structure +
TermSubstHet.lift, all zero-axiom under strict policy.

This is the level-polymorphic typed substitution that crosses universe
levels.  Used by Phase 4 to drop scope=0 on Term.cumulUp and by
Phase 6 to formulate the general ConvCumul.subst_compatible.

The architecture mirrors Term/Subst.lean: ~30 ctor cases, with the
heterogeneous foundation lemmas (Ty.weaken_substHet_commute,
Ty.subst0_substHet_commute) handling the cross-level casts.
-/

#print axioms LeanFX2.TermSubstHet
#print axioms LeanFX2.TermSubstHet.lift
#print axioms LeanFX2.Term.substHet
