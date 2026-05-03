import LeanFX2.Foundation.SubstHet

/-! # AuditPhase12AB12SubstHet — heterogeneous (level-polymorphic) Subst audit

Phase 12.A.B1.2 part 2: SubstHet structure + Ty.substHet operation +
bridges to/from same-level Subst, all zero-axiom under strict policy.

Ships the level-polymorphic substitution unblocked by the Phase 1
intrinsic-cumul Ty.universe.  Used by Phase 4 to drop scope=0 on
Term.cumulUp and by Phase 6 to prove ConvCumul commutes with Subst.
-/

#print axioms LeanFX2.SubstHet
#print axioms LeanFX2.SubstHet.fromSubst
#print axioms LeanFX2.SubstHet.toSubst
#print axioms LeanFX2.SubstHet.cumul
#print axioms LeanFX2.SubstHet.identity
#print axioms LeanFX2.SubstHet.lift
#print axioms LeanFX2.Ty.substHet
#print axioms LeanFX2.SubstHet.lift_forTy_pointwise
#print axioms LeanFX2.SubstHet.lift_forRaw_pointwise
#print axioms LeanFX2.Ty.substHet_pointwise
#print axioms LeanFX2.Ty.substHet_fromSubst
#print axioms LeanFX2.Ty.substHet_cumul
