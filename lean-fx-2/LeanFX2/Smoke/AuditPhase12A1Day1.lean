import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst

/-! # AuditPhase12A1Day1 — Day 1 (Phase 12.A.1) comprehensive zero-axiom audit.

Day 1 of the cubical+2LTT+HOTT sprint shipped:
* D1.5 — 13 new Ty ctors (covered separately in AuditPhase12A1NewTyCtors)
* D1.6 — 27 new RawTerm ctors (cubical / HOTT / refine / record / codata /
  session / effect / strict)
* D1.7 — RawSubst extensions: rename + subst arms for all 27 new ctors,
  plus the foundation lemmas (rename_pointwise, rename_compose,
  weaken_rename_commute, subst_pointwise, subst_rename_commute,
  rename_subst_commute, subst_identity, subst_compose) all extended
  with the 27 cases
* D1.8 — Subst.lean Ty.subst arms for path / glue / oeq / idStrict /
  equiv / refine / record / codata / session / effect / modal / empty /
  interval (covered separately in AuditPhase12A1NewTyCtors)
* D1.9–D1.11 — DEFERRED to per-need addition; raw scaffolding suffices
  for D2.* / D3.* downstream work

Every declaration listed must report "does not depend on any axioms".
The 212-job project build implicitly verifies the same — this file
explicitly enumerates the Day-1 deliverables for traceability.
-/

-- D1.6: RawTerm inductive (27 new ctors live inside the inductive)
#print axioms LeanFX2.RawTerm

-- D1.7: RawTerm renaming foundation
#print axioms LeanFX2.RawTerm.rename
#print axioms LeanFX2.RawTerm.rename_pointwise
#print axioms LeanFX2.RawTerm.rename_compose
#print axioms LeanFX2.RawTerm.weaken_rename_commute

-- D1.7: RawTerm substitution foundation
#print axioms LeanFX2.RawTerm.subst
#print axioms LeanFX2.RawTerm.subst_pointwise
#print axioms LeanFX2.RawTerm.subst_rename_commute
#print axioms LeanFX2.RawTerm.rename_subst_commute
#print axioms LeanFX2.RawTerm.subst_identity
#print axioms LeanFX2.RawTerm.subst_compose

-- D1.7: RawTerm β-load-bearing lemmas
#print axioms LeanFX2.RawTerm.weaken_subst_singleton
#print axioms LeanFX2.RawTerm.weaken_subst_commute

-- D1.7: RawTermSubst infrastructure
#print axioms LeanFX2.RawTermSubst.identity
#print axioms LeanFX2.RawTermSubst.lift
#print axioms LeanFX2.RawTermSubst.singleton
#print axioms LeanFX2.RawTermSubst.compose
#print axioms LeanFX2.RawTermSubst.lift_pointwise
#print axioms LeanFX2.RawTermSubst.lift_then_rename_lift
#print axioms LeanFX2.RawTermSubst.lift_renaming_pull
#print axioms LeanFX2.RawTermSubst.singleton_rename_commute_pointwise
#print axioms LeanFX2.RawTermSubst.identity_lift_pointwise
#print axioms LeanFX2.RawTermSubst.weaken_then_singleton_pointwise
#print axioms LeanFX2.RawTermSubst.weaken_lift_subst_pointwise
#print axioms LeanFX2.RawTermSubst.lift_compose_pointwise
