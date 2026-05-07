import LeanFX2.Algo.Completeness

/-! # Smoke/AuditPhase10AlgoCompleteness — M10 atomic + single-recurse reviewer log

Reviewer-facing `#print axioms` log over the M10 completeness
theorems shipped in `Algo/Completeness.lean`.  Each entry MUST
report "does not depend on any axioms" under strict policy (no
propext, no Quot.sound, no Classical.choice, no user axioms).

## Coverage

* Atomic fragment (5): `_var`, `_unit`, `_boolTrue`, `_boolFalse`,
  `_natZero` — each `rfl` against `Term.infer`'s pattern-match arm.
* Single-recurse fragment (5): `_natSucc`, `_optionSome`,
  `_modIntro`, `_modElim`, `_subsume` — each takes a structural IH
  on the inner sub-term and pushes through `unfold + rw [innerIH]`.

The 10 together close the atomic + single-recurse portion of M10
(#1279); multi-recurse cases (`app`, `fst`, `snd`, `listCons`,
`idJ`) and check-mode-only cases (`lam`, `pair`, `refl`,
eliminators) remain follow-on work.

The build-failing axiom gate is `#audit_namespace LeanFX2`
(`Tools/AuditGen.lean`), which auto-walks the `LeanFX2.*`
namespace excluding `Tools` / `Smoke`.  This file is
informational; failures here would already have failed the
build at the audit gate.
-/

#print axioms LeanFX2.Term.infer_complete_var
#print axioms LeanFX2.Term.infer_complete_unit
#print axioms LeanFX2.Term.infer_complete_boolTrue
#print axioms LeanFX2.Term.infer_complete_boolFalse
#print axioms LeanFX2.Term.infer_complete_natZero
#print axioms LeanFX2.Term.infer_complete_natSucc
#print axioms LeanFX2.Term.infer_complete_optionSome
#print axioms LeanFX2.Term.infer_complete_modIntro
#print axioms LeanFX2.Term.infer_complete_modElim
#print axioms LeanFX2.Term.infer_complete_subsume
