import LeanFX2.Algo.Completeness

/-! # Smoke/AuditPhase10AlgoCompleteness — M10 full inferable subset reviewer log

Reviewer-facing `#print axioms` log over the M10 completeness
theorems shipped in `Algo/Completeness.lean`.  Each entry MUST
report "does not depend on any axioms" under strict policy (no
propext, no Quot.sound, no Classical.choice, no user axioms).

## Coverage — full inferable subset (15 theorems)

* Atomic fragment (5): `_var`, `_unit`, `_boolTrue`, `_boolFalse`,
  `_natZero` — each `rfl` against `Term.infer`'s pattern-match arm.
* Single-recurse fragment (5): `_natSucc`, `_optionSome`,
  `_modIntro`, `_modElim`, `_subsume` — structural IH plus
  `unfold + rw [innerIH]`.
* Multi-recurse fragment (5): `_app`, `_fst`, `_snd`, `_listCons`,
  `_idJ` — `unfold + rw [IH...]; dsimp only; (exact dif_pos rfl)?`
  — `dsimp only` reduces the deep nested match definitionally
  (no propext leak), and the dite is closed by `dif_pos rfl`
  for the type-equality dispatch arms (`app`, `listCons`).

Closes the inferable side of M10 (#1279) completely.  Check-mode
companion (`Term.check_complete_X` family for `lam`, `pair`, `refl`,
all eliminators, all modal/cubical/HOTT primitives) remains
deferred — those constructors are check-only by design.

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
#print axioms LeanFX2.Term.infer_complete_app
#print axioms LeanFX2.Term.infer_complete_fst
#print axioms LeanFX2.Term.infer_complete_snd
#print axioms LeanFX2.Term.infer_complete_listCons
#print axioms LeanFX2.Term.infer_complete_idJ
