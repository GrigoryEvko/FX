import LeanFX2.Algo.Completeness

/-! # Smoke/AuditPhase10AlgoCompleteness — M10 full bidirectional reviewer log

Reviewer-facing `#print axioms` log over the M10 completeness
theorems shipped in `Algo/Completeness.lean`.  Each entry MUST
report "does not depend on any axioms" under strict policy (no
propext, no Quot.sound, no Classical.choice, no user axioms).

## Coverage — bidirectional bidi M10

### Inferable subset (15 theorems)

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

### Check-mode counterparts (15 theorems)

Mirrors the inferable atomic + single-recurse + parametric +
binder cases at `Term.check`.

* Atomic check fragment (5): `check_complete_var`, `_unit`,
  `_boolTrue`, `_boolFalse`, `_natZero` — direct `dif_pos rfl`
  in term mode (avoids `simp only` propext leak via `eq_self`).
* Parametric leaves (2): `check_complete_listNil`,
  `_optionNone` — `rfl` via outer expected-type match arm.
* Single-recurse check (4): `check_complete_natSucc`,
  `_optionSome`, `_eitherInl`, `_eitherInr` — `simp only
  [Term.check]; rw [innerIH]` (or `show`-with-dite for
  natSucc's DecEq dispatch).
* Multi-recurse check (1): `check_complete_listCons` —
  matches expectedType to listType then recurses on head + tail.
* Binder check (3): `check_complete_lam` (arrow),
  `_lamPi` (Π), `_pair` (Σ) — expected-type splitter feeds
  body recursion at the right type.

Closes both sides of M10 (#1279) completely.  Eliminator and
HoTT/cubical/modal-primitive check arms remain deferred to
their own dedicated milestones (each requires motive synthesis
or canonical-equality dispatch beyond the simple recipes here).

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
#print axioms LeanFX2.Term.check_complete_var
#print axioms LeanFX2.Term.check_complete_unit
#print axioms LeanFX2.Term.check_complete_boolTrue
#print axioms LeanFX2.Term.check_complete_boolFalse
#print axioms LeanFX2.Term.check_complete_natZero
#print axioms LeanFX2.Term.check_complete_listNil
#print axioms LeanFX2.Term.check_complete_optionNone
#print axioms LeanFX2.Term.check_complete_natSucc
#print axioms LeanFX2.Term.check_complete_optionSome
#print axioms LeanFX2.Term.check_complete_eitherInl
#print axioms LeanFX2.Term.check_complete_eitherInr
#print axioms LeanFX2.Term.check_complete_listCons
#print axioms LeanFX2.Term.check_complete_lam
#print axioms LeanFX2.Term.check_complete_lamPi
#print axioms LeanFX2.Term.check_complete_pair
