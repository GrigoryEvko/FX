import LeanFX2.Reducibility

namespace LeanFX2.Smoke

open LeanFX2

/-! K12.1 + K12.2 — Tait reducibility-candidate predicate
`Reducible` indexed by target type, plus the `Reducible.nat`
base-type arm.  Each `#print axioms` line below must report
"does not depend on any axioms".

K12.1 ships:
* `RawStep.parProgress` — non-reflexive parallel reduction
  (a `RawStep.par` step that fires at least one redex).
  Distinguishing source from target sidesteps the
  `RawStep.par.refl` trivial loop in the SN encoding.
* `RawTerm.isStronglyNormalizing` — inductive Prop closure
  under non-trivial parallel reduction.  Same shape as Lean's
  `Acc` but emits its own recursor, no Acc dependency
  (satisfies `GatesCore.acc_dependent_budget` 0).
* `Term.isStronglyNormalizing` — typed SN as raw SN of the
  term's raw projection (lifts through `Term.toRaw`
  definitionally).
* `Reducible` — inductive predicate `Reducible : Term ... →
  Prop` with per-Ty arms shipping incrementally across K12.x.

K12.2 ships:
* `Reducible.nat` — first per-Ty arm: a closed natural is
  reducible iff it is strongly normalizing (Tait's base-type
  clause).

K12.3 ships:
* `Reducible.bool` — closed boolean reducibility = SN.
* `Reducible.unit` — closed unit reducibility = SN (structurally
  trivial: one canonical inhabitant).
* `Reducible.empty` — closed empty reducibility = SN (no
  canonical inhabitants; reduction must terminate at a neutral
  form).

Future K12.4-K12.16 fill the remaining Ty arms;
K12.18-K12.26 ship the fundamental lemma;
K12.27 closes M04 / `strong_normalization`. -/

#print axioms RawStep.parProgress
#print axioms RawTerm.isStronglyNormalizing
#print axioms Term.isStronglyNormalizing
#print axioms Reducible
#print axioms Reducible.nat
#print axioms Reducible.bool
#print axioms Reducible.unit
#print axioms Reducible.empty

end LeanFX2.Smoke
