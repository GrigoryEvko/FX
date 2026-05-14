import LeanFX2.Reducibility.Kripke.Predicate
import LeanFX2.Reducibility.Kripke.Basic

/-! Kripke Tait reducibility zero-axiom audit log.

Pins for each Kripke `Reducibility.Kripke.*` declaration verifying
zero-axiom discipline (no propext, no Quot.sound, no Classical.choice,
no Acc/WellFounded dependents). -/

#print axioms LeanFX2.ReducibleK
#print axioms LeanFX2.ReducibleKBody
#print axioms LeanFX2.ReducibleK.zero_eq_true
#print axioms LeanFX2.ReducibleK.succ_unit_iff_sn
#print axioms LeanFX2.ReducibleK.succ_bool_iff_sn
#print axioms LeanFX2.ReducibleK.succ_nat_iff_sn
#print axioms LeanFX2.ReducibleK.succ_empty_iff_sn
#print axioms LeanFX2.ReducibleK.succ_interval_iff_sn
