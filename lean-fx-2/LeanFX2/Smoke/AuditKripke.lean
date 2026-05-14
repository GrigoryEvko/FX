import LeanFX2.Reducibility.Kripke.Predicate
import LeanFX2.Reducibility.Kripke.Basic
import LeanFX2.Reducibility.Kripke.Weaken
import LeanFX2.Reducibility.Kripke.Monotone
import LeanFX2.Reducibility.Kripke.Project
import LeanFX2.Reducibility.Kripke.SNClosure

/-! Kripke Tait reducibility zero-axiom audit log. -/

#print axioms LeanFX2.ReducibleK
#print axioms LeanFX2.ReducibleKBody
#print axioms LeanFX2.ReducibleK.zero_eq_true
#print axioms LeanFX2.ReducibleK.succ_unit_iff_sn
#print axioms LeanFX2.ReducibleK.succ_bool_iff_sn
#print axioms LeanFX2.ReducibleK.succ_nat_iff_sn
#print axioms LeanFX2.ReducibleK.succ_empty_iff_sn
#print axioms LeanFX2.ReducibleK.succ_interval_iff_sn
#print axioms LeanFX2.ReducibleK.weaken_unit
#print axioms LeanFX2.ReducibleK.weaken_bool
#print axioms LeanFX2.ReducibleK.weaken_nat
#print axioms LeanFX2.ReducibleK.weaken_empty
#print axioms LeanFX2.ReducibleK.weaken_interval
#print axioms LeanFX2.ReducibleK.mono_unit
#print axioms LeanFX2.ReducibleK.mono_bool
#print axioms LeanFX2.ReducibleK.mono_nat
#print axioms LeanFX2.ReducibleK.mono_empty
#print axioms LeanFX2.ReducibleK.mono_interval
#print axioms LeanFX2.ReducibleK.sn_of_unit
#print axioms LeanFX2.ReducibleK.sn_of_bool
#print axioms LeanFX2.ReducibleK.sn_of_nat
#print axioms LeanFX2.ReducibleK.sn_of_empty
#print axioms LeanFX2.ReducibleK.sn_of_interval
#print axioms LeanFX2.RawTerm.isStronglyNormalizing.step_closure
#print axioms LeanFX2.Term.isStronglyNormalizing.step_closure
#print axioms LeanFX2.ReducibleK.cr2_unit
#print axioms LeanFX2.ReducibleK.cr2_bool
#print axioms LeanFX2.ReducibleK.cr2_nat
#print axioms LeanFX2.ReducibleK.cr2_empty
#print axioms LeanFX2.ReducibleK.cr2_interval
