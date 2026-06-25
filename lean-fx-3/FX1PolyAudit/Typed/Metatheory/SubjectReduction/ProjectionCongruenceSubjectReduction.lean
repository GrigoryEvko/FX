import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ProjectionCongruenceSubjectReduction

/-! # FX1PolyAudit/ProjectionCongruenceSubjectReduction — param-output elim congruence SR audit shard

Per-declaration zero-axiom gate for the param-output eliminator-congruence subject reduction arms (gate 2 of
the consistency leg, TYTAB-2-FT-SR #1697): fst / snd scrutinee congruence and pathApp path/argument
congruence.  Each must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.fstScrutineeCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.sndScrutineeCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.pathAppPathCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.pathAppArgumentCongruenceSubjectReduction

end FX1PolyAudit
