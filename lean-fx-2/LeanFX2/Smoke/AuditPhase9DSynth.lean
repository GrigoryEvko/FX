import LeanFX2.Algo.Synth

/-! Phase 9.D Synth helpers zero-axiom audit.

21 per-ctor synth helpers — each a `@[reducible]` wrapper around
the corresponding Term constructor.  They make the typing rules
visually explicit at the call site and provide consistent
calling conventions for the future `Algo/Infer` algorithm.
-/

namespace LeanFX2.SmokePhase9DSynth

#print axioms LeanFX2.Algo.Term.synthVar
#print axioms LeanFX2.Algo.Term.synthUnit
#print axioms LeanFX2.Algo.Term.synthBoolTrue
#print axioms LeanFX2.Algo.Term.synthBoolFalse
#print axioms LeanFX2.Algo.Term.synthNatZero
#print axioms LeanFX2.Algo.Term.synthListNil
#print axioms LeanFX2.Algo.Term.synthOptionNone
#print axioms LeanFX2.Algo.Term.synthApp
#print axioms LeanFX2.Algo.Term.synthAppPi
#print axioms LeanFX2.Algo.Term.synthFst
#print axioms LeanFX2.Algo.Term.synthNatSucc
#print axioms LeanFX2.Algo.Term.synthListCons
#print axioms LeanFX2.Algo.Term.synthOptionSome
#print axioms LeanFX2.Algo.Term.synthEitherInl
#print axioms LeanFX2.Algo.Term.synthEitherInr
#print axioms LeanFX2.Algo.Term.synthBoolElim
#print axioms LeanFX2.Algo.Term.synthNatElim
#print axioms LeanFX2.Algo.Term.synthNatRec
#print axioms LeanFX2.Algo.Term.synthListElim
#print axioms LeanFX2.Algo.Term.synthOptionMatch
#print axioms LeanFX2.Algo.Term.synthEitherMatch
#print axioms LeanFX2.Algo.Term.synthIdJ

end LeanFX2.SmokePhase9DSynth
