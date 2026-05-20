import LeanFX2.Reducibility.SN.Helpers

/-! # LeanFX2.Reducibility.NeutralSNFoundation.PiSigma

Variable SN atom.  Sole surviving live theorem after the Tait
`IsNeutral` cascade was retired in favour of Kripke step-indexed
reducibility: `RawTerm.var_isStronglyNormalizing` remains as a
direct atom consumed by `Reducibility.Kripke.Fundamental` and
`Term.SN.DirectCases`. -/

namespace LeanFX2

/-- Variables are strongly normalizing.  No `RawStep.par` ctor has
a variable as source other than `refl`, so any `parProgress` step
contradicts. -/
theorem RawTerm.var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing (RawTerm.var position) :=
  RawTerm.isStronglyNormalizing.intro (RawTerm.var position)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.var_inv progressStep.1).symm).elim)

end LeanFX2
