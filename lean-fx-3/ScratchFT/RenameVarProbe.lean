import FX1Poly.Typed.ConsistentStratification
import FX1Poly.Core.CandidateInterpretationRename
import FX1Poly.Typed.HasTypeWeakening
import FX1Poly.Typed.UniverseCodeShape

/-! SCRATCH: rename-variable inversion for the #662 cons-preservation. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

-- variableCell injectivity
example {scope : Nat} {a b : Fin scope} (h : variableCell a = variableCell b) : a = b := by
  injection h with _ payloadEq

-- the inversion
theorem renameEqVariableCellInversion {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {typeIndex : Fin targetScope}
    (isVar : RawTerm.rename rawRenaming term = variableCell typeIndex) :
    ∃ sourceIndex : Fin sourceScope,
      term = variableCell sourceIndex ∧ rawRenaming sourceIndex = typeIndex := by
  have rootVar : RawTerm.headGenerator term = Generator.gen_var := by
    have step : (RawTerm.rename rawRenaming term).rootGenerator = Generator.gen_var := by
      rw [isVar]; rfl
    rwa [RawTerm.rename_rootGenerator] at step
  obtain ⟨sourceIndex, termEq⟩ := eq_variableCell_of_headGenerator rootVar
  refine ⟨sourceIndex, termEq, ?_⟩
  rw [termEq, rename_variableCell] at isVar
  injection isVar with _ payloadEq

end FX1Poly.Typed
