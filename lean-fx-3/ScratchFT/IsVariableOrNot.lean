import FX1Poly.Typed.UniverseCodeShape

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem RawTerm.isVariableOrNot {scope : Nat} (term : RawTerm scope) :
    (∃ index : Fin scope, term = variableCell index) ∨
    (∀ index : Fin scope, term ≠ variableCell index) := by
  by_cases headIsVariable : RawTerm.headGenerator term = Generator.gen_var
  · exact Or.inl (eq_variableCell_of_headGenerator headIsVariable)
  · refine Or.inr (fun index termEqVariable => headIsVariable ?_)
    rw [termEqVariable]
    exact headGenerator_variableCell index

end FX1Poly.Typed

#print axioms FX1Poly.Typed.RawTerm.isVariableOrNot
