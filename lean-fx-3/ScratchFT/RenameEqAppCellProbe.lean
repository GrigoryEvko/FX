import FX1Poly.Typed.PinnedPiRenameImage

/-! Probe: STR-8b enabling brick — app-head rename inversion ([0,0] spine drilling, the appCell
twin of `renameEqLamCellInversion`). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Application-head rename inversion**: an image term that IS an application comes from an
application with exact-image function and argument — the piElim residual's subject-destructuring
step. -/
theorem renameEqAppCellInversion {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {sourceTerm : RawTerm sourceScope} {functionTerm argument : RawTerm targetScope}
    (imageIsApp : RawTerm.rename rho sourceTerm = appCell functionTerm argument) :
    ∃ (sourceFunction sourceArgument : RawTerm sourceScope),
      sourceTerm = appCell sourceFunction sourceArgument ∧
      functionTerm = RawTerm.rename rho sourceFunction ∧
      argument = RawTerm.rename rho sourceArgument := by
  cases sourceTerm with
  | mkGen generator payload children =>
    by_cases hVar : generator = .gen_var
    · subst hVar
      cases children with
      | childNil =>
        rw [RawTerm.rename_var_reduces] at imageIsApp
        injection imageIsApp with hScope hGenerator hPayload hChildren
        exact Generator.noConfusion hGenerator
    · rw [RawTerm.rename_mkGen_of_ne_var rho hVar] at imageIsApp
      injection imageIsApp with hScope hGenerator hPayload hChildren
      subst hGenerator
      have hChildrenEq := eq_of_heq hChildren
      cases children with
      | childCons functionChild restChildren =>
        cases restChildren with
        | childCons argumentChild nilChildren =>
          cases nilChildren with
          | childNil =>
            dsimp only [RawTermChildren.rename, foldChildren, iterateLiftRaw] at hChildrenEq
            injection hChildrenEq with hHeadScope hHeadShift hRestShifts hFunctionChild
              hTailChildren
            injection hTailChildren with hTailScope hTailShift hTailRestShifts hArgumentChild
              hNilChildren
            exact ⟨functionChild, argumentChild, rfl,
              hFunctionChild.symm, hArgumentChild.symm⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.renameEqAppCellInversion
