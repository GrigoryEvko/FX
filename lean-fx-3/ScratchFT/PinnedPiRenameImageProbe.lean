import FX1Poly.Typed.PinnedPiImageComponents
import FX1Poly.Typed.HasTypeDescPi

/-! Probe: STR-8 brick 2 — the pinning analysis over an ARBITRARY renaming + the λ-head rename
inversion.

Under binders the reflection works at `lift ρ`, so the weaken-specific analysis must generalize:
`Conv.pinnedPiComponentsInRenameImage` is the arbitrary-`ρ` form (same drilling).  The piIntro arm
also needs to destruct an image λ: `RawTerm.renameEqLamCellInversion` inverts
`rename ρ s = lamCell body` into `s = lamCell sourceBody` with the body an exact lift-image. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The pinning analysis over an arbitrary renaming**: a Π-code `Conv` to a `ρ`-image exposes its
components EXACTLY in the image — the image `StepStar`-reduces to a Π-cell whose domain is an exact
`rename ρ` and whose codomain is an exact `rename (lift ρ)`, each `Conv` to the original component.
Generalizes `Conv.pinnedPiComponentsInWeakenImage` (the `ρ := weaken` instance); the reflection
needs this form under binders, where it works at `lift ρ`. -/
theorem Conv.pinnedPiComponentsInRenameImage {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {domainCode : RawTerm targetScope} {codomainCode : RawTerm (targetScope + 1)}
    {classifierBase : RawTerm sourceScope}
    (pinned : Conv (piTyCodeCell domainCode codomainCode) (RawTerm.rename rho classifierBase)) :
    ∃ (domainBase : RawTerm sourceScope) (codomainBase : RawTerm (sourceScope + 1)),
      StepStar (RawTerm.rename rho classifierBase)
        (piTyCodeCell (RawTerm.rename rho domainBase)
          (RawTerm.rename (RawRenaming.lift rho) codomainBase)) ∧
      Conv domainCode (RawTerm.rename rho domainBase) ∧
      Conv codomainCode (RawTerm.rename (RawRenaming.lift rho) codomainBase) := by
  obtain ⟨domainReduct, codomainReduct, imageChain, domainConv, codomainConv⟩ :=
    Conv.reducesToPiTyCode pinned.sym
  obtain ⟨reflected, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename rho imageChain
  cases reflected with
  | mkGen generator payload children =>
    by_cases hVar : generator = Generator.gen_var
    · subst hVar
      cases children with
      | childNil =>
        rw [RawTerm.rename_var_reduces] at imageEq
        injection imageEq with hScope hGenerator hPayload hChildren
        exact Generator.noConfusion hGenerator
    · rw [RawTerm.rename_mkGen_of_ne_var _ hVar] at imageEq
      injection imageEq with hScope hGenerator hPayload hChildren
      subst hGenerator
      have hChildrenEq := eq_of_heq hChildren
      cases children with
      | childCons domainChild restChildren =>
        cases restChildren with
        | childCons codomainChild nilChildren =>
          cases nilChildren with
          | childNil =>
            dsimp only [RawTermChildren.rename, foldChildren, iterateLiftRaw] at hChildrenEq
            injection hChildrenEq with hHeadScope hHeadShift hRestShifts hDomainReduct
              hTailChildren
            injection hTailChildren with hTailScope hTailShift hTailRestShifts hCodomainReduct
              hNilChildren
            refine ⟨domainChild, codomainChild, ?_, ?_, ?_⟩
            · rw [← hDomainReduct, ← hCodomainReduct] at imageChain
              exact imageChain
            · rw [← hDomainReduct] at domainConv
              exact domainConv
            · rw [← hCodomainReduct] at codomainConv
              exact codomainConv

/-- **λ-head rename inversion**: an image term that IS a λ comes from a λ, with the body an exact
lift-image — the destructuring step of the reflection's piIntro arm. -/
theorem renameEqLamCellInversion {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {sourceTerm : RawTerm sourceScope} {body : RawTerm (targetScope + 1)}
    (imageIsLam : RawTerm.rename rho sourceTerm = lamCell body) :
    ∃ sourceBody : RawTerm (sourceScope + 1),
      sourceTerm = lamCell sourceBody ∧
      body = RawTerm.rename (RawRenaming.lift rho) sourceBody := by
  cases sourceTerm with
  | mkGen generator payload children =>
    by_cases hVar : generator = Generator.gen_var
    · subst hVar
      cases children with
      | childNil =>
        rw [RawTerm.rename_var_reduces] at imageIsLam
        injection imageIsLam with hScope hGenerator hPayload hChildren
        exact Generator.noConfusion hGenerator
    · rw [RawTerm.rename_mkGen_of_ne_var _ hVar] at imageIsLam
      injection imageIsLam with hScope hGenerator hPayload hChildren
      subst hGenerator
      have hChildrenEq := eq_of_heq hChildren
      cases children with
      | childCons bodyChild nilChildren =>
        cases nilChildren with
        | childNil =>
          dsimp only [RawTermChildren.rename, foldChildren, iterateLiftRaw] at hChildrenEq
          injection hChildrenEq with hHeadScope hHeadShift hRestShifts hBodyChild hNilChildren
          exact ⟨bodyChild, rfl, hBodyChild.symm⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.Conv.pinnedPiComponentsInRenameImage
#print axioms FX1Poly.Typed.renameEqLamCellInversion
