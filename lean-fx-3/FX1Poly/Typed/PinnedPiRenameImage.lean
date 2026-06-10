import FX1Poly.Typed.PinnedPiImageComponents
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/PinnedPiRenameImage — the pinning analysis over an ARBITRARY renaming
     (route-H reflection brick 2)

Under binders the pinned reflection works at `lift ρ` (and `lift (lift ρ)`, …), so the
weaken-specific analysis of `PinnedPiImageComponents` must generalize over the renaming.  This file
ships the two destructuring bricks of the reflection's `piIntro` arm:

  * `Conv.pinnedPiComponentsInRenameImage` — a Π-code `Conv` to a `ρ`-image exposes its components
    EXACTLY in the image: the image `StepStar`-reduces to a Π-cell whose domain is an exact
    `rename ρ domainBase` and whose codomain is an exact `rename (lift ρ) codomainBase`, each
    `Conv` to the original component.  `Conv.pinnedPiComponentsInWeakenImage` is the `ρ := weaken`
    instance.
  * `renameEqLamCellInversion` — an image term that IS a λ comes from a λ, with the body an exact
    `lift ρ`-image (the subject-destructuring step: from `rename ρ s = lamCell body` recover
    `s = lamCell sourceBody` with `body = rename (lift ρ) sourceBody`).

Together with the shipped `rename_lift_weaken_commute` / `rename_piTyCodeCell` /
`Conv.piTyCode_cong` / `RawRenaming.lift_injective`, these are the piIntro arm's full destructuring
kit; the remaining piIntro prerequisite is term-level rename injectivity from `Fin`-injectivity
(for `Conv.reflectRename` at `lift ρ`), a separate brick.

## Zero-axiom verification

Both proofs are the STR-1 mkGen drilling: the var head dies by `Generator.noConfusion` after
collapsing the (empty) child spine; the non-var head drills `rename_mkGen_of_ne_var` + the concrete
child spine, with `iterateLiftRaw ρ 1` definitionally `RawRenaming.lift ρ`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

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

/-- **The pinning analysis with the source chain**: a Π-code `Conv` to a `ρ`-image exposes EXACT
image components AND the base itself `StepStar`-reduces to the source Π-cell over those components.
The source chain is what lets the reflection's piIntro arm type `domainBase`/`codomainBase` on the
source side (source subject reduction from `classifierBase`'s typing + Π-formation inversion).
Same proof as `pinnedPiComponentsInRenameImage` — the reflected source reduct IS
`piTyCodeCell domainBase codomainBase` (Unit-payload eta), so the source chain lands on it
directly. -/
theorem Conv.pinnedPiComponentsWithSourceChain {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {domainCode : RawTerm targetScope} {codomainCode : RawTerm (targetScope + 1)}
    {classifierBase : RawTerm sourceScope}
    (pinned : Conv (piTyCodeCell domainCode codomainCode) (RawTerm.rename rho classifierBase)) :
    ∃ (domainBase : RawTerm sourceScope) (codomainBase : RawTerm (sourceScope + 1)),
      StepStar classifierBase (piTyCodeCell domainBase codomainBase) ∧
      Conv domainCode (RawTerm.rename rho domainBase) ∧
      Conv codomainCode (RawTerm.rename (RawRenaming.lift rho) codomainBase) := by
  obtain ⟨domainReduct, codomainReduct, imageChain, domainConv, codomainConv⟩ :=
    Conv.reducesToPiTyCode pinned.sym
  obtain ⟨reflected, sourceChain, imageEq⟩ :=
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
            refine ⟨domainChild, codomainChild, sourceChain, ?_, ?_⟩
            · rw [← hDomainReduct] at domainConv
              exact domainConv
            · rw [← hCodomainReduct] at codomainConv
              exact codomainConv

/-- **λ-head rename inversion**: an image term that IS a Church-style λ comes from a λ, with BOTH the
domain annotation an exact `ρ`-image and the body an exact `lift ρ`-image — the subject-destructuring
step of the reflection's piIntro arm.  T2 strengthens this: the λ now carries its domain annotation as
the first child, so the inversion recovers the SOURCE domain syntactically (the domain is pinned, not
free).  The `[0, 1]`-spine twin of `renameEqAppCellInversion`. -/
theorem renameEqLamCellInversion {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {sourceTerm : RawTerm sourceScope}
    {domainAnn : RawTerm targetScope} {body : RawTerm (targetScope + 1)}
    (imageIsLam : RawTerm.rename rho sourceTerm = lamCell domainAnn body) :
    ∃ (sourceDomain : RawTerm sourceScope) (sourceBody : RawTerm (sourceScope + 1)),
      sourceTerm = lamCell sourceDomain sourceBody ∧
      domainAnn = RawTerm.rename rho sourceDomain ∧
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
      | childCons domainChild restChildren =>
        cases restChildren with
        | childCons bodyChild nilChildren =>
          cases nilChildren with
          | childNil =>
            dsimp only [RawTermChildren.rename, foldChildren, iterateLiftRaw] at hChildrenEq
            injection hChildrenEq with hHeadScope hHeadShift hRestShifts hDomainChild
              hTailChildren
            injection hTailChildren with hTailScope hTailShift hTailRestShifts hBodyChild
              hNilChildren
            exact ⟨domainChild, bodyChild, rfl, hDomainChild.symm, hBodyChild.symm⟩

/-- **Application-head rename inversion**: an image term that IS an application comes from an
application with exact-image function and argument — the piElim residual's subject-destructuring
step (the `[0, 0]`-spine twin of `renameEqLamCellInversion`). -/
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
