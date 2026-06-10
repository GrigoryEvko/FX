import FX1Poly.Typed.PinnedPiRenameImage

/-! Probe: STR-8 brick 5 — ENRICH the pinning analysis with the SOURCE chain.  The shipped
`Conv.pinnedPiComponentsInRenameImage` proof constructs `StepStar classifierBase reflected` and
drops it (`_sourceChain`); the piIntro arm needs it: `classifierBase ↝* piTyCodeCell domainBase
codomainBase` AT THE SOURCE, so source SR + Π-formation inversion can discharge the source-side
universe premises from classifierBase's source-typedness. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The pinning analysis with the source chain**: a Π-code `Conv` to a `ρ`-image exposes EXACT
image components AND the base itself `StepStar`-reduces to the source Π-cell over those components.
The source chain is what lets the reflection's piIntro arm type `domainBase`/`codomainBase` on the
source side (source subject reduction from `classifierBase`'s typing + Π-formation inversion). -/
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

end FX1Poly.Typed

#print axioms FX1Poly.Typed.Conv.pinnedPiComponentsWithSourceChain
