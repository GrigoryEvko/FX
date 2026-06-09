import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Core.ConvRenameReflection

/-! # FX1Poly/Typed/PinnedPiImageComponents — the pinning analysis (route-H reflection brick 1)

The strengthening campaign's three refutations (`GrownStrengtheningRefutation`,
`GrownCheckSoundnessRefutation`, `ConvExistentialStrengtheningRefutation`) force the route-H
reflection motive: induction over engine derivations with the image-PINNED-classifier premise
`∃ S_img, Conv S (weaken S_img)`.  This file ships the analysis every binder arm consumes:

  * `Conv.pinnedPiComponentsInWeakenImage` — a Π-classifier `Conv` to a weakening exposes its
    components EXACTLY in the weaken image: the weakening `StepStar`-reduces to a Π-cell whose
    domain is an exact `weaken domainBase` and whose codomain is an exact
    `rename (lift weaken) codomainBase`, each `Conv` to the original component.

Proof composition: `Conv.reducesToPiTyCode` (#1060) reduces the weakening to a Π-reduct with
`Conv`-related components; `StepStar.reflectRename` (#1104) pulls that chain back through the
weakening (the image is reduction-closed); the mkGen drilling (the STR-1 recipe) forces the
reduct's components to be exact renames — the var head dies by `Generator.noConfusion` (a renamed
variable is never Π-headed), the non-var head drills through `rename_mkGen_of_ne_var` and the
concrete `[0,1]` child spine.

## Why this is THE load-bearing brick

In the reflection's `piIntro` arm, the derivation's freely-chosen domain `domainCode` was the
historical wall (it can mention the fresh variable — `ConvExistentialStrengtheningRefutation`'s
witness).  Under the pinned premise this lemma hands the arm an EXACT in-image representative
`weaken domainBase` with `Conv domainCode (weaken domainBase)`: the binder swaps to the image
(grown context conversion), the codomain pin recurses identically, and the small-side `piIntro`
rebuilds over `domainBase`/`codomainBase`.  The same analysis serves the universe-classified
type-code reflection's Π-former cases.

## Zero-axiom verification

`reducesToPiTyCode` + `StepStar.reflectRename` + the drilling (injection on `mkGen` emits the
leading scope equation; `childCons` injection emits five components; `dsimp only
[RawTermChildren.rename, foldChildren, iterateLiftRaw]` reduces the concrete spine;
`iterateLiftRaw weaken 1` is definitionally `RawRenaming.lift RawRenaming.weaken`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The pinning analysis**: a Π-code `Conv` to a weakening exposes its components in the weaken
image — the weakening `StepStar`-reduces to a Π-cell whose domain is an EXACT `weaken` and whose
codomain is an EXACT lift-weaken rename, each `Conv` to the original component. -/
theorem Conv.pinnedPiComponentsInWeakenImage {scope : Nat}
    {domainCode : RawTerm (scope + 1)} {codomainCode : RawTerm (scope + 2)}
    {classifierBase : RawTerm scope}
    (pinned : Conv (piTyCodeCell domainCode codomainCode) (RawTerm.weaken classifierBase)) :
    ∃ (domainBase : RawTerm scope) (codomainBase : RawTerm (scope + 1)),
      StepStar (RawTerm.weaken classifierBase)
        (piTyCodeCell (RawTerm.weaken domainBase)
          (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) codomainBase)) ∧
      Conv domainCode (RawTerm.weaken domainBase) ∧
      Conv codomainCode (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) codomainBase) := by
  obtain ⟨domainReduct, codomainReduct, weakenChain, domainConv, codomainConv⟩ :=
    Conv.reducesToPiTyCode pinned.sym
  obtain ⟨reflected, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename RawRenaming.weaken
      (show StepStar (RawTerm.rename RawRenaming.weaken classifierBase)
          (piTyCodeCell domainReduct codomainReduct) from weakenChain)
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
            · rw [← hDomainReduct, ← hCodomainReduct] at weakenChain
              exact weakenChain
            · rw [← hDomainReduct] at domainConv
              exact domainConv
            · rw [← hCodomainReduct] at codomainConv
              exact codomainConv

end FX1Poly.Typed
