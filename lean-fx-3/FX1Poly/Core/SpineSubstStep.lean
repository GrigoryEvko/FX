import FX1Poly.Core.SpineConsStep
import FX1Poly.Core.RawTermSubst

/-! # Foundation/PolyCell/Core/SpineSubstStep
   — subst-shaped spine step helpers for the SR-beta mutual block

Part of the spine-renamer substrate consumed by the SR-beta and SR-cong
mutual blocks (`SubstPreservationMutual.lean`, `CongPreservationMutual.lean`).
Sibling files: `SpineRenameStep.lean`, `SpineConsStep.lean`,
`StepHCCWrappers.lean`.

This file packages the two spine-side subst cases the
`HasCertifiedCellDim0.preservedBySubst` mutual block needs:

* nil: substituting an empty child spine stays empty;
* cons: the head is substituted under `headSpec.scopeShift` binders
  via `iterateLiftRaw`, the tail is substituted at the parent scope,
  and `CertifiedTermSpine.consStep_dim0Trivial` rebuilds the spine.

These helpers are deliberately non-recursive.  The mutual block
produces the substituted head cell and substituted tail spine
recursively, then calls the cons helper here.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- Empty spines are stable under substitution.  This is the nil arm of
the certified-spine substitution recursion. -/
def CertifiedTermSpine.substNilStep
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope) :
    CertifiedTermSpine profile [] tgtScope []
      (foldChildren GenAlgebra.canonical sigma
        (.childNil : RawTermChildren [] srcScope)) := by
  exact CertifiedTermSpine.nilStep

/-- Cons arm for certified-spine substitution.

The head child lives under `headSpec.scopeShift` additional binders, so
it is substituted by `iterateLiftRaw sigma headSpec.scopeShift`; the
tail remains at parent scope and uses `sigma` directly.  Given those
two recursive results, this helper rebuilds the substituted cons spine
with the existing dim-0 boundary-cast helper. -/
def CertifiedTermSpine.substConsStep_dim0Trivial
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    {headSpec : ChildSpec} {restSpecs : List ChildSpec}
    {restShifts : List Nat}
    (hHeadDim0 : headSpec.cellDimension = 0)
    (sigma : RawTermSubst srcScope tgtScope)
    {headRaw : RawTerm (srcScope + headSpec.scopeShift)}
    {restRaws : RawTermChildren restShifts srcScope}
    (substitutedHeadCell :
      PolyCell profile headSpec.cellSort 0
        (tgtScope + headSpec.scopeShift) CellBoundary.trivial
        (.termBase
          (RawTerm.subst
            (iterateLiftRaw sigma headSpec.scopeShift) headRaw)))
    (substitutedRestSpine :
      CertifiedTermSpine profile restSpecs tgtScope restShifts
        (foldChildren GenAlgebra.canonical sigma restRaws)) :
    CertifiedTermSpine profile (headSpec :: restSpecs) tgtScope
      (headSpec.scopeShift :: restShifts)
      (foldChildren GenAlgebra.canonical sigma
        (.childCons headRaw restRaws)) := by
  change CertifiedTermSpine profile (headSpec :: restSpecs) tgtScope
    (headSpec.scopeShift :: restShifts)
    (.childCons
      (RawTerm.subst (iterateLiftRaw sigma headSpec.scopeShift) headRaw)
      (foldChildren GenAlgebra.canonical sigma restRaws))
  exact CertifiedTermSpine.consStep_dim0Trivial hHeadDim0
    substitutedHeadCell substitutedRestSpine

end FX1Poly.Core
