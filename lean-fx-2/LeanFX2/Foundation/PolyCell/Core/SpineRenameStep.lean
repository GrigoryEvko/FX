import LeanFX2.Foundation.PolyCell.Core.SpineConsStep
import LeanFX2.Foundation.PolyCell.Core.RawTermRename

/-! # Foundation/PolyCell/Core/SpineRenameStep
   — rename-shaped spine step helpers for structural preservation

Per `M-spineRenamers-retro` (#379): this file is part of the
~400-LoC spine-renamer substrate task home consumed by M2 #251
(SR arm 17 beta) + M3 #252 (SR arm 18 cong) mutual block.
Sibling files in the retro: `SpineSubstStep.lean`,
`SpineConsStep.lean`, `StepHCCWrappers.lean`.

This is the rename sibling of `SpineSubstStep.lean`.  It packages
the certified-spine nil/cons cases against
`foldChildren GenAlgebra.canonical rho`, so the future mutual
rename-preservation proof can focus on recursive descent rather than
repeating the `foldChildren` shape and dim-0 cons rebuild.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- Empty spines are stable under renaming.  This is the nil arm of
the future certified-spine rename recursion. -/
def CertifiedTermSpine.renameNilStep
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (rho : RawRenaming srcScope tgtScope) :
    CertifiedTermSpine profile [] tgtScope []
      (foldChildren GenAlgebra.canonical rho
        (.childNil : RawTermChildren [] srcScope)) := by
  exact CertifiedTermSpine.nilStep

/-- Cons arm for certified-spine renaming.

The head child lives under `headSpec.scopeShift` binders, so it is
renamed by `iterateLiftRaw rho headSpec.scopeShift`; the tail stays at
parent scope and uses `rho` directly. -/
def CertifiedTermSpine.renameConsStep_dim0Trivial
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    {headSpec : ChildSpec} {restSpecs : List ChildSpec}
    {restShifts : List Nat}
    (hHeadDim0 : headSpec.cellDimension = 0)
    (rho : RawRenaming srcScope tgtScope)
    {headRaw : RawTerm (srcScope + headSpec.scopeShift)}
    {restRaws : RawTermChildren restShifts srcScope}
    (renamedHeadCell :
      PolyCell profile headSpec.cellSort 0
        (tgtScope + headSpec.scopeShift) CellBoundary.trivial
        (.termBase
          (RawTerm.rename
            (iterateLiftRaw rho headSpec.scopeShift) headRaw)))
    (renamedRestSpine :
      CertifiedTermSpine profile restSpecs tgtScope restShifts
        (foldChildren GenAlgebra.canonical rho restRaws)) :
    CertifiedTermSpine profile (headSpec :: restSpecs) tgtScope
      (headSpec.scopeShift :: restShifts)
      (foldChildren GenAlgebra.canonical rho
        (.childCons headRaw restRaws)) := by
  change CertifiedTermSpine profile (headSpec :: restSpecs) tgtScope
    (headSpec.scopeShift :: restShifts)
    (.childCons
      (RawTerm.rename (iterateLiftRaw rho headSpec.scopeShift) headRaw)
      (foldChildren GenAlgebra.canonical rho restRaws))
  exact CertifiedTermSpine.consStep_dim0Trivial hHeadDim0
    renamedHeadCell renamedRestSpine

end LeanFX2.Foundation.PolyCell.Core
