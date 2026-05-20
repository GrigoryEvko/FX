import LeanFX2.Term.Rename
import LeanFX2.Foundation.RawTermInjective
import LeanFX2.Foundation.TyRenameInjective

/-! # Term/RenameInjective/Core

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

theorem termRenameInjectiveCastHEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (typeEq : sourceType = targetType)
    (sourceTerm : Term context sourceType sourceRaw) :
    HEq (typeEq ▸ sourceTerm) sourceTerm := by
  cases typeEq
  rfl

end LeanFX2
