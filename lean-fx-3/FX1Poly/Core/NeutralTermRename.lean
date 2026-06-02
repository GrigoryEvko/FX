import FX1Poly.Core.NeutralTerm
import FX1Poly.Core.RawTermRename

/-! # Foundation/PolyCell/Core/NeutralTermRename
    — neutrality is preserved by renaming

A neutral term (stuck at the root: a variable or an elimination form with a neutral principal child) stays
neutral after any renaming.  Renaming preserves the root generator and the principal child's position, so
each `IsNeutral` arm renames to the same arm with the principal child's neutrality from the induction
hypothesis.

This is the structural prerequisite for the (Kripke) reducibility-candidate CR3 of the dependent arrow: in
that proof a neutral function `functionTerm` is applied (under a renaming `furtherRenaming`) to a fresh
variable, and the application `app (rename furtherRenaming functionTerm) argument` must be neutral — which
needs `rename furtherRenaming functionTerm` neutral, i.e. this lemma, then `IsNeutral.app`.

## Zero-axiom verification

A single induction on `IsNeutral`; each of the twelve arms closes by `exact IsNeutral.<arm> ih`, the
renaming computing definitionally through `mkGen` so the constructor's principal-child position receives
the renamed child directly.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega` (verified by `#print axioms` in scratch before landing).  Gated per declaration in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Neutrality is preserved by renaming.**  Renaming preserves the stuck-root structure (root generator
and principal child position), so a neutral term renames to a neutral term — the principal child's
neutrality threading through by the induction hypothesis. -/
theorem IsNeutral.rename {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} (neutral : IsNeutral term) :
    IsNeutral (RawTerm.rename forwardRenaming term) := by
  induction neutral with
  | var index => exact IsNeutral.var _
  | app _headNeutral ih => exact IsNeutral.app ih
  | fst _argumentNeutral ih => exact IsNeutral.fst ih
  | snd _argumentNeutral ih => exact IsNeutral.snd ih
  | boolElim _scrutineeNeutral ih => exact IsNeutral.boolElim ih
  | natElim _scrutineeNeutral ih => exact IsNeutral.natElim ih
  | natRec _scrutineeNeutral ih => exact IsNeutral.natRec ih
  | listElim _scrutineeNeutral ih => exact IsNeutral.listElim ih
  | optionMatch _scrutineeNeutral ih => exact IsNeutral.optionMatch ih
  | eitherMatch _scrutineeNeutral ih => exact IsNeutral.eitherMatch ih
  | idJ _witnessNeutral ih => exact IsNeutral.idJ ih
  | idStrictRec _witnessNeutral ih => exact IsNeutral.idStrictRec ih

end FX1Poly.Core
