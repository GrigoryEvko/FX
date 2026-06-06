import FX1Poly.Core.ReducibleMemberNeutral
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.WeakHeadStep
import FX1Poly.Typed.CellConstructors

/-! # FX1Poly/Typed/ReducibleMemberFormation
    — membership at a universe-code classifier is exactly strong normalization

The fundamental theorem's FORMATION arms (universe formation, type-former formation) have a UNIVERSE-CODE
classifier (`universeCodeCell levelExpr flag` — the code `Type@levelExpr` at universe `flag`).  A universe
code is a NORMAL LEAF (`noStep_universeCode`), hence neutral, so semantic membership there collapses to
strong normalization (`IsReducibleMember.atNeutralClassifier`):

  `IsReducibleMember (universeCodeCell levelExpr flag) term ↔ IsStronglyNormalizing term`.

This is the bridge the formation arm reads in the `←` direction (an SN formation subject — a universe
code or a type former with SN children — is a reducible member of its universe-code classifier) and the
`→` direction supplies (a well-formed type's term is SN).

## Zero-axiom verification

`universeCodeCell_noWeakHeadStep` derives "no weak-head step" from `noStep_universeCode` via
`WeakHeadStep.toStep` (weak-head reduction embeds into full reduction); the universe code is not Π-rooted
by `Generator.noConfusion`.  `atUniverseCode` then specializes the Core
`IsReducibleMember.atNeutralClassifier`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- A universe-code cell admits no weak-head step.  It is a normal leaf (`noStep_universeCode`), and every
weak-head step embeds into a full step (`WeakHeadStep.toStep`), so a weak-head step would contradict
leaf-normality. -/
theorem universeCodeCell_noWeakHeadStep {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ∀ reduct : RawTerm scope, ¬ WeakHeadStep (universeCodeCell levelExpr flag) reduct := by
  intro reduct weakHeadStep
  exact noStep_universeCode (levelExpr, flag) weakHeadStep.toStep

/-- **Membership at a universe-code classifier is exactly strong normalization.**  A universe code is
neutral (weak-head-normal by `universeCodeCell_noWeakHeadStep`, and not Π-rooted), so a term is a
reducible member of `universeCodeCell levelExpr flag` precisely when strongly normalizing — the
fundamental theorem's formation-arm bridge between a well-formed type term and its strong normalization. -/
theorem IsReducibleMember.atUniverseCode {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {term : RawTerm scope} :
    IsReducibleMember (universeCodeCell levelExpr flag) term ↔ IsStronglyNormalizing term := by
  apply IsReducibleMember.atNeutralClassifier (universeCodeCell_noWeakHeadStep levelExpr flag)
  intro rootIsPiType
  exact Generator.noConfusion rootIsPiType

end FX1Poly.Typed
