import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StratifiedReducibleMemberNonDependent

/-! # FX1Poly/Core/StratifiedReducibleSmoke
    — concrete end-to-end smoke tests of the stratified reducibility → strong-normalization pipeline

These witnesses exercise the choice-free dependent-reducibility stack (the `ofPointwiseIff` congruence
closure, the canonical member-predicate, and the choice-free Π formation/introduction) end to end on CLOSED,
genuinely-well-typed cells, producing strong normalization via CR1 (`IsReducibleMemberAt.stronglyNormalizing`).
They are baby cases of the SN-for-well-typed fundamental-theorem corollary (#426): "a well-typed term is a
reducible member of its type, hence strongly normalizing", instantiated at concrete closed terms so the whole
pipeline is exercised before the general fundamental-theorem induction lands.

## Zero-axiom verification

Each smoke composes shipped pieces (`IsReducibleMemberAt.universeFormation`,
`IsReducibleMemberAt.stronglyNormalizing`, the universe-code reducibility) — no new proof obligation, no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- **SN of a closed universe code, via the reducibility → SN pipeline.**  `Type@levelExpr` is a reducible
member of `Type@(lsucc levelExpr)` (`universeFormation`), and reducible members are strongly normalizing
(CR1, `IsReducibleMemberAt.stronglyNormalizing`) — so the universe code is strongly normalizing.  A concrete
instance of "a well-typed term is strongly normalizing" routed through the stratified reducibility model
rather than the direct leaf-normality argument: `Type@e : Type@(lsucc e)` ⟹ `SN (Type@e)`. -/
theorem universeCode_stronglyNormalizing_viaReducibility {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm (scope + 1)) :=
  (IsReducibleMemberAt.universeFormation predLevel levelExpr flag).stronglyNormalizing

end FX1Poly.Core
