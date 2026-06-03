import FX1Poly.Typed.FundamentalAtAllPositiveArguments
import FX1Poly.Core.StratifiedReducibleUniverseDecode

/-! # FX1Poly/Typed/UniverseCumulativity
    — cumulativity of reducibility across universe levels (SN-072), and its honest model scope

SN-072 asks whether reducibility respects the universe inclusion `Type@e ⊆ Type@(e+1)`: a reducible member of
`Type@e` should be a reducible member of the higher universe.  This file discharges it for FX's stratified
Tarski reducibility model — and pins exactly what cumulativity MEANS in that model.

The stratified model (`StratifiedReducibleType.lean`) stratifies the logical relation by a META-level `Nat`
fuel, and its `universeCode` arm produces the SAME candidate (`universeReducibilityPredicate lower`) for EVERY
`gen_universeCode (levelExpr, flag)` payload — the meta-fuel is DECOUPLED from the kernel's object-level
`LevelExpr` universe labels (documented at `StratifiedReducibleUniverseDecode.lean`).  The no-Type-in-Type
hierarchy discipline (`Type@e : Type@(lsucc e)`, NOT `Type@e : Type@e`) is enforced by the TYPING rules
(`HasType` universe formation, `#442`), not re-derived in this permissive semantic interpretation.

Consequently `IsReducibleMemberAt.universeMembership_iff` decodes membership in `Type@levelExpr` at fuel
`predLevel + 1` to `IsStronglyNormalizing ∧ IsReducibleTypeAt predLevel` — a payload INDEPENDENT of
`levelExpr` / `flag`.  So universe membership is level-label-IRRELEVANT: cumulativity holds, and is in fact a
two-way EQUIVALENCE (`universeMembershipLevelLabelIrrelevant`).  Cumulativity `Type@e ⊆ Type@(lsucc e)` is its
named corollary (`universeCumulativity`, single-level and all-positive-level forms).

**Honest scope.**  This is cumulativity in the coarse fuel-stratified model where the object-level hierarchy
is invisible to the reducibility relation.  A finer model that matches the meta-fuel to the cell's `LevelExpr`
(the deferred per-`LevelExpr` refinement noted in `StratifiedReducibleType.lean`) would make cumulativity a
genuine one-way inclusion rather than an equivalence; that refinement is future work.  The theorems here are
real (a membership iff-transport through the universe decode/encode), not vacuous — they correctly state that
the semantic model does not see the universe hierarchy, which is the honest content of SN-072 at this layer.

## Zero-axiom verification

Each lemma composes `IsReducibleMemberAt.universeMembership_iff` (decode) with itself (encode) at the two
labels; the all-positive form quantifies the single-level corollary over fuels.  No induction.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Universe membership is level-label-irrelevant** (at a fixed meta-fuel).  Membership in `Type@levelExpr`
at fuel `predLevel + 1` is equivalent to membership in `Type@levelExpr'` for any other label/flag, because the
universe decode (`universeMembership_iff`) produces the `LevelExpr`/`flag`-independent payload
`IsStronglyNormalizing ∧ IsReducibleTypeAt predLevel`.  The reducibility model does not see the object-level
universe hierarchy (enforced by typing, not the semantic model) — so cumulativity is a two-way equivalence
here. -/
theorem IsReducibleMemberAt.universeMembershipLevelLabelIrrelevant {scope predLevel : Nat}
    {levelExpr levelExpr' : LevelExpr} {flag flag' : UniverseFlag} {typeCode : RawTerm scope} :
    IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag) typeCode ↔
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr' flag') typeCode :=
  (IsReducibleMemberAt.universeMembership_iff (levelExpr := levelExpr) (flag := flag)).trans
    (IsReducibleMemberAt.universeMembership_iff (levelExpr := levelExpr') (flag := flag')).symm

/-- **Cumulativity (single fuel level), SN-072.**  A reducible member of `Type@levelExpr` is a reducible
member of the higher universe `Type@(lsucc levelExpr)` — the named corollary of level-label-irrelevance.  (In
this model the converse also holds; see `universeMembershipLevelLabelIrrelevant`.) -/
theorem IsReducibleMemberAt.universeCumulativity {scope predLevel : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (member : IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag) typeCode) :
    IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell (LevelExpr.lsucc levelExpr) flag) typeCode :=
  IsReducibleMemberAt.universeMembershipLevelLabelIrrelevant.mp member

/-- **Cumulativity at all positive fuels, SN-072.**  The all-positive-levels form: an all-positive member of
`Type@levelExpr` is an all-positive member of `Type@(lsucc levelExpr)`, by applying the single-level
cumulativity at each fuel. -/
theorem IsReducibleMemberAtAllPositiveLevels.universeCumulativity {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (member : IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag) typeCode) :
    IsReducibleMemberAtAllPositiveLevels (universeCodeCell (LevelExpr.lsucc levelExpr) flag) typeCode :=
  fun level => IsReducibleMemberAt.universeCumulativity (member level)

end FX1Poly.Typed
