import FX1Poly.Typed.FundamentalAtAllPositiveArguments

/-! # FX1Poly/Typed/UniverseDomainMemberExtension
    — the universe-domain member-extension is EXACTLY type-level positive level-irrelevance

The formation-fragment fundamental theorem's telescope-cons arm (`HasTypeDesc.fundamentalAtAll`) reduces,
via `fundamentalTelescopeConsAtAllFromAllLevelHeadCandidateCompanion`, to manufacturing the all-positive
member-extension principle for the binder's DOMAIN type: a one-positive-level member of the domain extends
to a member at every positive level (so the all-level Kripke environment `ReducibleEnvAtAllLevels` can be
`cons`-extended by a fresh argument).  For NEUTRAL / Π / Σ domains the candidate producers already discharge
this (`HasAllPositiveReducibleCandidateAt.ofNeutralClassifier` / `.piType` / `.sigmaType`).  The remaining
hard case is the **universe domain** — the type-polymorphic binder `Π (A : Type@levelExpr). …` — which is
the `gen_universeCode` Tarski case.

This file pins that last case to its cleanest possible form.  By the universe decode
(`IsReducibleMemberAt.universeMembership_iff`: membership in `Type@levelExpr` at fuel `predLevel + 1` is
strong normalization together with type-reducibility at fuel `predLevel`, ONE LEVEL DOWN) and the
all-positive universe encode (`IsReducibleMemberAtAllPositiveLevels.universeCode_iff`: all-positive
membership is strong normalization together with `IsReducibleTypeAtAllLevels`), the universe-domain
member-extension holds for a type code EXACTLY when that code's one-positive-level type-reducibility lifts to
ALL-level type-reducibility — i.e. precisely **type-level level-irrelevance**.  The strong-normalization
half transfers for free; the entire content is the type-level lift.

This is a genuine reduction, not a restatement: it strips the membership/SN layer off the fundamental
theorem's last obligation and exposes the pure type-level core
`IsReducibleTypeAt predLevel A → IsReducibleTypeAtAllLevels A`, which is the form the level-congruence
inductive step `ReducibleTypeStep.existsCongr` is built to thread (its docstring records the remaining
degenerate-fuel-`0` boundary obstruction, and the well-formedness escape route).  The cons-arm universe
domain is closed the moment that type-level lift is supplied.

## Zero-axiom verification

Each direction is one application of the universe decode/encode iff and a hypothesis use; no induction.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The universe-domain member-extension from type-level level-irrelevance (per type code).**  If the
type code's one-positive-level type-reducibility (`IsReducibleTypeAt predLevel`) lifts to all-level
type-reducibility, then a positive-level member of `Type@levelExpr` is a member at every positive level.
The strong-normalization half of universe membership is preserved verbatim; the lift supplies the type
half. -/
theorem IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUnderTypeLevelIrrelevance
    {scope : Nat} {predLevel : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {typeCode : RawTerm scope}
    (typeLevelIrrelevance :
      IsReducibleTypeAt predLevel typeCode → IsReducibleTypeAtAllLevels typeCode)
    (member : IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag) typeCode) :
    IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag) typeCode := by
  have decoded : IsStronglyNormalizing typeCode ∧ IsReducibleTypeAt predLevel typeCode :=
    (IsReducibleMemberAt.universeMembership_iff
      (predLevel := predLevel) (levelExpr := levelExpr) (flag := flag)).mp member
  exact (IsReducibleMemberAtAllPositiveLevels.universeCode_iff
    (levelExpr := levelExpr) (flag := flag)).mpr
    ⟨decoded.1, typeLevelIrrelevance decoded.2⟩

/-- **The universe-domain positive member-extension principle, packaged from uniform type-level
irrelevance.**  Quantifying `ofUniverseMemberUnderTypeLevelIrrelevance` over the term and fuel gives the
exact shape the fundamental theorem's cons arm consumes for a universe domain
(`∀ {term predLevel}, IsReducibleMemberAt (predLevel+1) (Type@levelExpr) term →
IsReducibleMemberAtAllPositiveLevels (Type@levelExpr) term`): the cons-arm universe-domain case is closed by
a uniform type-level level-irrelevance witness. -/
theorem universeDomainMemberExtension_ofTypeLevelIrrelevance
    {scope : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typeLevelIrrelevance :
      ∀ {typeCode : RawTerm scope} {predLevel : Nat},
        IsReducibleTypeAt predLevel typeCode → IsReducibleTypeAtAllLevels typeCode) :
    ∀ {term : RawTerm scope} {predLevel : Nat},
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag) term →
        IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag) term :=
  fun {_term} {_predLevel} member =>
    IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUnderTypeLevelIrrelevance
      (fun typeReducible => typeLevelIrrelevance typeReducible) member

/-- **Tightness of the reduction.**  Conversely, the universe-domain member-extension principle (applied to
a strongly-normalizing type code reducible at one positive fuel) recovers all-level type-reducibility — so
the cons-arm universe-domain obligation is EQUIVALENT to type-level level-irrelevance, not merely implied by
it.  (The strong-normalization premise is the encode side of universe membership; it is automatic for the
reducible domains the fundamental theorem feeds, via CR1.) -/
theorem typeLevelIrrelevance_ofUniverseDomainMemberExtension
    {scope : Nat} {predLevel : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {typeCode : RawTerm scope}
    (memberExtension :
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag) typeCode →
        IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag) typeCode)
    (typeNormalizing : IsStronglyNormalizing typeCode)
    (typeReducible : IsReducibleTypeAt predLevel typeCode) :
    IsReducibleTypeAtAllLevels typeCode := by
  have member : IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag) typeCode :=
    (IsReducibleMemberAt.universeMembership_iff
      (predLevel := predLevel) (levelExpr := levelExpr) (flag := flag)).mpr
      ⟨typeNormalizing, typeReducible⟩
  exact ((IsReducibleMemberAtAllPositiveLevels.universeCode_iff
    (levelExpr := levelExpr) (flag := flag)).mp (memberExtension member)).2

end FX1Poly.Typed
