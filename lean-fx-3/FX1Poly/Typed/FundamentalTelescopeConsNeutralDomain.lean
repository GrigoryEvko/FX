import FX1Poly.Typed.FundamentalAtAllTelescopePositiveArguments
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsLeaves

/-! # FX1Poly/Typed/FundamentalTelescopeConsNeutralDomain
    — the formation-FT telescope-cons arm CLOSES for a neutral / data-former domain

This is the ASSEMBLY of the member-side leaf into the formation fundamental theorem's binder
(telescope-cons) arm.  The all-level cons companion
`fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises` reduces the cons arm to its
`headMemberExtendsToAllPositive` premise (one-level head member ⇒ all-positive head member, so the all-level
Kripke environment extends by the fresh argument) plus the tail-recursion premise.  When the (substituted)
DOMAIN is neutral or a data former, that head-member premise is discharged outright by
`headMemberExtendsToAllPositive_ofNeutralClassifier` (membership in such a classifier is
`IsStronglyNormalizing`, level-independent).

So the formation-FT telescope-cons arm — the arm that has carried the lone `sorry` in the all-level
assembly — CLOSES unconditionally for every former whose domain is neutral or a data former (variable /
stuck eliminator / Σ / Nat / List / Option / Either / Id / product / sum codes), leaving only the tail
recursion (supplied by the FT's own inductive hypothesis).  The residual open case is a former whose domain
weak-head-reduces to a Π- or universe-rooted type (higher-order / type-polymorphic domains).

## Zero-axiom verification

A direct composition of the shipped companion with the neutral-classifier head-member premise; no new
proof.  Verified `#print axioms` clean: no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The formation-FT telescope-cons arm, closed for a neutral / data-former domain.**  When the
substituted domain `RawTerm.subst substitution head` is weak-head-normal and neither Π- nor universe-rooted,
the cons companion's head-member premise is discharged by the member-side leaf, so the telescope-cons
relation holds given only the tail recursion.  This is the binder arm of the all-level fundamental theorem
for every non-type-polymorphic (non-Π / non-universe-domain) former. -/
theorem fundamentalTelescopeConsAtAllNeutralDomain {profile : PolyProfile}
    {baseScope targetScope currentDepth count : Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)}
    (reducibleEnv : ReducibleEnvAtAllLevels context substitution)
    (headFundamental : FundamentalConclusionAtAll context head (universeCodeCell headLevel flag))
    (substitutedHeadWeakHeadNormal :
      ∀ reduct : RawTerm (targetScope + 1),
        ¬ WeakHeadStep (RawTerm.subst substitution head) reduct)
    (substitutedHeadNotPiType :
      (RawTerm.subst substitution head).rootGenerator ≠ Generator.gen_piTyCode)
    (substitutedHeadNotUniverse :
      (RawTerm.subst substitution head).rootGenerator ≠ Generator.gen_universeCode)
    (tailReducibleAtAllPositiveArgument :
      ∀ (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution head) argument →
          TelescopeReducible flag (currentDepth + 1) count
            (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducible flag currentDepth (count + 1) substitution (headLevel :: restLevels)
      (.childCons head rest) :=
  fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises reducibleEnv headFundamental
    (headMemberExtendsToAllPositive_ofNeutralClassifier substitutedHeadWeakHeadNormal
      substitutedHeadNotPiType substitutedHeadNotUniverse)
    tailReducibleAtAllPositiveArgument

end FX1Poly.Typed
