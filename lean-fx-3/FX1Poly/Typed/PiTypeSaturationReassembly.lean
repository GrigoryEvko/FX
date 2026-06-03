import FX1Poly.Typed.FundamentalAtAllPositiveArguments

/-! # FX1Poly/Typed/PiTypeSaturationReassembly
    — the Π type-saturation reassembly arm (toward #672 / SN-043)

`FundamentalAtAllPositiveArguments.lean` ships the Π type-reducibility PROJECTIONS — from an all-level
reducible Π type, the domain is all-level reducible (`IsReducibleTypeAtAllLevels.domainOfPiType`) and each
instantiated codomain is all-positive reducible for an all-positive argument
(`codomainOfPiTypeAtAllPositiveArgument`).  This file ships the INVERSE: reassembling a Π type's
all-positive reducibility FROM its components' reducibility.

This is the Π arm of the type-level fuel-saturation the #672 gate
(`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes`) needs at its universe-member-is-a-Π case
(member `T = Π dom. cod`, reducible at one fuel ⟹ reducible at all fuels reduces to reassembling `T` at
every positive fuel from its saturated components).  Like the other gate arms
(`extendsToAllPositiveAtWeakHeadExpansion`, the Π MEMBER extension), it is a CONDITIONAL inductive step:
it takes the components' fuel-stability as hypotheses (the IH the eventual well-founded recursion supplies).

**Choice-free.**  The codomain candidate at each argument is fed the FIXED canonical member-predicate
`IsReducibleMemberAt (predLevel+1) (subst0 cod arg)` (no `∃ candidate` extracted), discharged from mere
EXISTENCE of a codomain candidate via the shipped `IsReducibleTypeAt.reducibleMemberCandidate` engine
(PathA-3) — the same choice-free Π-codomain technique the dependent fundamental theorem uses.

## The conditional hypotheses (the recursion's IH shape)

* `domainAllPositive` — the domain is reducible at every positive fuel;
* `domainMembersStable` — domain membership is fuel-stable (a level-`predLevel+1` member is an all-positive
  member); this coerces an argument in the level-specific domain candidate up to an all-positive member so
  the codomain hypothesis applies;
* `codomainAllPositive` — for every all-positive domain member, the instantiated codomain is reducible at
  every positive fuel.

The first two are the domain's fuel-stability, the third the codomain's — exactly the sub-term IHs of the
#672 well-founded recursion.  The universe / whnf arms remain elsewhere; the recursion tie-up (#672) is the
open crux.

## Zero-axiom verification

The `piType` constructor of `ReducibleTypeStep` (through the `ReducibleTypeAt (predLevel+1) =
ReducibleTypeStep (ReducibleTypeAt predLevel)` defeq), `IsReducibleTypeAt.reducibleMemberCandidate`, and
existential repackaging.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Π type-saturation reassembly** (the Π arm of the #672 type-level fuel-saturation).  From the domain's
all-positive reducibility + domain-member fuel-stability + the instantiated codomain's all-positive
reducibility (per all-positive argument), the Π type `Π dom. cod` is reducible at every positive fuel.  The
inverse of `IsReducibleTypeAtAllLevels.domainOfPiType` / `codomainOfPiTypeAtAllPositiveArgument`.  At fuel
`predLevel+1`, the `piType` arm builds the dependent function-space: the domain reducibility comes from
`domainAllPositive`; for each argument in the level-specific domain candidate, `domainMembersStable` lifts
it to an all-positive domain member, `codomainAllPositive` then gives the codomain reducible at that fuel,
and the FIXED canonical member-predicate is its candidate by `reducibleMemberCandidate` (choice-free). -/
theorem IsReducibleTypeAtAllPositiveLevels.ofPiType {scope : Nat}
    {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    (domainAllPositive : IsReducibleTypeAtAllPositiveLevels dom)
    (domainMembersStable : ∀ {arg : RawTerm scope} {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1) dom arg → IsReducibleMemberAtAllPositiveLevels dom arg)
    (codomainAllPositive : ∀ {arg : RawTerm scope},
        IsReducibleMemberAtAllPositiveLevels dom arg →
        IsReducibleTypeAtAllPositiveLevels (RawTerm.subst0 cod arg)) :
    IsReducibleTypeAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil))) := by
  intro predLevel
  obtain ⟨domCand, domReducible⟩ := domainAllPositive predLevel
  refine ⟨_, ReducibleTypeStep.piType
    (fun arg => IsReducibleMemberAt (predLevel + 1) (RawTerm.subst0 cod arg))
    domReducible ?_⟩
  intro arg argInDomCand
  have argMember : IsReducibleMemberAt (predLevel + 1) dom arg := ⟨domCand, domReducible, argInDomCand⟩
  have codReducibleType : IsReducibleTypeAt (predLevel + 1) (RawTerm.subst0 cod arg) :=
    codomainAllPositive (domainMembersStable argMember) predLevel
  exact codReducibleType.reducibleMemberCandidate

end FX1Poly.Typed
