import FX1Poly.Typed.DenoteKeyedLevelIrrelevance
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate

/-! # FX1Poly/Typed/DenoteKeyedPiFormationFromExistence
    — the denote Π-formation arm FROM CODOMAIN EXISTENCE (the route-D-friendly piArm)

Where `DenoteKeyedLevelIrrelevance.uniformDomainPi_reducibleAtEveryDenoteLevel` takes the codomain candidate as
DATA (a chosen `codomainCandidate` function), this file takes only the codomain IH's EXISTENCE —
`IsReducibleTypeAtAllDenoteLevels env (subst0 codomainCode argument)` — and extracts the per-level candidate
CHOICE-FREELY via the canonical-member-candidate engine (`IsReducibleTypeAtDenote.reducibleMemberCandidate`).
This is exactly the shape the denote fundamental theorem's Π-formation arm has: its codomain induction
hypothesis yields existence-of-a-candidate per argument, NOT a single chosen candidate, so the arm must build
the `piType` premise from existence without `Classical.choice`.

The construction, at each level: pick the canonical predicate `fun argument => IsReducibleMemberAtDenote env
level (subst0 codomainCode argument)` as the codomain candidate and discharge the `piType` per-argument premise
by `reducibleMemberCandidate` on the codomain existence at that level.  The domain-membership gating matches
because the domain candidate is UNIFORM across levels (it does not drift) — so the codomain existence, gated by
that same uniform `domainCandidate`, feeds each level's obligation directly.  This covers the domain shapes
whose candidate is level-stable: any uniform-candidate domain, and (the witnessing instance) neutral domains
— type variables and stuck applications, the common FT case `Π (x : X). C` under a context where `X` is a
variable.

## Zero-axiom verification

A single anonymous-constructor term per lemma: `fun level => ⟨_, ReducibleTypeStepDenote.piType …⟩`, the
codomain premise discharged by `(codomainExistence …).reducibleMemberCandidate`.  No tactic, no recursion.
`reducibleMemberCandidate` is `ofPointwiseIff` + `deterministic` (no `funext`, no `Quot.sound`); the `neutral`
constructor is by-construction.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- **Uniform-candidate-domain Π-formation from codomain EXISTENCE (choice-free).**  Given a domain reducible
with a SINGLE candidate at every denote level and the codomain reducible-at-all-levels (existence) under domain
membership, `Π domainCode codomainCode` is reducible at every denote level.  At each level the canonical
member-predicate of the closed codomain is its candidate (`reducibleMemberCandidate`), so the per-argument
codomain obligation is discharged from mere existence — no `Classical.choice`. -/
theorem uniformDomainPi_reducibleFromCodomainExistence {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainExistence : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  fun level => ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argument))
    (domainReducible level)
    (fun argument argumentInDomain =>
      (codomainExistence argument argumentInDomain level).reducibleMemberCandidate)⟩

/-- **Neutral-domain Π-formation from codomain EXISTENCE.**  The witnessing instance: a weak-head-normal non-Π
non-universe domain (a type variable or stuck application) has the literally-uniform candidate
`IsStronglyNormalizing` at every level, so the uniform-candidate arm applies with the codomain supplied as mere
existence. -/
theorem neutralDomainPi_reducibleFromCodomainExistence {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainExistence : ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  uniformDomainPi_reducibleFromCodomainExistence env IsStronglyNormalizing
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse)
    codomainExistence

end FX1Poly.Typed
