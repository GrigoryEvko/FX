import FX1Poly.Typed.PiFormerMembership
import FX1Poly.Typed.TelescopeReducible

/-! # FX1Poly/Typed/FormerChildrenReducible
    — the non-recursive 2-child former-children reducibility bundle and its dispatch to former membership

The fundamental theorem's `genFormationPi` arm runs only on the two dependent type-formers (Π / Σ), whose
premise telescope is ALWAYS exactly two children (domain, codomain).  Rather than a general (rebased,
consecutive-shift) telescope logical relation, this bundles exactly the three child fundamental-theorem
results the shipped dispatch lemmas (`piFormerOfChildMemberships` / `sigmaFormerOfChildMemberships`) consume:
the domain's universe membership at `predLevel+1` and `predLevel+2` (the latter only to mine a variable
inhabitant of the domain candidate), and the codomain's universe membership under a `cons`-extended
substitution for any reducible argument.  The specialized `fundamentalTelescope` companion (which inverts the
concrete two-`cons`-then-`nil` former telescope, calling the term fundamental theorem on each child head —
the mutual structural recursion already validated) produces this bundle; `toPiMember` / `toSigmaMember`
discharge the genFormationPi conclusion for each former.

## Zero-axiom verification

A `def` plus two one-line dispatches to the shipped `piFormerOfChildMemberships` /
`sigmaFormerOfChildMemberships`; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The 2-child former-children reducibility bundle.**  The three child fundamental-theorem results the
former membership dispatch consumes: the domain's universe membership at `predLevel+1` and `predLevel+2`, and
the codomain's universe membership under `cons argument substitution` for every reducible argument. -/
def FormerChildrenReducible {scope targetScope : Nat} (predLevel : Nat)
    (flag : UniverseFlag) (substitution : RawTermSubst scope (targetScope + 1))
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) : Prop :=
  IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell domainLevel flag) (RawTerm.subst substitution domainCode) ∧
    IsReducibleMemberAt (predLevel + 2)
      (universeCodeCell domainLevel flag) (RawTerm.subst substitution domainCode) ∧
    (∀ {memberLevel : Nat} (argument : RawTerm (targetScope + 1)),
      IsReducibleMemberAt memberLevel (RawTerm.subst substitution domainCode) argument →
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))

/-- **The level-exact 2-child former-children reducibility bundle.**  This weaker bundle packages exactly the
codomain premises consumed by the Π/Σ former-membership dispatches: codomain membership at the domain
candidate level `predLevel`, plus codomain membership at the one-higher level `predLevel + 1` used to get
open-body normalization from the fresh variable.  It is the intended target for future mixed-env telescope
companions; the older `FormerChildrenReducible` implies this bundle, but asks for a stronger
`∀ memberLevel` codomain premise. -/
def FormerChildrenReducibleAtDispatchLevels {scope targetScope : Nat} (predLevel : Nat)
    (flag : UniverseFlag) (substitution : RawTermSubst scope (targetScope + 1))
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) : Prop :=
  IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell domainLevel flag) (RawTerm.subst substitution domainCode) ∧
    IsReducibleMemberAt (predLevel + 2)
      (universeCodeCell domainLevel flag) (RawTerm.subst substitution domainCode) ∧
    (∀ argument : RawTerm (targetScope + 1),
      IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)) ∧
    (∀ argument : RawTerm (targetScope + 1),
      IsReducibleMemberAt (predLevel + 1) (RawTerm.subst substitution domainCode) argument →
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))

/-- The older all-member-level bundle implies the level-exact dispatch bundle. -/
theorem FormerChildrenReducible.toDispatchLevels {scope targetScope : Nat}
    {predLevel : Nat} {flag : UniverseFlag} {substitution : RawTermSubst scope (targetScope + 1)}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr}
    (bundle : FormerChildrenReducible predLevel flag substitution domainCode codomainCode
      domainLevel codomainLevel) :
    FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
      domainLevel codomainLevel :=
  ⟨bundle.1, bundle.2.1,
    fun argument argumentMember => bundle.2.2 argument argumentMember,
    fun argument argumentMember => bundle.2.2 argument argumentMember⟩

/-- **Dispatch the bundle to the Π former's universe membership.**  Unpacks the three child results and
applies the shipped `piFormerOfChildMemberships`. -/
theorem FormerChildrenReducible.toPiMember {scope targetScope : Nat}
    {predLevel : Nat} {flag : UniverseFlag} {substitution : RawTermSubst scope (targetScope + 1)}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr}
    (bundle : FormerChildrenReducible predLevel flag substitution domainCode codomainCode
      domainLevel codomainLevel) :
    IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell formerLevel flag)
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode)) :=
  IsReducibleMemberAt.piFormerOfChildMemberships bundle.1 bundle.2.1 bundle.2.2

/-- **Dispatch the level-exact bundle to the Π former's universe membership.** -/
theorem FormerChildrenReducibleAtDispatchLevels.toPiMember {scope targetScope : Nat}
    {predLevel : Nat} {flag : UniverseFlag} {substitution : RawTermSubst scope (targetScope + 1)}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr}
    (bundle : FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
      domainLevel codomainLevel) :
    IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell formerLevel flag)
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode)) :=
  IsReducibleMemberAt.piFormerOfChildMembershipsAtRequiredLevels bundle.1 bundle.2.1
    bundle.2.2.1 bundle.2.2.2

/-- **Dispatch the bundle to the Σ former's universe membership.**  The data-former twin of `toPiMember`,
applying the shipped `sigmaFormerOfChildMemberships`. -/
theorem FormerChildrenReducible.toSigmaMember {scope targetScope : Nat}
    {predLevel : Nat} {flag : UniverseFlag} {substitution : RawTermSubst scope (targetScope + 1)}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr}
    (bundle : FormerChildrenReducible predLevel flag substitution domainCode codomainCode
      domainLevel codomainLevel) :
    IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell formerLevel flag)
      (RawTerm.subst substitution
        (.mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))) :=
  IsReducibleMemberAt.sigmaFormerOfChildMemberships bundle.1 bundle.2.1 bundle.2.2

/-- **Dispatch the level-exact bundle to the Σ former's universe membership.** -/
theorem FormerChildrenReducibleAtDispatchLevels.toSigmaMember {scope targetScope : Nat}
    {predLevel : Nat} {flag : UniverseFlag} {substitution : RawTermSubst scope (targetScope + 1)}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr}
    (bundle : FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
      domainLevel codomainLevel) :
    IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell formerLevel flag)
      (RawTerm.subst substitution
        (.mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))) :=
  IsReducibleMemberAt.sigmaFormerOfChildMembershipsAtRequiredLevel bundle.1 bundle.2.1 bundle.2.2.2

/-- **Extract the bundle from the telescope logical relation.**  The mutual `fundamentalTelescope`
companion returns a `TelescopeReducible flag 0 2 substitution (domainLevel :: codomainLevel :: [])` over
the former's two-child spine; this projects the three child fundamental-theorem results the dispatch
lemmas consume.  Both child memberships at `predLevel` (domain) and `predLevel + 1` (domain, above) come
from the head conjunct `telescopeReducible.1` (universal in the level); the codomain conjunct comes from
the tail conjunct `telescopeReducible.2` applied to a domain member, whose own head conjunct (at the
codomain level) is read at `predLevel`.  The `TelescopeReducible` relation reduces definitionally at the
concrete two-`cons`-then-`nil` shape, so the projections typecheck directly.  This is the genFormationPi
arm's whole extraction step — the bridge from `fundamentalTelescope`'s output to `toPiMember` /
`toSigmaMember`. -/
theorem FormerChildrenReducible.ofTelescopeReducible {scope targetScope : Nat}
    (predLevel : Nat) {flag : UniverseFlag}
    {substitution : RawTermSubst scope (targetScope + 1)}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr}
    (telescopeReducible :
      TelescopeReducible flag 0 2 substitution (domainLevel :: codomainLevel :: [])
        (.childCons domainCode (.childCons codomainCode .childNil))) :
    FormerChildrenReducible predLevel flag substitution domainCode codomainCode
      domainLevel codomainLevel :=
  ⟨telescopeReducible.1 predLevel, telescopeReducible.1 (predLevel + 1),
    fun {_memberLevel} argument argumentMember =>
      (telescopeReducible.2 argument argumentMember).1 predLevel⟩

/-- **Extract the level-exact bundle from the telescope logical relation.**  This is the precise projection
of the two codomain levels consumed by the former dispatches. -/
theorem FormerChildrenReducibleAtDispatchLevels.ofTelescopeReducible {scope targetScope : Nat}
    (predLevel : Nat) {flag : UniverseFlag}
    {substitution : RawTermSubst scope (targetScope + 1)}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr}
    (telescopeReducible :
      TelescopeReducible flag 0 2 substitution (domainLevel :: codomainLevel :: [])
        (.childCons domainCode (.childCons codomainCode .childNil))) :
    FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
      domainLevel codomainLevel :=
  (FormerChildrenReducible.ofTelescopeReducible predLevel telescopeReducible).toDispatchLevels

end FX1Poly.Typed
