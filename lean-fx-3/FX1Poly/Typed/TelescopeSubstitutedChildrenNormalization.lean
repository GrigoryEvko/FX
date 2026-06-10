import FX1Poly.Typed.LiftedChildNormalizationFromClosure
import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Typed.HasTypeDescSubjectStronglyNormalizingNative

/-! # FX1Poly/Typed/TelescopeSubstitutedChildrenNormalization
   — telescope reducibility ⟹ SN of every substituted child (GTL-06 kernel, brick 2)

Brick 1 (`liftedSubstOfConsClosureAtFreshVariable`) extracted the fresh-variable instantiation
that turns a cons-closure into LIFTED-open child SN.  This brick assembles the kernel's child
half: from `TelescopeReducible` at each arity the current formation table uses, strong
normalization of EVERY substituted child — in exactly the spine positions the substituted
former cell stores them:

  * count 1 (`[0]` — list/option/unit-free unary rows): the head membership at any positive
    level, CR1 — `subst σ element` is SN.
  * count 2 (`[0,1]` — Π/Σ-shaped binary rows): the head membership gives `subst σ domain` SN;
    the tail closure + brick 1 give `subst (lift σ) codomain` SN — the binder-child position.
  * count 0 (nullary rows): the substituted spine is `childNil`; `allStronglyNormalizing` is
    trivially `True` (no lemma needed; recorded for the arity inventory).

The `substituted*SpineStronglyNormalizing` corollaries package these as
`RawTermChildren.allStronglyNormalizing` of the LITERAL substituted spines — the exact input
`formerCellStronglyNormalizingOfChildren` (the cascade-free N-child accessibility assembly)
consumes.  Brick 3 (the table-generic dispatch arm) plugs these into the six dispatch files'
single generic non-Π branch; a new formation row at an EXISTING arity then absorbs with zero
new lines anywhere.  Arity ≥ 3 (`consecutiveShifts` would produce a shift-2 child) remains the
named non-blocker from brick 1 — no current row has one.

## Zero-axiom verification

CR1 projections (`.stronglyNormalizing`) of telescope head memberships + one application of
brick 1 per binder child; the spine corollaries are anonymous-constructor packaging.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Unary telescope ⟹ substituted element SN.**  The count-1 telescope's head membership at
any positive level projects to strong normalization (CR1). -/
theorem TelescopeReducible.substitutedOneChildStronglyNormalizing
    {baseScope targetScope : Nat} {flag : UniverseFlag}
    {substitution : RawTermSubst baseScope (targetScope + 1)}
    {elementCode : RawTerm baseScope} {elementLevel : LevelExpr}
    (telescope : TelescopeReducible flag 0 1 substitution [elementLevel]
      (.childCons elementCode .childNil)) :
    IsStronglyNormalizing (RawTerm.subst substitution elementCode) :=
  (telescope.1 0).stronglyNormalizing

/-- **Binary (Π/Σ-shaped) telescope ⟹ both substituted children SN.**  The head membership
gives the domain (CR1); the tail closure feeds brick 1
(`liftedSubstOfConsClosureAtFreshVariable`) for the LIFTED-open codomain — the binder-child
position of the substituted cell's spine. -/
theorem TelescopeReducible.substitutedTwoChildrenStronglyNormalizing
    {baseScope targetScope : Nat} {flag : UniverseFlag}
    {substitution : RawTermSubst baseScope (targetScope + 1)}
    {domainCode : RawTerm baseScope} {codomainCode : RawTerm (baseScope + 1)}
    {domainLevel codomainLevel : LevelExpr} (predLevel : Nat)
    (telescope : TelescopeReducible flag 0 2 substitution [domainLevel, codomainLevel]
      (.childCons domainCode (.childCons codomainCode .childNil))) :
    IsStronglyNormalizing (RawTerm.subst substitution domainCode) ∧
      IsStronglyNormalizing
        (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) := by
  obtain ⟨headMember, tailClosure⟩ := telescope
  refine ⟨(headMember 0).stronglyNormalizing, ?_⟩
  exact IsStronglyNormalizing.liftedSubstOfConsClosureAtFreshVariable
    (headMember (predLevel + 1))
    (fun argument argumentMember => (tailClosure argument argumentMember).1 predLevel)

/-- **The substituted unary spine is all-SN** — `allStronglyNormalizing` of the literal spine
the substituted cell stores, the exact input of `formerCellStronglyNormalizingOfChildren`. -/
theorem TelescopeReducible.substitutedOneChildSpineStronglyNormalizing
    {baseScope targetScope : Nat} {flag : UniverseFlag}
    {substitution : RawTermSubst baseScope (targetScope + 1)}
    {elementCode : RawTerm baseScope} {elementLevel : LevelExpr}
    (telescope : TelescopeReducible flag 0 1 substitution [elementLevel]
      (.childCons elementCode .childNil)) :
    RawTermChildren.allStronglyNormalizing
      ((RawTermChildren.childCons (RawTerm.subst substitution elementCode)
        RawTermChildren.childNil : RawTermChildren [0] (targetScope + 1))) :=
  ⟨telescope.substitutedOneChildStronglyNormalizing, True.intro⟩

/-- **The substituted binary spine is all-SN** — the Π/Σ-shaped twin, with the codomain at the
lifted position. -/
theorem TelescopeReducible.substitutedTwoChildSpineStronglyNormalizing
    {baseScope targetScope : Nat} {flag : UniverseFlag}
    {substitution : RawTermSubst baseScope (targetScope + 1)}
    {domainCode : RawTerm baseScope} {codomainCode : RawTerm (baseScope + 1)}
    {domainLevel codomainLevel : LevelExpr} (predLevel : Nat)
    (telescope : TelescopeReducible flag 0 2 substitution [domainLevel, codomainLevel]
      (.childCons domainCode (.childCons codomainCode .childNil))) :
    RawTermChildren.allStronglyNormalizing
      ((RawTermChildren.childCons (RawTerm.subst substitution domainCode)
        (RawTermChildren.childCons
          (RawTerm.subst (RawTermSubst.lift substitution) codomainCode)
          RawTermChildren.childNil) : RawTermChildren [0, 1] (targetScope + 1))) :=
  ⟨(telescope.substitutedTwoChildrenStronglyNormalizing predLevel).1,
   (telescope.substitutedTwoChildrenStronglyNormalizing predLevel).2, True.intro⟩

end FX1Poly.Typed
