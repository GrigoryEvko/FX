import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.ClosedSNSmoke
import FX1Poly.Typed.ClosedStronglyNormalizing

/-! # Foundation/PolyCell/Typed/TypedLambdaDerivations
    - concrete `HasTypeDescPi` typing-engine derivations of real λ-terms

The closed-SN smoke corpus (`ClosedSNSmoke.lean`) exercises the LEVEL-INDEXED
fundamental theorem (`fundamentalPiIntroLevelIndexed` and friends) — the
reducibility/SN machinery — on closed terms.  This file is complementary: it
exhibits concrete derivations of the actual TYPING JUDGMENT `HasTypeDescPi` for
honest-to-goodness λ-abstractions, exercising the grown engine's `piIntro`
constructor end-to-end (with the variable rule and universe-formation routed
through `ofFormation`).  These are the first concrete witnesses that the grown
engine *types real programs* — λ-terms, not only type-former formation cells.

Two derivations, both generic over the universe level and flag:

  * `identityOnUniverse_hasTypeDescPi` — the identity `λ(x : Type@e). x` is typed
    at `Π(x : Type@e). Type@e`.  The body `x` types by the `var` rule, whose
    classifier `(empty.cons Type@e).lookup 0 = rename weaken Type@e` is
    definitionally `Type@e` (a nullary universe-code leaf renames to itself), so
    it matches the `piIntro` codomain with no coercion.

  * `constantTypeLambda_hasTypeDescPi` — the constant function
    `λ(x : Type@e). Type@e` is typed at `Π(x : Type@e). Type@(e+1)`, exercising
    `piIntro` with a body (`Type@e : Type@(e+1)`) that ignores the bound
    variable.

And one bridge to the metatheory:

  * `identityOnUniverse_stronglyNormalizing` — feeding the concrete identity
    derivation through SN-043 (`HasTypeDescPi.closedStronglyNormalizing`) yields
    `IsStronglyNormalizing` for the λ-term, demonstrating the
    typing → strong-normalization pipeline on a concrete closed program.

And the elimination (application) form, with a concrete subject-reduction
witness:

  * `identityApplicationOnUniverseCode_hasTypeDescPi` — applying the identity at
    `Type@(e+1)` to the universe code `Type@e` (which inhabits `Type@(e+1)`),
    typed by `piElim`.  The result type `subst0 Type@(e+1) Type@e` is
    definitionally `Type@(e+1)` (the constant codomain ignores the argument).

  * `identityApplication_subjectReduction` — the redex β-reduces to its argument
    `Type@e`, and BOTH the redex and the reduct are typed at the same type
    `Type@(e+1)` — concrete subject reduction for an honest application.

And the capstone — the canonical dependently-typed term:

  * `polymorphicIdentity_hasTypeDescPi` — `λ(A : Type@0). λ(x : A). x` is typed at
    `Π(A : Type@0). Π(x : A). A`, via NESTED `piIntro` with a type-VARIABLE inner
    domain.  The outer codomain `Π(x : A). A` is a genuine Π-FORMATION with
    variable children (`dependentArrowOverTypeVariable_hasTypeDescPi`, through
    `genFormationPi` + a `DescTelescopePi` typing `A` and its shift each at
    `Type@0` by the `var` rule).  `polymorphicIdentity_stronglyNormalizing`
    feeds it through SN-043.

Zero-axiom: every derivation is a direct constructor application; the only
non-trivial steps are the `var`-lookup defeqs (a nullary universe-code leaf and
its iterated weakenings all reduce to `Type@0`; a value variable's weakening
reduces to the next de Bruijn index) and the constant-codomain `subst0`, all of
which hold by computation.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe
open StepStar

/-- `λ(x : Type@e). x : Π(x : Type@e). Type@e` — the identity on the universe
`Type@e`, typed end-to-end by the grown engine's `piIntro`.  The body `x` types
by the `var` rule (through `ofFormation`); its lookup classifier `rename weaken
Type@e` is definitionally `Type@e`, matching the codomain. -/
theorem identityOnUniverse_hasTypeDescPi
    {profile : PolyProfile} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (piTyCodeCell (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr flag)) :=
  HasTypeDescPi.piIntro levelExpr.lsucc levelExpr.lsucc flag
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty levelExpr flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation (TypingContext.empty.cons _) levelExpr flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (TypingContext.empty.cons _) (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

/-- `λ(x : Type@e). Type@e : Π(x : Type@e). Type@(e+1)` — a constant
type-returning function whose body ignores the bound variable, typed end-to-end
by `piIntro`.  Both the codomain `Type@(e+1)` and the body `Type@e` type by
`universeFormation`; the body's classifier `Type@(e+1)` matches the Π codomain. -/
theorem constantTypeLambda_hasTypeDescPi
    {profile : PolyProfile} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (universeCodeCell levelExpr flag))
      (piTyCodeCell (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc flag)) :=
  HasTypeDescPi.piIntro levelExpr.lsucc levelExpr.lsucc.lsucc flag
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty levelExpr flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation (TypingContext.empty.cons _)
        levelExpr.lsucc flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation (TypingContext.empty.cons _) levelExpr flag))

/-- The concrete identity derivation, fed through SN-043
(`HasTypeDescPi.closedStronglyNormalizing`), yields strong normalization for the
λ-term — the typing → strong-normalization pipeline exercised on a concrete
closed program. -/
theorem identityOnUniverse_stronglyNormalizing
    {profile : PolyProfile} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing
    (identityOnUniverse_hasTypeDescPi (profile := profile) levelExpr flag)

/-- `(λ(x : Type@(e+1)). x) (Type@e) : Type@(e+1)` — the identity at the universe
`Type@(e+1)` applied to the universe code `Type@e` (which inhabits `Type@(e+1)`),
typed by the grown engine's `piElim`.  The result type `subst0 Type@(e+1) Type@e`
is definitionally `Type@(e+1)`: the identity's codomain is constant, so the
substitution ignores the argument. -/
theorem identityApplicationOnUniverseCode_hasTypeDescPi
    {profile : PolyProfile} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell levelExpr flag))
      (universeCodeCell levelExpr.lsucc flag) :=
  HasTypeDescPi.piElim
    (identityOnUniverse_hasTypeDescPi (profile := profile) levelExpr.lsucc flag)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty levelExpr flag))

/-- The identity application β-reduces to its argument `Type@e` (the body `x`
substituted by the argument). -/
theorem identityApplicationOnUniverseCode_betaReducesToArgument
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    Step
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell levelExpr flag))
      (universeCodeCell levelExpr flag) :=
  Step.beta

/-- ★ Concrete subject reduction for an honest application.  The identity
application `(λ(x : Type@(e+1)). x) (Type@e)` β-reduces to its argument `Type@e`,
and BOTH the redex and the reduct are typed at the SAME type `Type@(e+1)` — the
β-step preserves the type.  This is subject reduction exhibited on a concrete
closed `piElim` derivation, not a general lemma. -/
theorem identityApplication_subjectReduction
    {profile : PolyProfile} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    Step
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell levelExpr flag))
      (universeCodeCell levelExpr flag) ∧
    HasTypeDescPi profile TypingContext.empty
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell levelExpr flag))
      (universeCodeCell levelExpr.lsucc flag) ∧
    HasTypeDescPi profile TypingContext.empty
      (universeCodeCell levelExpr flag)
      (universeCodeCell levelExpr.lsucc flag) :=
  ⟨identityApplicationOnUniverseCode_betaReducesToArgument levelExpr flag,
    identityApplicationOnUniverseCode_hasTypeDescPi (profile := profile) levelExpr flag,
    HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty levelExpr flag)⟩

/-- In context `[A : Type@0]`, the dependent function type `Π(x : A). A` (codes
`piTyCodeCell (var 0) (var 1)`) is a type at `Type@(lmax 0 0)` — a Π-FORMATION
with VARIABLE children, via `genFormationPi`.  The `DescTelescopePi` premise
types the domain `A` (= `var 0`) and the shifted codomain `A` (= `var 1`) each at
`Type@0` by the `var` rule; the cumulative-lookup classifiers are definitionally
`Type@0` (a nullary universe-code leaf is fixed by weakening). -/
theorem dependentArrowOverTypeVariable_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
      (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (universeCodeCell (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero, LevelExpr.lzero] flag { outputType := universeFormerOutput }
    rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    · exact DescTelescopePi.nil _ _

/-- ★ The POLYMORPHIC IDENTITY `λ(A : Type@0). λ(x : A). x` is typed at
`Π(A : Type@0). Π(x : A). A` — the canonical dependently-typed term — via nested
`piIntro`.  The outer codomain is the dependent arrow over the type variable
(`dependentArrowOverTypeVariable_hasTypeDescPi`); the inner `λ(x : A). x` types
by `piIntro` with the type-VARIABLE domain `A = var 0`, its body `x = var 0`
classified at `A = var 1` by the `var` rule (its weakened lookup is the next de
Bruijn index). -/
theorem polymorphicIdentity_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))) := by
  refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc
    (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag ?domainTyped ?codomainTyped ?bodyTyped
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)
  · exact dependentArrowOverTypeVariable_hasTypeDescPi flag
  · refine HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero flag
      ?innerDomainTyped ?innerCodomainTyped ?innerBodyTyped
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 1⟩ : Fin 2))

/-- The polymorphic identity is strongly normalizing — SN-043 on the concrete
nested-`piIntro` derivation. -/
theorem polymorphicIdentity_stronglyNormalizing
    {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))) : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing
    (polymorphicIdentity_hasTypeDescPi (profile := profile) flag)

/-! ## Dependent type-instantiation — applying a polymorphic function to a type

`polymorphicIdentity_hasTypeDescPi` types the polymorphic identity but cannot be
APPLIED to a closed argument: its domain is `Type@0`, and the formation-only engine
has NO closed inhabitant of `Type@0` (every typed type is a former needing a
level-0 component, and there is no typed nullary base).  The fix is to climb ONE
universe: the LEVEL-1 polymorphic identity `Λ(A : Type@1). λ(x : A). x` has domain
`Type@1`, which the closed universe code `Type@0` DOES inhabit (`Type@0 : Type@1`
by universe formation).  Instantiating it at `Type@0` is the first DEPENDENT
application whose codomain genuinely depends on the argument — unlike the
identity-application above (and the ID-TOWER family), whose codomain is constant.
The dependent codomain `Π(x : A). A` truly specializes under the substitution. -/

/-- In context `[A : Type@1]`, the dependent function type `Π(x : A). A` is a type
at `Type@(lmax 1 1)` — the level-1 twin of `dependentArrowOverTypeVariable_hasType
DescPi`, with the child levels bumped from `lzero` to `lzero.lsucc`.  The
`DescTelescopePi` premise types the domain `A` (= `var 0`) and shifted codomain `A`
(= `var 1`) each at `Type@1` by the `var` rule. -/
theorem dependentArrowOverTypeVariableAtLevelOne_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero.lsucc flag))
      (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc] flag { outputType := universeFormerOutput }
    rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    · exact DescTelescopePi.nil _ _

/-- The LEVEL-1 polymorphic identity `λ(A : Type@1). λ(x : A). x` is typed at
`Π(A : Type@1). Π(x : A). A` — the level-1 twin of `polymorphicIdentity_hasType
DescPi` (the term is IDENTICAL `λA. λx. x`; only the universe of the type variable
climbs from `Type@0` to `Type@1`, so its domain admits the closed argument
`Type@0`).  Via nested `piIntro` with the type-VARIABLE inner domain. -/
theorem polymorphicIdentityAtLevelOne_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc flag)
        (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))) := by
  refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc.lsucc
    (lmaxAll [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc]) flag
    ?domainTyped ?codomainTyped ?bodyTyped
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero.lsucc flag)
  · exact dependentArrowOverTypeVariableAtLevelOne_hasTypeDescPi flag
  · refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc flag
      ?innerDomainTyped ?innerCodomainTyped ?innerBodyTyped
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 1⟩ : Fin 2))

/-- ★ The DEPENDENT TYPE-INSTANTIATION `(Λ(A : Type@1). λ(x : A). x) (Type@0)` is
typed at `Π(x : Type@0). Type@0` — the monomorphic identity on `Type@0`.  Typed by
`piElim`: the function is the level-1 polymorphic identity, the argument is
`Type@0 : Type@1` (universe formation), and the result type
`subst0 (Π(x : A). A) Type@0` computes by defeq to `Π(x : Type@0). Type@0` — the
dependent codomain genuinely specializes (the bound `A` is replaced by `Type@0` in
BOTH the domain and the body of the inner Π).  The first application witness whose
codomain truly depends on the argument. -/
theorem polymorphicIdentityInstantiatedAtTypeZero_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero flag))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag)) :=
  HasTypeDescPi.piElim
    (polymorphicIdentityAtLevelOne_hasTypeDescPi (profile := profile) flag)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- The instantiation β-reduces to the MONOMORPHIC identity `λx. x`: the inner
lambda `λ(x : A). x` survives `subst0` unchanged (it does not mention `A`), so
`subst0 (λx. x) Type@0` is defeq `λx. x`. -/
theorem polymorphicIdentityInstantiation_betaReducesToIdentity (flag : UniverseFlag) :
    Step
      (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero flag))
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) :=
  Step.beta

/-- ★ Concrete subject reduction for the dependent type-instantiation.  The redex
`(Λ(A : Type@1). λ(x : A). x) (Type@0)` β-reduces to the monomorphic identity
`λx. x`, and BOTH are typed at the SAME type `Π(x : Type@0). Type@0` — the reduct's
typing is `identityOnUniverse_hasTypeDescPi` at level `lzero`.  Dependent
type-application followed by β, with the type preserved end-to-end. -/
theorem polymorphicIdentityInstantiation_subjectReduction
    {profile : PolyProfile} (flag : UniverseFlag) :
    Step
      (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero flag))
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) ∧
    HasTypeDescPi profile TypingContext.empty
      (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero flag))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag)) ∧
    HasTypeDescPi profile TypingContext.empty
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag)) :=
  ⟨polymorphicIdentityInstantiation_betaReducesToIdentity flag,
    polymorphicIdentityInstantiatedAtTypeZero_hasTypeDescPi (profile := profile) flag,
    identityOnUniverse_hasTypeDescPi (profile := profile) LevelExpr.lzero flag⟩

/-- The dependent type-instantiation is strongly normalizing — SN-043 on the
concrete `piElim` derivation. -/
theorem polymorphicIdentityInstantiation_stronglyNormalizing
    {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero flag) : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing
    (polymorphicIdentityInstantiatedAtTypeZero_hasTypeDescPi (profile := profile) flag)

end FX1Poly.Typed
