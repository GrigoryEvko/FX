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

/-! ## Curried 2-argument application — parametric polymorphism in action

The instantiation above stops at the type-application: `(ΛA. λx. x) (Type@0)` is the
SPECIALIZED identity, but it cannot then be applied to a value, because `Type@0` has
no closed inhabitant.  Climbing ONE more universe fixes this: the LEVEL-2 polymorphic
identity `Λ(A : Type@2). λ(x : A). x`, instantiated at `Type@1`, yields the identity on
`Type@1` (`Π(x : Type@1). Type@1`), which DOES accept the closed value `Type@0 : Type@1`.
So the curried application `(Λ(A : Type@2). λ(x : A). x) (Type@1) (Type@0)` typechecks
end-to-end — the first ARGUMENT instantiates the polymorphic `A`, the second is the
actual value passed to the specialized identity — and reduces in TWO β-steps (an inner
contraction under the outer application's function position, then the outer β) to the
value `Type@0`.  This is parametric polymorphism exercised in full: instantiate, then
apply. -/

/-- In context `[A : Type@2]`, `Π(x : A). A` is a type at `Type@(lmax 2 2)` — the level-2
twin of `dependentArrowOverTypeVariableAtLevelOne_hasTypeDescPi` (child levels bumped to
`lzero.lsucc.lsucc`). -/
theorem dependentArrowOverTypeVariableAtLevelTwo_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero.lsucc.lsucc flag))
      (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc.lsucc, LevelExpr.lzero.lsucc.lsucc]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero.lsucc.lsucc, LevelExpr.lzero.lsucc.lsucc] flag
    { outputType := universeFormerOutput } rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    · exact DescTelescopePi.nil _ _

/-- The LEVEL-2 polymorphic identity `λ(A : Type@2). λ(x : A). x` is typed at
`Π(A : Type@2). Π(x : A). A` — the level-2 twin of `polymorphicIdentityAtLevelOne_hasType
DescPi` (same term; the type-variable universe climbs to `Type@2` so that instantiating at
`Type@1` leaves room to apply the result to `Type@0 : Type@1`). -/
theorem polymorphicIdentityAtLevelTwo_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc.lsucc flag)
        (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))) := by
  refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc.lsucc.lsucc
    (lmaxAll [LevelExpr.lzero.lsucc.lsucc, LevelExpr.lzero.lsucc.lsucc]) flag
    ?domainTyped ?codomainTyped ?bodyTyped
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero.lsucc.lsucc flag)
  · exact dependentArrowOverTypeVariableAtLevelTwo_hasTypeDescPi flag
  · refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc.lsucc LevelExpr.lzero.lsucc.lsucc flag
      ?innerDomainTyped ?innerCodomainTyped ?innerBodyTyped
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 1⟩ : Fin 2))

/-- The level-2 polymorphic identity instantiated at `Type@1` — `(Λ(A : Type@2). λ(x : A).
x) (Type@1)` is typed at `Π(x : Type@1). Type@1`, the identity on `Type@1` (the `piElim`
result `subst0 (Π(x : A). A) Type@1` specializes by defeq).  The intermediate partial
application of the curried use below. -/
theorem polymorphicIdentityInstantiatedAtTypeOne_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero.lsucc flag))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc flag)
        (universeCodeCell LevelExpr.lzero.lsucc flag)) :=
  HasTypeDescPi.piElim
    (polymorphicIdentityAtLevelTwo_hasTypeDescPi (profile := profile) flag)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero.lsucc flag))

/-- ★ The CURRIED 2-ARGUMENT application `(Λ(A : Type@2). λ(x : A). x) (Type@1) (Type@0)` is
typed at `Type@1` — a nested `piElim`: the first argument `Type@1` instantiates the
polymorphic `A` (giving the identity on `Type@1`), the second argument `Type@0 : Type@1` is
the actual value.  The outer `piElim` result `subst0 Type@1 Type@0` is defeq `Type@1` (the
specialized identity's codomain is the constant `Type@1`).  Parametric polymorphism applied
in full: instantiate, then apply. -/
theorem polymorphicIdentityAppliedToTypeOneThenTypeZero_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (appCell (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero.lsucc flag)) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell LevelExpr.lzero.lsucc flag) :=
  HasTypeDescPi.piElim
    (polymorphicIdentityInstantiatedAtTypeOne_hasTypeDescPi (profile := profile) flag)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- ★ The curried application reduces in TWO β-steps to the value `Type@0`: first a
CONGRUENCE step contracts the inner type-application `(ΛA. λx. x) (Type@1) ↝ λx. x` under
the outer application's function position (`Step.cong .gen_app` + `StepChildren.here`),
leaving `(λx. x) (Type@0)`; then the outer β contracts that to `Type@0` (`subst0 (var 0)
Type@0 = Type@0`). -/
theorem polymorphicIdentityTwoArgReducesToTypeZero (flag : UniverseFlag) :
    StepStar
      (appCell (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero.lsucc flag)) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell LevelExpr.lzero flag) :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here
        (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons (universeCodeCell LevelExpr.lzero flag) .childNil) : RawTermChildren [0] 0)
        Step.beta))
    (StepStar.trans Step.beta (StepStar.refl _))

/-- ★ Subject reduction for the curried 2-argument application.  The redex
`(Λ(A : Type@2). λ(x : A). x) (Type@1) (Type@0)` reduces (in two β-steps) to the value
`Type@0`, and BOTH the redex and the reduct are typed at the SAME type `Type@1` (the reduct
`Type@0 : Type@1` by universe formation).  Curried polymorphic application followed by a
multi-step reduction, with the type preserved end-to-end. -/
theorem polymorphicIdentityTwoArg_subjectReduction
    {profile : PolyProfile} (flag : UniverseFlag) :
    StepStar
      (appCell (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero.lsucc flag)) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell LevelExpr.lzero flag) ∧
    HasTypeDescPi profile TypingContext.empty
      (appCell (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero.lsucc flag)) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell LevelExpr.lzero.lsucc flag) ∧
    HasTypeDescPi profile TypingContext.empty
      (universeCodeCell LevelExpr.lzero flag)
      (universeCodeCell LevelExpr.lzero.lsucc flag) :=
  ⟨polymorphicIdentityTwoArgReducesToTypeZero flag,
    polymorphicIdentityAppliedToTypeOneThenTypeZero_hasTypeDescPi (profile := profile) flag,
    HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)⟩

/-- The curried 2-argument application is strongly normalizing — SN-043 on the concrete
nested-`piElim` derivation. -/
theorem polymorphicIdentityTwoArg_stronglyNormalizing
    {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (appCell (appCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
        (universeCodeCell LevelExpr.lzero.lsucc flag)) (universeCodeCell LevelExpr.lzero flag)
        : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing
    (polymorphicIdentityAppliedToTypeOneThenTypeZero_hasTypeDescPi (profile := profile) flag)

/-! ## Dependent PAIR-type formation — the generic `genFormationPi` arm types Σ, not only Π

Every derivation above heads a Π former (`piTyCodeCell`).  But the engine's
generic `genFormationPi` arm is FORMER-AGNOSTIC: it dispatches through
`typingRuleDescOf`, whose `gen_sigmaTyCode` row carries the SAME
`{ outputType := universeFormerOutput }` payload as the `gen_piTyCode` row.  So
the identical proof script — `genFormationPi _ <generator> () _ <levels> flag
{ outputType := universeFormerOutput } rfl` followed by a two-entry
`DescTelescopePi` premise — types a dependent PAIR type `Σ(x : A). A` by swapping
ONLY the `Generator` argument from `.gen_piTyCode` to `.gen_sigmaTyCode`.  These
are the first Σ-FORMATION derivations in the TYPING ENGINE (`HasTypeDescPi`); the
closed-SN smoke corpus exercises Σ only through the LEVEL-INDEXED reducibility
layer (`fundamentalSigmaFormationLevelIndexed`), never the typing judgment. -/

/-- In context `[A : Type@0]`, the dependent pair type `Σ(x : A). A` (codes
`sigmaTyCodeCell (var 0) (var 1)`) is a type at `Type@(lmax 0 0)` — the Σ twin of
`dependentArrowOverTypeVariable_hasTypeDescPi`, via the SAME `genFormationPi` arm
with `.gen_sigmaTyCode` in place of `.gen_piTyCode`.  The `DescTelescopePi`
premise types the domain `A` (= `var 0`) and the shifted codomain `A` (= `var 1`)
each at `Type@0` by the `var` rule. -/
theorem dependentPairTypeOverTypeVariable_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
      (sigmaTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (universeCodeCell (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_sigmaTyCode () _
    [LevelExpr.lzero, LevelExpr.lzero] flag { outputType := universeFormerOutput }
    rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    · exact DescTelescopePi.nil _ _

/-- A CLOSED dependent pair type `Σ(_ : Type@0). Type@0` (codes
`sigmaTyCodeCell (universeCode 0) (universeCode 0)`) is a type at
`Type@(lmax (0+1) (0+1))`, typed by the same `genFormationPi` arm at the
`gen_sigmaTyCode` row — the Σ twin of the closed Π formations above.  Each
universe-code component is typed by `universeFormation` (`Type@0 : Type@1`), so
the telescope premises live one level up, exactly as in the Π case. -/
theorem closedDependentPairType_hasTypeDescPi
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (sigmaTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_sigmaTyCode () _
    [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc] flag { outputType := universeFormerOutput }
    rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation (TypingContext.empty.cons _) LevelExpr.lzero flag)
    · exact DescTelescopePi.nil _ _

/-- The closed dependent pair type is strongly normalizing — SN-043 on the
concrete `genFormationPi` Σ derivation. -/
theorem closedDependentPairType_stronglyNormalizing
    {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (sigmaTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag) : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing
    (closedDependentPairType_hasTypeDescPi (profile := profile) flag)

/-- ★ The generic `genFormationPi` arm types BOTH the Π and the Σ former at one
identical context and output classifier — the two conjuncts differ ONLY in the
head former (`piTyCodeCell` vs `sigmaTyCodeCell`), hence ONLY in the `Generator`
argument fed to the same arm (`.gen_piTyCode` vs `.gen_sigmaTyCode`).  This is the
cascade-free typing thesis made concrete: a new type former is a
`typingRuleDescOf` table ROW, never a new `HasTypeDescPi` constructor. -/
theorem genFormationPiTypesBothPiAndSigmaFormers
    {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
        (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
        (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
        (universeCodeCell (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag)
      ∧
    HasTypeDescPi profile
        (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
        (sigmaTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
        (universeCodeCell (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag) :=
  ⟨dependentArrowOverTypeVariable_hasTypeDescPi flag,
   dependentPairTypeOverTypeVariable_hasTypeDescPi flag⟩

end FX1Poly.Typed
