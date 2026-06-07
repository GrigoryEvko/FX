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

Zero-axiom: every derivation is a direct constructor application; the only
non-trivial steps are the `var`-lookup defeq and the constant-codomain `subst0`,
both of which hold by computation on nullary leaves.
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

end FX1Poly.Typed
