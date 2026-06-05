import FX1Poly.Typed.GrownCanonicalFormsByClassifier
import FX1Poly.Typed.HasTypeDescClosedForms
import FX1Poly.Typed.WfContext

/-! # FX1Poly/Typed/GrownCanonicalFormsNonVacuity — the canonical-forms-per-type theorems are NON-VACUOUS

`GrownCanonicalFormsByClassifier` proved canonical forms PER TYPE — `closedNormalFunctionIsLambda` (a closed
normal Π-typed term is a λ) and `closedNormalTypeIsFormer` (a closed normal universe-typed term is a type
former).  Both are `∀`-statements; a degenerate engine that types NOTHING at a Π / universe would make them
vacuously true.  This file rules that out, exhibiting CONCRETE closed witnesses that satisfy each theorem's
hypotheses and feeding them through, so the theorems demonstrably FIRE on real input — the honest counterpart to
the abstract canonical-forms lemmas, and the first NAMED concrete closed POSITIVE typing derivations in the
grown engine (the complement to the `GrownEngineHonesty` 0-false-positive corpus, which exhibits cells with NO
derivation).

  * `closedUniverseCodeTyping` — `Type@s : Type@(s+1)` at the empty context, by `universeFormation` bridged into
    the grown engine.  A closed term inhabiting a universe.
  * `closedIdentityLambdaTyping` — the identity `λ (x : Type@s). x : Π (Type@s). Type@s` at the empty context,
    by `piIntro` (domain + codomain by `universeFormation`, body by the `var` rule).  A closed term inhabiting a
    Π type — the scope-0 closed analogue of `OpenSNSmoke.openIdentityLambda`.
  * `closedNormalTypeIsFormer_nonVacuous` — there EXISTS a closed normal term inhabiting a universe whose head is
    a type former: `Type@0` itself, fed through `closedNormalTypeIsFormer`.  The universe-classifier theorem is
    not vacuous.
  * `closedNormalFunctionIsLambda_nonVacuous` — there EXISTS a closed normal term inhabiting a Π type that is a
    λ: the identity `λ (x : Type@0). x`, fed through `closedNormalFunctionIsLambda`.  The Π-classifier theorem is
    not vacuous.

The concrete level is `Type@0` (`LevelExpr.lzero`) with the `standard` flag, so the normal-form side conditions
discharge by `decide` on a fully-closed term.  Both non-vacuity theorems bundle the typing derivation into the
existential, so the `profile` is threaded through `HasTypeDescPi profile …`.

## Zero-axiom verification

The typing derivations are concrete `universeFormation` / `piIntro` / `var` compositions; the normal-form side
conditions are `by decide` on closed cells; the canonical-forms theorems are applied directly.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (verified by `#print axioms` in scratch
before landing).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Closed universe-code typing.**  `Type@s : Type@(s+1)` at the empty context, by the universe-formation rule
bridged into the grown engine — a concrete closed term inhabiting a universe. -/
def closedUniverseCodeTyping {profile : PolyProfile} (subjectLevel : LevelExpr) (flag : UniverseFlag) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell subjectLevel flag) (universeCodeCell subjectLevel.lsucc flag) :=
  HasTypeDesc.toHasTypeDescPi
    (HasType.toHasTypeDesc
      (HasType.universeFormation (TypingContext.empty : TypingContext profile 0) subjectLevel flag))

/-- **Closed identity-lambda typing.**  `λ (x : Type@s). x : Π (Type@s). Type@s` at the empty context, by
`piIntro` (domain + codomain by `universeFormation`, body by the `var` rule) — a concrete closed term inhabiting
a Π type.  The scope-0 closed analogue of `OpenSNSmoke.openIdentityLambda_stronglyNormalizing`. -/
def closedIdentityLambdaTyping {profile : PolyProfile} (subjectLevel : LevelExpr) (flag : UniverseFlag) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (piTyCodeCell (universeCodeCell subjectLevel flag) (universeCodeCell subjectLevel flag)) :=
  HasTypeDescPi.piIntro
    (context := (TypingContext.empty : TypingContext profile 0))
    (domainCode := universeCodeCell subjectLevel flag)
    (codomainCode := universeCodeCell subjectLevel flag)
    (body := variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
    (domainLevel := subjectLevel.lsucc) (codomainLevel := subjectLevel.lsucc) (flag := flag)
    (HasTypeDesc.toHasTypeDescPi
      (HasType.toHasTypeDesc (HasType.universeFormation _ subjectLevel flag)))
    (HasTypeDesc.toHasTypeDescPi
      (HasType.toHasTypeDesc (HasType.universeFormation _ subjectLevel flag)))
    (HasTypeDesc.toHasTypeDescPi
      (HasType.toHasTypeDesc (HasType.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))))

/-- **`closedNormalTypeIsFormer` is non-vacuous.**  There EXISTS a closed normal term inhabiting a universe whose
head is a type former — `Type@0`, typed at `Type@1` by `closedUniverseCodeTyping` and fed through
`closedNormalTypeIsFormer`.  The universe-classifier canonical-forms theorem fires on real input. -/
theorem closedNormalTypeIsFormer_nonVacuous {profile : PolyProfile} :
    ∃ (subject : RawTerm 0) (classifierLevel : LevelExpr) (classifierFlag : UniverseFlag),
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (universeCodeCell classifierLevel classifierFlag) ∧
      RawTerm.isStepNormalForm subject ∧
      (RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
       RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
       RawTerm.headGenerator subject = Generator.gen_universeCode) := by
  refine ⟨universeCodeCell LevelExpr.lzero UniverseFlag.standard, _, _,
    closedUniverseCodeTyping (profile := profile) LevelExpr.lzero UniverseFlag.standard, by decide, ?_⟩
  exact HasTypeDescPi.closedNormalTypeIsFormer
    (closedUniverseCodeTyping (profile := profile) LevelExpr.lzero UniverseFlag.standard) (by decide)

/-- **`closedNormalFunctionIsLambda` is non-vacuous.**  There EXISTS a closed normal term inhabiting a Π type
that is a λ — the identity `λ (x : Type@0). x`, typed at `Π (Type@0). Type@0` by `closedIdentityLambdaTyping` and
fed through `closedNormalFunctionIsLambda`.  The Π-classifier canonical-forms theorem fires on real input. -/
theorem closedNormalFunctionIsLambda_nonVacuous {profile : PolyProfile} :
    ∃ (subject : RawTerm 0) (outerDomain : RawTerm 0) (outerCodomain : RawTerm 1),
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (piTyCodeCell outerDomain outerCodomain) ∧
      RawTerm.isStepNormalForm subject ∧
      (∃ body : RawTerm 1, subject = lamCell body) := by
  refine ⟨lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)), _, _,
    closedIdentityLambdaTyping (profile := profile) LevelExpr.lzero UniverseFlag.standard, by decide, ?_⟩
  exact HasTypeDescPi.closedNormalFunctionIsLambda
    (closedIdentityLambdaTyping (profile := profile) LevelExpr.lzero UniverseFlag.standard) (by decide)

end FX1Poly.Typed
