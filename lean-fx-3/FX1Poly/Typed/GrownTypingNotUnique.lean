import FX1Poly.Typed.GrownCanonicalFormsNonVacuity
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/GrownTypingNotUnique
    — the grown engine's typing is NOT unique (Curry-style λ): a metatheory guard

The formation engine has uniqueness of typing (`HasType.uniqueness`: `Γ ⊢ t : T₁` and `Γ ⊢ t : T₂` force
`Conv T₁ T₂`) because it types only formation subjects (var / conv / universe / formers), none of which is a
domain-free binder.  It is tempting to conjecture the GROWN engine `HasTypeDescPi` inherits uniqueness.  **It does
not.**  This file records the refutation as a permanent theorem so the conjecture is not re-attempted.

The grown `lamCell body` is **Curry-style** — a one-child cell carrying only the body, with NO domain annotation.
The `piIntro` rule chooses the domain freely, so the SAME closed identity `λ(var 0)` types at `Π(Type@s).Type@s`
for EVERY level `s` (this is exactly what the shipped `closedIdentityLambdaTyping` witnesses, parameterically in
`s`).  Picking two different levels gives one subject with two classifiers that are NOT convertible — uniqueness
fails.

  * `grownTypingNotUnique` — there exist a closed subject and two classifiers, each typing it in the grown engine,
    that are not `Conv`: the identity `λ(var 0)` typed at `Π(Type@0).Type@0` and at `Π(Type@1).Type@1`.  The two
    Π-codes are refuted convertible by `Conv.piTyCode_inj` (the SHIPPED Π-injectivity — itself a pure
    raw-confluence corollary, `StepStar.shapeStable_piTyCode` + `piTyCodeCell_inj`, independent of the SR /
    context-conversion bundle) composed with `universeCodeCell_inj_of_conv` + the predicativity guard
    `LevelExpr.ne_lsucc_self`.

## Why this matters (the design record)

This closes a spike on whether grown uniqueness is "the live engine's missing metatheorem."  Verdict: Π/Σ-code
injectivity (`Conv.piTyCode_inj` / `…sigmaTyCode_inj`) is already shipped and IS separable from the GCC-5 mutual
bundle (confirming it is a free confluence corollary); but grown FULL uniqueness is genuinely false under
Curry-style binders, so the bidirectional checker SYNTHESIZES against a target (check mode), it does not infer a
unique type for a bare λ.  Any future "exact classifier" result must restrict to TYPE-CODE subjects (where the
classifier is pinned by the formers' levels), not bare introduction forms.

## Zero-axiom verification

Two instances of the shipped `closedIdentityLambdaTyping` at levels `0` and `1`; the non-convertibility is
`Conv.piTyCode_inj` (confluence-backed) → `universeCodeCell_inj_of_conv` (confluence + cell injectivity) →
`LevelExpr.ne_lsucc_self` (size-free predicativity).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The grown engine's typing is not unique.**  There exist a closed subject and two non-convertible classifiers
each typing it: the Curry-style identity `λ(var 0)` is typed at both `Π(Type@0).Type@0` and `Π(Type@1).Type@1` (by
`closedIdentityLambdaTyping` at levels `0` and `1` — the domain is chosen freely by `piIntro`, the cell carries no
annotation).  The two Π-codes are not `Conv`: `Conv.piTyCode_inj` would force `Conv (Type@0) (Type@1)`, hence
`lzero = lsucc lzero` (`universeCodeCell_inj_of_conv`), refuted by `LevelExpr.ne_lsucc_self`.  The permanent guard
against the (false) grown-uniqueness conjecture — proven via the shipped Π-injectivity. -/
theorem grownTypingNotUnique {profile : PolyProfile} :
    ∃ (subject classifier₁ classifier₂ : RawTerm 0),
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier₁ ∧
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier₂ ∧
      ¬ Conv classifier₁ classifier₂ := by
  refine ⟨lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)),
    piTyCodeCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard),
    piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard),
    closedIdentityLambdaTyping LevelExpr.lzero UniverseFlag.standard,
    closedIdentityLambdaTyping LevelExpr.lzero.lsucc UniverseFlag.standard,
    ?_⟩
  intro convClassifiers
  obtain ⟨convDomains, _convCodomains⟩ := Conv.piTyCode_inj convClassifiers
  exact absurd (universeCodeCell_inj_of_conv convDomains).1 (LevelExpr.ne_lsucc_self LevelExpr.lzero)

end FX1Poly.Typed
