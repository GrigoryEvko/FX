import FX1Poly.Typed.GrownCanonicalFormsNonVacuity
import FX1Poly.Typed.HasTypeDescPiBetaSR

/-! # FX1Poly/Typed/GrownBetaRedexInAction — type safety in action on a concrete reducing closed term

`GrownCanonicalFormsNonVacuity` exhibited concrete closed witnesses for the canonical-forms theorems, but all
were NORMAL forms — they do not reduce.  This file closes the loop with a concrete closed term that actually
REDUCES, threading it through the whole safety pipeline (Π-elimination typing, the real `Step.beta`,
preservation via `betaSubjectReduction`, and canonical forms) so progress + preservation + canonicity are seen
firing TOGETHER on one term.  The witness is the application of the identity to a type:
`(λ (x : Type@1). x) (Type@0)`.

  * `closedIdentityAppRedexTyping` — the redex `(λ (x : Type@1). x) (Type@0)` is typed at `Type@1` at the empty
    context, by `piElim` over the shipped `closedIdentityLambdaTyping` (the function) and `closedUniverseCodeTyping`
    (the argument `Type@0 : Type@1`).  The piElim result classifier `subst0 (Type@1) (Type@0)` is `Type@1` (the
    codomain is constant), so the redex inhabits `Type@1`.

  * `closedIdentityAppRedex_betaStep` — the β-redex actually fires: `Step` carries it to `Type@0`
    (`subst0 (var 0) (Type@0)` is `Type@0`, the body being the bound variable), by `Step.beta` directly.

  * `closedIdentityAppRedex_safety` — TYPE SAFETY IN ACTION: the reduct `Type@0` is STILL typed at `Type@1`
    (PRESERVATION, by `betaSubjectReduction` on the redex), and it is a CANONICAL VALUE (a type former, by
    `closedNormalTypeIsFormer`).  The concrete instantiation of "a well-typed term steps to a well-typed value of
    the same type" — progress, preservation, and canonical forms on one reducing closed term.

This complements the abstract safety statements (`GrownTypeSafety`) and the non-reducing non-vacuity witnesses
(`GrownCanonicalFormsNonVacuity`): here the term genuinely reduces, `Step.beta` genuinely fires, and
`betaSubjectReduction` is genuinely exercised end-to-end.  `#672`-independent.

## Zero-axiom verification

`piElim` over the two shipped concrete typing derivations; `Step.beta` directly (the `subst0` of a bound variable
computes to the argument); `betaSubjectReduction` + `closedNormalTypeIsFormer`; the normal-form side condition is
`by decide` on the closed reduct.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The concrete closed β-redex, typed.**  `(λ (x : Type@1). x) (Type@0) : Type@1` at the empty context, by
`piElim` over `closedIdentityLambdaTyping` (the identity at `Type@1`) and `closedUniverseCodeTyping` (the argument
`Type@0 : Type@1`).  The piElim output `subst0 (Type@1) (Type@0)` is `Type@1` (constant codomain). -/
def closedIdentityAppRedexTyping {profile : PolyProfile} :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
  HasTypeDescPi.piElim
    (closedIdentityLambdaTyping (profile := profile) LevelExpr.lzero.lsucc UniverseFlag.standard)
    (closedUniverseCodeTyping (profile := profile) LevelExpr.lzero UniverseFlag.standard)

/-- **The β-redex fires.**  `(λ (x : Type@1). x) (Type@0)` `Step`s to `Type@0`: the β-contractum
`subst0 (var 0) (Type@0)` is `Type@0` (the body is the bound variable), so `Step.beta` applies directly. -/
theorem closedIdentityAppRedex_betaStep :
    Step (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard) : RawTerm 0)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  Step.beta

/-- **Type safety in action.**  After the redex `(λ (x : Type@1). x) (Type@0) : Type@1` β-reduces to `Type@0`,
PRESERVATION holds — the reduct `Type@0` is still typed at `Type@1` (by `betaSubjectReduction`) — and the reduct
is a CANONICAL VALUE — a type former (by `closedNormalTypeIsFormer`).  The concrete instantiation of progress +
preservation + canonical forms on one reducing closed term: a well-typed term steps to a well-typed value of the
same type. -/
theorem closedIdentityAppRedex_safety {profile : PolyProfile} :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) ∧
    (RawTerm.headGenerator (universeCodeCell LevelExpr.lzero UniverseFlag.standard : RawTerm 0)
        = Generator.gen_piTyCode ∨
      RawTerm.headGenerator (universeCodeCell LevelExpr.lzero UniverseFlag.standard : RawTerm 0)
        = Generator.gen_sigmaTyCode ∨
      RawTerm.headGenerator (universeCodeCell LevelExpr.lzero UniverseFlag.standard : RawTerm 0)
        = Generator.gen_universeCode) := by
  have reductTyped :
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
        (RawTerm.subst0 (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
        (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
    HasTypeDescPi.betaSubjectReduction closedIdentityAppRedexTyping WfContext.emptyIsWellFormed
  refine ⟨reductTyped, ?_⟩
  exact HasTypeDescPi.closedNormalTypeIsFormer reductTyped (by decide)

end FX1Poly.Typed
