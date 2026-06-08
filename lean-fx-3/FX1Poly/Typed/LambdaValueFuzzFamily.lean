import FX1Poly.Typed.MetatheoryFuzz
import FX1Poly.Typed.GrownClosedProgressByClassifier
import FX1Poly.Typed.TypedNormalizer

/-! # FX1Poly/Typed/LambdaValueFuzzFamily — a §27.3-L2 fuzz family that evaluates to a FUNCTION value

`MetatheoryFuzz.lean` ships two L2 fuzz families — the identity tower and the constant tower — and both
normalize to the universe code `Type@0` (`FuzzCorpusNormalizes`).  Neither exercises the Π-typed
canonical-forms branch: the value they reach is a TYPE code, never a function.  This file adds the THIRD,
genuinely-distinct family — one whose members evaluate to a `λ` (a function VALUE at a Π type) — so the
fuzz corpus now covers BOTH canonical-forms outcomes (a type code AND a function).

The construction applies a NESTED constant function `λx.λy.Type@0 : Π(Type@1, Π(Type@1, Type@1))` (which
returns the constant lambda `λy.Type@0`, discarding its first argument) to the identity-tower member.  One
β-step erases the argument and exposes the inner `λy.Type@0` — a closed normal function value typed at the
arrow `Π(Type@1, Type@1)`.

  * `arrowType1Type1` / `nestedConstantLambdaTyping` — the new typing infrastructure: the codomain
    formation `Π(Type@1, Type@1) : Type@2` (genFormationPi over two universe-code children — the universe-code
    analogue of `churchNatArrow`) and the doubly-nested constant lambda typed at `Π(Type@1, Π(Type@1, Type@1))`.
  * `metatheoryFuzzLambdaFamily` / `_typed` — the family, each member typed at the arrow `Π(Type@1, Type@1)`.
  * `metatheoryFuzzLambdaFamily_betaStep` / `_reducesToLambdaValue` — each member β-steps in one step to the
    constant lambda value `λy.Type@0` (the argument is discarded).
  * **`metatheoryFuzzLambdaFamily_normalizesToLambda`** — ★ the verified SN-normalizer computes each member to
    `λy.Type@0` (`reachedNormalForm_eq_normalForm` on the single-step reduction).
  * **`metatheoryFuzzLambdaFamily_evaluatesToFunction`** — ★ the distinct content: every member's normal form
    is a `λ` — the family EVALUATES TO A FUNCTION, the Π-typed canonical-forms outcome the universe-code
    families never reach.
  * `metatheoryFuzzLambdaFamily_progress` — progress AT THE FUNCTION TYPE via firing-112's
    `closedFunctionStepsOrIsLambda` (steps or is a λ), exercised in the fuzz corpus; plus
    `_stronglyNormalizing` (SN-043).

## Zero-axiom verification

`genFormationPi` + nested `piIntro` over `universeFormation` premises (the typing, mirroring the Church-numeral
formations); `Step.beta` for the discarding β-step (`subst0` of the closed body is the body by defeq);
`reachedNormalForm_eq_normalForm` (firing-117 tool) on the single-step reduction with `by decide` for the
λ-value's normality; `closedFunctionStepsOrIsLambda` (firing 112) for progress; `stronglyNormalizingOfWfContextDesc`
(SN-043) for SN.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (every
declaration probed with `#print axioms` before landing).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The non-dependent arrow `Π(Type@1, Type@1) : Type@2` in context `[Type@1]` — a Π-FORMATION over two
universe-code children (the universe-code analogue of the Church numeral's `churchNatArrow`, whose children are
variables).  Both children `Type@1` are formed by `universeFormation` (`Type@1 : Type@2`). -/
theorem arrowType1Type1 {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero.lsucc flag))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc flag)
        (universeCodeCell LevelExpr.lzero.lsucc flag))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc.lsucc, LevelExpr.lzero.lsucc.lsucc]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero.lsucc.lsucc, LevelExpr.lzero.lsucc.lsucc] flag
    { outputType := universeFormerOutput } rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc flag)
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc flag)
    · exact DescTelescopePi.nil _ _

/-- **The doubly-nested constant lambda** `λx.λy.Type@0 : Π(Type@1, Π(Type@1, Type@1))` — a function that
returns the constant lambda `λy.Type@0`, discarding its first argument.  Built by an outer `piIntro` (domain
`Type@1`, codomain the arrow `Π(Type@1, Type@1)` via `arrowType1Type1`, body the inner constant lambda) wrapping
an inner `piIntro` (`λy.Type@0 : Π(Type@1, Type@1)` in context `[Type@1]`). -/
theorem nestedConstantLambdaTyping {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (lamCell (universeCodeCell LevelExpr.lzero flag)))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc flag)
        (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc flag)
          (universeCodeCell LevelExpr.lzero.lsucc flag))) := by
  refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc.lsucc
    (lmaxAll [LevelExpr.lzero.lsucc.lsucc, LevelExpr.lzero.lsucc.lsucc]) flag
    ?domainTyped ?codomainTyped ?bodyTyped
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero.lsucc flag)
  · exact arrowType1Type1 flag
  · refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc.lsucc LevelExpr.lzero.lsucc.lsucc flag
      ?innerDomainTyped ?innerCodomainTyped ?innerBodyTyped
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc flag)
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc flag)
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero flag)

/-- **The λ-VALUE fuzz family.**  Apply the nested constant function `λx.λy.Type@0` to the identity-tower
member; one β-step discards the argument and exposes the constant lambda `λy.Type@0` — a FUNCTION value (not a
type code).  The third L2 family, completing the canonical-forms coverage of the fuzz corpus. -/
def metatheoryFuzzLambdaFamily : Nat → RawTerm 0
  | n => appCell (lamCell (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)))
      (metatheoryFuzzFamily n)

/-- Every λ-value family member is well-typed at the arrow `Π(Type@1, Type@1)` — `piElim` of the nested
constant lambda against the identity-tower member (typed at `Type@1`); the var-free codomain makes the `piElim`
output the arrow `Π(Type@1, Type@1)` by defeq. -/
theorem metatheoryFuzzLambdaFamily_typed {profile : PolyProfile} (n : Nat) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (metatheoryFuzzLambdaFamily n)
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
        (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)) :=
  HasTypeDescPi.piElim (nestedConstantLambdaTyping UniverseFlag.standard)
    (metatheoryFuzzFamily_typed n)

/-- Each member β-steps in ONE step to the constant lambda value `λy.Type@0`: the application
`(λx.λy.Type@0) (member)` contracts by `Step.beta`, the argument discarded (`subst0` of the closed body
`λy.Type@0` is itself by defeq). -/
theorem metatheoryFuzzLambdaFamily_betaStep (n : Nat) :
    Step (metatheoryFuzzLambdaFamily n)
      (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) :=
  Step.beta

/-- Each member reaches the constant lambda value in a single-step `StepStar` chain. -/
theorem metatheoryFuzzLambdaFamily_reducesToLambdaValue (n : Nat) :
    StepStar (metatheoryFuzzLambdaFamily n)
      (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) :=
  StepStar.single (metatheoryFuzzLambdaFamily_betaStep n)

/-- ★ **The verified SN-normalizer computes each member to the function value `λy.Type@0`.**
`reachedNormalForm_eq_normalForm` (firing-117) on the single-step reduction, with the λ-value's structural
normality discharged by `decide`.  Unlike the universe-code fuzz families (which normalize to `Type@0`), this
family's normal form is a `λ`. -/
theorem metatheoryFuzzLambdaFamily_normalizesToLambda {profile : PolyProfile} (n : Nat) :
    (metatheoryFuzzLambdaFamily_typed (profile := profile) n).normalForm
      = lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  ((metatheoryFuzzLambdaFamily_typed (profile := profile) n).reachedNormalForm_eq_normalForm
    (metatheoryFuzzLambdaFamily_reducesToLambdaValue n) (by decide)).symm

/-- ★ **Every λ-value family member EVALUATES TO A FUNCTION.**  Its computed normal form is a `λ` (with body
extracted) — the Π-typed canonical-forms outcome (`closedNormalFunctionIsLambda`'s shape) that neither
universe-code fuzz family reaches.  The fuzz corpus now covers both canonical-forms outcomes: a type code
(`Type@0`) and a function (`λy.Type@0`). -/
theorem metatheoryFuzzLambdaFamily_evaluatesToFunction {profile : PolyProfile} (n : Nat) :
    ∃ body, (metatheoryFuzzLambdaFamily_typed (profile := profile) n).normalForm = lamCell body :=
  ⟨universeCodeCell LevelExpr.lzero UniverseFlag.standard,
    metatheoryFuzzLambdaFamily_normalizesToLambda n⟩

/-- **Progress at the function type over the family.**  Each member either steps or IS a `λ` — firing-112's
`closedFunctionStepsOrIsLambda` (progress sharpened at a Π classifier), exercised in the fuzz corpus.  Every
member steps (the β-redex); the λ disjunct is the forward-compatible value case. -/
theorem metatheoryFuzzLambdaFamily_progress {profile : PolyProfile} (n : Nat) :
    (∃ reduct : RawTerm 0, Step (metatheoryFuzzLambdaFamily n) reduct)
    ∨ (∃ body : RawTerm 1, metatheoryFuzzLambdaFamily n = lamCell body) :=
  HasTypeDescPi.closedFunctionStepsOrIsLambda (metatheoryFuzzLambdaFamily_typed (profile := profile) n)

/-- **Strong normalization over the family** (SN-043) — every member terminates, even though it discards a
redex-bearing argument. -/
theorem metatheoryFuzzLambdaFamily_stronglyNormalizing {profile : PolyProfile} (n : Nat) :
    StepStar.IsStronglyNormalizing (metatheoryFuzzLambdaFamily n) :=
  HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed
    (metatheoryFuzzLambdaFamily_typed (profile := profile) n)

end FX1Poly.Typed
