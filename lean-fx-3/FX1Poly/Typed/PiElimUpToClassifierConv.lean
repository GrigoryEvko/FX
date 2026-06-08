import FX1Poly.Typed.HasTypeDescPiApplication
import FX1Poly.Typed.HasTypeDescPiClassifierValidity

/-! # FX1Poly/Typed/PiElimUpToClassifierConv — the GCC-5 reduction: the piElim arm closes
    given exactly ONE property, `IsTypeDescPi` respects `Conv` (type-Conv-closure).

GCC-5 (`#842`, "the grown context-conversion piElim arm — the entangled crux") has gated the
subject-reduction / canonicity apex for the grown engine.  The conditional dispatchers
(`HasTypeDescPiContextConversionConditional`, `HasTypeDescPiSubjectReductionMutual`,
`ConsistencyOfPiElimArm`) all factor out the SAME residual: a `piElimArm` hypothesis that re-types
an application `appCell fn arg` under a `Conv`-replaced context.  This file PINS that residual to a
single, textbook-clean property.

## The reduction

In the mutual context-conversion, the `piElim` arm has, by the induction hypotheses on the function
and argument SUBDERIVATIONS, the function and argument already re-typed under the target context — at
types `Conv`-equal to (respectively) the Π-code `piTyCodeCell domainCode codomainCode` and the
domain `domainCode`.  `piElimUpToClassifierConv` is exactly that arm body: it rebuilds the
application from those two re-typings, parameterized by `classifierRespectsConv`.

The proof uses ONLY shipped pieces — the SOLE genuinely-new ingredient is `classifierRespectsConv`:

  1. **validity** (`HasTypeDescPi.classifierIsTypeDescPi`, unconditional, WFG-3): the re-typed
     function's classifier `functionType` is itself a grown type (`IsTypeDescPi functionType`);
  2. **`classifierRespectsConv`** (the hypothesis): transport that `IsTypeDescPi` across
     `Conv functionType (piTyCodeCell domainCode codomainCode)` to get `IsTypeDescPi` of the
     SYNTACTIC Π-code — this is the lone residual, `type-Conv-closure`;
  3. the **`conv` rule** re-ascribes the function to the syntactic Π-code (its premise `IsType` is
     exactly step 2's output) and the argument to the domain (its `IsType` is the Π-code's domain
     component, by `inversionPiCodeComponents`);
  4. **`piElim`** assembles the application, landing at `subst0 codomainCode argument` on the nose
     (no `Conv` wiggle on the output).

So GCC-5 reduces to `classifierRespectsConv : IsTypeDescPi Γ A → Conv A B → IsTypeDescPi Γ B`.
Everything else — `classifierIsTypeDescPi`, the `conv` rule, `inversionPiCodeComponents`,
`Conv.piTyCode_inj` — is shipped and unconditional.

`classifierRespectsConv` itself is NOT a subject-reduction corollary (it would need subject
EXPANSION on the convertible side, false in general); it is `validity`-strength and the tractable
attack is the reducibility model — the universe candidate IS `IsReducibleType`
(`StratifiedReducibleType`), which is `Conv`-invariant by `ReducibleTypeAt.convInvariant` (`#537`),
leaving the reducible→typed reflect (`ReducibleTypeWellFormed`-adjacent) as the VAL-2 residual.

## Zero-axiom

`classifierIsTypeDescPi` + `classifierRespectsConv` (hyp) + two `HasTypeDescPi.conv` applications +
`inversionPiCodeComponents` + `HasTypeDescPi.piElim`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **GCC-5 reduced to one property.**  The grown Π-elimination arm of context-conversion: given the
function re-typed at `functionType ≡ piTyCodeCell domainCode codomainCode` and the argument re-typed
at `argumentType ≡ domainCode` (the mutual-induction hypotheses), plus `classifierRespectsConv`
(type-Conv-closure: `IsTypeDescPi` respects `Conv` at this context), the application
`appCell functionTerm argument` types at `subst0 codomainCode argument`.  Pins the GCC-5 residual to
the single lemma `classifierRespectsConv`; all else is shipped + unconditional. -/
theorem HasTypeDescPi.piElimUpToClassifierConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument functionType argumentType domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (classifierRespectsConv : ∀ {typeLeft typeRight : RawTerm scope},
      IsTypeDescPi profile context typeLeft → Conv typeLeft typeRight →
        IsTypeDescPi profile context typeRight)
    (wellFormed : WfContextDescPi context)
    (functionTyped : HasTypeDescPi profile context functionTerm functionType)
    (functionConv : Conv functionType (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument argumentType)
    (argumentConv : Conv argumentType domainCode) :
    HasTypeDescPi profile context (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument) := by
  have functionTypeIsType : IsTypeDescPi profile context functionType :=
    functionTyped.classifierIsTypeDescPi wellFormed
  have piIsType : IsTypeDescPi profile context (piTyCodeCell domainCode codomainCode) :=
    classifierRespectsConv functionTypeIsType functionConv
  obtain ⟨piLevel, piFlag, piTyped⟩ := piIsType
  have functionAtPi : HasTypeDescPi profile context functionTerm
      (piTyCodeCell domainCode codomainCode) :=
    HasTypeDescPi.conv piLevel piFlag functionTyped functionConv piTyped
  obtain ⟨domainLevel, _codomainLevel, domainFlag, domainTyped, _codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponents piTyped
  have argumentAtDomain : HasTypeDescPi profile context argument domainCode :=
    HasTypeDescPi.conv domainLevel domainFlag argumentTyped argumentConv domainTyped
  exact HasTypeDescPi.piElim functionAtPi argumentAtDomain

end FX1Poly.Typed
