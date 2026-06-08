import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction
import FX1Poly.Typed.HasTypeDescPiFormerCongruence
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.HasTypeDescPiInversion

/-! # FX1Poly/Typed/ConvContextPreservesPiValidityFormerStep
    — the binary-former (Π and Σ) recursion steps of the GrownCtxConv-5 residual `ConvContextPreservesPiValidity`

`ConvContextPreservesPiValidity` (`#1092`) — a `Π`-type-code's grown validity is stable under context
conversion — is the single residual to which both open grown-metatheory release blockers reduce (GrownCtxConv-5
context-conversion `#842` AND SRD-2 master SR `#845`, unified in `#1098`).  Two of its three structural pieces
already ship:

  * **base (formation fragment, `#1099`)** — `convContextPreservesPiValidityForFormationCode`: a `Π`-code whose
    validity factors through `ofFormation` (the common dependent-type case, no type-level computation)
    context-converts unconditionally.
  * **neutral leaf (var-headed, `#1119`)** — `varHeadedAppReassemblyUnderContextConv`: a var-headed neutral
    type-level application's reassembly reduces to exactly this residual at its sub-codes.

This file ships the MIDDLE piece — the **inductive ENGINE**: the `Π`-FORMER recursion step.  It shows the
residual recurses STRUCTURALLY on the `Π`-code, reducing a `Π domainCode codomainCode`'s validity transport to
its component transports — `inversionPiCodeComponentsUnconditional` decomposes the source `Π`-validity into the
domain (at `sourceContext`) and codomain (at `sourceContext.cons domainCode`) universe-typings, the structural
IHs transport each (the codomain under the cons-lifted context conversion `convContextCondition_cons`), and
`piFormationViaGenArm` re-forms the `Π`-code's validity under the target.  "Semantic types are `Conv`-closed by
construction" made concrete for the `Π`-former: the `Π`-validity under the target is REBUILT from its
(transported) parts, never carried as a black box.

## The universe-code-PRESERVING IH shape (the flag-matching insight)

The structural IHs `domainConverts` / `codomainConverts` transport at a FIXED universe code
(`universeCodeCell level flag`), PRESERVING both level and flag — NOT the existential `IsTypeDescPi`.  This is
essential, not cosmetic: `piFormationViaGenArm` requires the domain and codomain universe-typings to share the
SAME `flag`.  `inversionPiCodeComponentsUnconditional` hands back the domain and codomain at a COMMON `flag`
(the `Π`-formation rule forms them at one flag); the universe-preserving IHs keep that flag fixed through the
transport, so the two re-formation inputs still agree.  The existential `IsTypeDescPi` transport would
re-existentialize the flags independently — they could come back distinct, and `piFormationViaGenArm` would not
apply.  The universe-preserving form is also exactly what a structural recursion over the type-code naturally
carries (each recursive call returns the SAME universe code).

## What this localizes

With the base (#1099), the engine (here), and the var-headed neutral leaf (#1119) in place, the residual's
genuinely-open core is precisely the APP-HEADED neutral type-level application leaf — a neutral whose argument
is an arbitrary term (not a variable), whose typing transport needs the general-term context conversion (the
mutual fundamental-metatheory bundle, GTL-20/`#1098`).  The `Π`-former is NO LONGER an obstruction (this file);
neither is the formation fragment (#1099) nor the var-spine (#1119).

## Zero-axiom verification

`obtain` the source `Π`-universe witness, `inversionPiCodeComponentsUnconditional` to decompose,
`convContextCondition_cons` for the codomain cons-lift, the two universe-preserving IHs, and
`piFormationViaGenArm` to re-form.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The Π-former recursion step of `ConvContextPreservesPiValidity`.**  Given the universe-code-PRESERVING
context conversions of the domain type-code (`domainConverts`, at `sourceContext`) and the codomain type-code
(`codomainConverts`, at `sourceContext.cons domainCode`) — the structural IHs — a `Π domainCode codomainCode`'s
grown validity transports across any pointwise-`Conv` context conversion: decompose the source `Π`-validity
into its components (`inversionPiCodeComponentsUnconditional`), transport each (the codomain under the
cons-lifted condition `convContextCondition_cons`, preserving the COMMON universe flag — see the file header),
and re-form via `piFormationViaGenArm`.  The inductive engine of the residual's structural discharge, between
the formation base (`#1099`) and the var-headed neutral leaf (`#1119`). -/
theorem HasTypeDescPi.piCodeValidityContextConversionFormerStep {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainConverts : ∀ {domainLevel : LevelExpr} {domainFlag : UniverseFlag},
      HasTypeDescPi profile sourceContext domainCode (universeCodeCell domainLevel domainFlag) →
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      HasTypeDescPi profile targetContext domainCode (universeCodeCell domainLevel domainFlag))
    (codomainConverts : ∀ {codomainLevel : LevelExpr} {codomainFlag : UniverseFlag},
      HasTypeDescPi profile (sourceContext.cons domainCode) codomainCode
        (universeCodeCell codomainLevel codomainFlag) →
      (∀ index : Fin (scope + 1),
        Conv ((sourceContext.cons domainCode).lookup index)
          ((targetContext.cons domainCode).lookup index)) →
      HasTypeDescPi profile (targetContext.cons domainCode) codomainCode
        (universeCodeCell codomainLevel codomainFlag))
    (piValidity : IsTypeDescPi profile sourceContext (piTyCodeCell domainCode codomainCode))
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    IsTypeDescPi profile targetContext (piTyCodeCell domainCode codomainCode) := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := piValidity
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponentsUnconditional piTyped
  have domainTyped' := domainConverts domainTyped contextConv
  have codomainTyped' :=
    codomainConverts codomainTyped (convContextCondition_cons domainCode contextConv)
  exact ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
    HasTypeDescPi.piFormationViaGenArm targetContext domainCode codomainCode
      domainLevel codomainLevel flag domainTyped' codomainTyped'⟩

/-- **The Σ-former recursion step of the residual** (the exact twin of the Π-former step).  The residual's
Π-engine (`piCodeValidityContextConversionFormerStep`) recurses on the component type-codes `domainCode` /
`codomainCode`, which can THEMSELVES be `Σ`-codes — so the `Σ`-former step is a genuinely-needed companion, not
a separate concern.  Given the universe-code-PRESERVING context conversions of the domain (at `sourceContext`)
and codomain (at `sourceContext.cons domainCode`) type-codes, a `Σ domainCode codomainCode`'s grown validity
transports across any pointwise-`Conv` context conversion: `inversionSigmaCodeComponents` decomposes the source
`Σ`-validity into its component universe-typings (at a COMMON flag), the IHs transport each (the codomain under
the cons-lifted condition `convContextCondition_cons`, preserving that common flag), and `sigmaFormationViaGenArm`
re-forms.  Identical recipe to the `Π` step over `sigmaTyCodeCell` / `inversionSigmaCodeComponents` /
`sigmaFormationViaGenArm`. -/
theorem HasTypeDescPi.sigmaCodeValidityContextConversionFormerStep {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainConverts : ∀ {domainLevel : LevelExpr} {domainFlag : UniverseFlag},
      HasTypeDescPi profile sourceContext domainCode (universeCodeCell domainLevel domainFlag) →
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      HasTypeDescPi profile targetContext domainCode (universeCodeCell domainLevel domainFlag))
    (codomainConverts : ∀ {codomainLevel : LevelExpr} {codomainFlag : UniverseFlag},
      HasTypeDescPi profile (sourceContext.cons domainCode) codomainCode
        (universeCodeCell codomainLevel codomainFlag) →
      (∀ index : Fin (scope + 1),
        Conv ((sourceContext.cons domainCode).lookup index)
          ((targetContext.cons domainCode).lookup index)) →
      HasTypeDescPi profile (targetContext.cons domainCode) codomainCode
        (universeCodeCell codomainLevel codomainFlag))
    (sigmaValidity : IsTypeDescPi profile sourceContext (sigmaTyCodeCell domainCode codomainCode))
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    IsTypeDescPi profile targetContext (sigmaTyCodeCell domainCode codomainCode) := by
  obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := sigmaValidity
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩ :=
    HasTypeDescPi.inversionSigmaCodeComponents sigmaTyped
  have domainTyped' := domainConverts domainTyped contextConv
  have codomainTyped' :=
    codomainConverts codomainTyped (convContextCondition_cons domainCode contextConv)
  exact ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
    HasTypeDescPi.sigmaFormationViaGenArm targetContext domainCode codomainCode
      domainLevel codomainLevel flag domainTyped' codomainTyped'⟩

end FX1Poly.Typed
