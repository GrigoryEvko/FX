import FX1Poly.Typed.HasTypeDescPiContextConversionConditional
import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction
import FX1Poly.Typed.GrownMutualMetatheoryFromPiValidity

/-! # FX1Poly/Typed/HasTypeDescPiContextConversionPiElimEquivalence
    — the REVERSE direction `piElimArm → residual`, completing the equivalence `residual ⟺ piElimArm`

GrownCtxConv-5 (the grown context-conversion `piElim` arm, `#842`) is the FX-kernel release blocker.  Two
companion files surround it:

  * `HasTypeDescPiContextConversionConditional` — the full grown context conversion, conditional on the lone
    `piElimArm` hypothesis (`convContextOfPiElimArm`); the `piElim` case is FACTORED OUT as that hypothesis
    because the native `conv` rule (`HasTypeDescPi.conv`) requires the NEW classifier to be a valid type code
    (`reclassifierTyped : HasTypeDescPi tgt reclassifier (universeCodeCell …)`), so re-typing the function at
    the literal `piTyCodeCell domainCode codomainCode` in the target needs `IsTypeDescPi tgt (Π D C)`.
  * `HasTypeDescPiContextConversionPiElimReduction` — the FORWARD reduction
    `piElimArmFromPiValidityTransfer` (`#1092`): under the residual `ConvContextPreservesPiValidity` (plus
    source well-formedness) the `piElim` arm holds.  That is exactly "`IsTypeDescPi tgt (Π D C)` from the
    residual", so `residual → piElimArm`.

## What this file adds — the REVERSE, and it is FREE

`piValidityFromPiElimArm`: `piElimArm → ConvContextPreservesPiValidity`, with NO well-formedness premise.

The residual transports a Π-CODE's *universe* typing (`HasTypeDescPi src (Π D C) (universe level flag)`), not an
application's.  `convContextOfPiElimArm piElimArm` already transports it to
`∃ reclassifier, Conv (universe level flag) reclassifier ∧ HasTypeDescPi tgt (Π D C) reclassifier`.  The
conv-back to the literal universe code is then UNCONDITIONAL: the `conv` rule's `reclassifierTyped` obligation
here is the UNIVERSE code's validity `HasTypeDescPi tgt (universe level flag) (universe level.lsucc flag)`,
which `HasTypeDesc.universeFormation` supplies for free (universe codes are always valid).  So the circularity
that blocks the application case (re-typing at a Π-code) simply does not arise for the type-code case (re-typing
at a universe code).

## The consequence — `piElimArm` is the single lynchpin

Combining the forward (`#1092`) and this reverse gives `residual ⟺ piElimArm` (the forward needs source
well-formedness; the reverse is free).  So GrownCtxConv-5's ENTIRE remaining content is EXACTLY the one
`piElim` arm — no more, no less.  Concretely, `piElimArm` alone unlocks the whole grown metatheory:

  * grown context conversion — `convContextOfPiElimArm piElimArm` (already shipped, no extra premise);
  * the residual `ConvContextPreservesPiValidity` — `piValidityFromPiElimArm` (here);
  * master subject reduction — `masterSubjectReductionFromPiElimArm` (here), chaining this through GTL-20's
    `masterSubjectReductionFromPiValidity`;
  * the full GTL-20 mutual bundle (`grownMutualMetatheoryFromPiValidity`) and SRD-2 (`#845`) / SN-055
    (`#558`), all of which take the residual as their single hypothesis.

This sharpens every downstream task: discharging GrownCtxConv-5, SRD-2, or SN-055 all reduce to discharging the
one `piElim` arm (equivalently, the residual).

## Zero-axiom verification

`piValidityFromPiElimArm` is `convContextOfPiElimArm` specialized to a Π-code subject plus a free `conv`-back via
`ofFormation ∘ universeFormation`; `masterSubjectReductionFromPiElimArm` is a direct composition with GTL-20.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **★ The reverse equivalence: `piElimArm → residual`, with NO well-formedness premise.**  The residual
transports a Π-CODE's universe typing; `convContextOfPiElimArm piElimArm` does exactly that (up to a `Conv`-equal
classifier), and the conv-back to the literal universe code is FREE because the `conv` rule's classifier-validity
obligation is here the universe code's own validity (`ofFormation ∘ universeFormation`), not a Π-code's.  So the
circularity that blocks the application case does not arise for the type-code case.  Combined with the forward
`piElimArmFromPiValidityTransfer` (`#1092`) this gives `residual ⟺ piElimArm`: GrownCtxConv-5's entire remaining
content IS the single `piElim` arm. -/
theorem piValidityFromPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier') :
    ConvContextPreservesPiValidity profile := by
  intro scope sourceContext targetContext domainCode codomainCode piValidity contextConv
  obtain ⟨level, flag, piTyped⟩ := piValidity
  obtain ⟨reclassifier, convToReclassifier, typedAtReclassifier⟩ :=
    HasTypeDescPi.convContextOfPiElimArm piElimArm piTyped targetContext contextConv
  exact ⟨level, flag,
    HasTypeDescPi.conv _ _ typedAtReclassifier convToReclassifier.sym
      (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation targetContext level flag))⟩

/-- **★ The master-SR capstone: `piElimArm` alone yields master subject reduction.**  Chains the reverse
equivalence `piValidityFromPiElimArm` through GTL-20's `masterSubjectReductionFromPiValidity`.  Together with
`convContextOfPiElimArm` (grown context conversion from `piElimArm`, no extra premise) this exhibits `piElimArm`
as the single lynchpin of the grown metatheory: one arm unlocks context conversion AND subject reduction. -/
theorem masterSubjectReductionFromPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDescPi context) :
    ∀ reduct : RawTerm scope, Step subject reduct →
      HasTypeDescPi profile context reduct classifier :=
  HasTypeDescPi.masterSubjectReductionFromPiValidity
    (piValidityFromPiElimArm piElimArm) derivation wellFormed

end FX1Poly.Typed
