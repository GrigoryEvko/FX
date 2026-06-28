import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstUnionTyped
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction

/-! # FX1Poly/Typed/Metatheory/ContextConversion/HasTypeUnionContextConversion
    — NATIVE single-binder context conversion along a `Conv` in the head binding (SR-DSL-2 motive-arm unblock)

The eliminator-congruence subject reduction's MOTIVE arm rebuilds the eliminator cell with the stepped motive
`motive'`; its binder-extended branch obligations then live over a context whose HEAD binding drifted
`motive ⟶ motive'` (e.g. `natElim`'s step branch over `(context.cons natTypeCell).cons motive`).  Re-typing the
branch there needs CONTEXT CONVERSION: a derivation over `context.cons oldBinding` transports to
`context.cons newBinding` when the two bindings are `Conv`-equal and well-formed.

Only the GROWN `HasTypeDescPi.*ContextConversion*` masters existed (`Typed/Metatheory/ContextConversion/`); the
NATIVE-union version was a gap.  This file closes it WITHOUT a fresh induction: context conversion is exactly the
substitution master `HasTypeUnion.substRespectingContext` at the IDENTITY substitution between the two converted
contexts.  The `SubstUnionTyped` condition holds because (i) `subst identity` collapses every looked-up source
binding (`subst_identity_apply`); (ii) the head variable `var 0` is typed at the NEW binding's weakening and
reclassified back to the OLD binding's weakening through the `Conv` (`reclassifyToType` + the old binding's
weakened validity); (iii) every deeper variable is typed at its (unchanged) tail lookup directly.  The identity
substitution then collapses the subject and classifier on the conclusion.

## Zero-axiom verification

`HasTypeUnion.substRespectingContext` + `RawTerm.subst_identity_apply` + the native `var` arm +
`HasTypeUnion.reclassifyToType` + `Conv.weaken` + `UnionClassifierIsType.weakenUnderBinding` over a `Fin`
0/successor split.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **The identity substitution between two `Conv`-converted head bindings is union-typed.**  Maps the source
context `context.cons oldBinding` into the target `context.cons newBinding`: `var 0` resolves at the new binding
and reclassifies back to the old binding's weakening via the `Conv` (the old binding's weakened validity supplies
the reclassification target); every deeper variable resolves at its unchanged tail lookup directly. -/
theorem identityAcrossConvertedHeadBinding_isSubstUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (oldBinding newBinding : RawTerm scope)
    (bindingConv : Conv oldBinding newBinding)
    (oldFormed : UnionClassifierIsType profile context oldBinding) :
    HasTypeUnion.SubstUnionTyped (context.cons oldBinding) (context.cons newBinding)
      RawTermSubst.identity := by
  -- ★ A1-CONJUNCT-WIRE: `SubstUnionTyped` is now `(typing component) ∧ (accessibility-preservation component)`.
  refine ⟨?_, ?_⟩
  · -- `.1` (the original TYPING component): each identity image `var index` is union-typed at the substituted
    -- lookup, with the head `var 0` reclassified across the `Conv` between the two head bindings.
    intro index useModality isAccessible
    rw [RawTerm.subst_identity_apply]
    match index, isAccessible with
    | ⟨0, _⟩, _ =>
        rw [TypingContext.lookup_cons_zero]
        -- `var 0 : weaken newBinding` (target head), reclassified to `weaken oldBinding` through the `Conv`.
        have varTyped := HasTypeUnion.var (context.cons newBinding) ⟨0, Nat.zero_lt_succ scope⟩
          (useModality := .fibrant) rfl
        rw [TypingContext.lookup_cons_zero] at varTyped
        exact HasTypeUnion.reclassifyToType varTyped (Conv.weaken bindingConv).sym
          (oldFormed.weakenUnderBinding newBinding)
    | ⟨Nat.succ priorIndex, indexBound⟩, isAccessible =>
        rw [TypingContext.lookup_cons_succ]
        -- Deeper variables resolve at the (unchanged) tail lookup directly; the source-`cons` accessibility is
        -- defeq to the target-`cons` accessibility (`isFibrantlyAccessibleAt` ignores the binding CONTENT).
        have varTyped := HasTypeUnion.var (context.cons newBinding) ⟨priorIndex + 1, indexBound⟩ isAccessible
        rwa [TypingContext.lookup_cons_succ] at varTyped
  · -- `.2` (the ACCESSIBILITY-PRESERVATION component): the identity carries every accessible source variable to
    -- itself (`RawTermSubst.identity index = var index`), and `isAccessibleAtModality` ignores the binding
    -- CONTENT, so the source-`cons oldBinding` accessibility transports to the target-`cons newBinding` usability
    -- by defeq at every modality.
    intro modality index isAccessible
    show (context.cons newBinding).isSubjectUsableAtModality
      (.mkGen .gen_var index .childNil) modality = true
    rw [isSubjectUsableAtModality_var]
    -- Casing the index reduces the `cons`-accessibility match, dropping the binding CONTENT from both sides, so
    -- the source-`oldBinding` accessibility IS the target-`newBinding` accessibility (defeq).
    obtain ⟨indexValue, indexBound⟩ := index
    cases indexValue <;> exact isAccessible

/-- **★ NATIVE single-binder context conversion.**  A union derivation over `context.cons oldBinding` transports
to `context.cons newBinding` whenever the two head bindings are `Conv`-equal and the old binding is a well-formed
type.  The substitution master `HasTypeUnion.substRespectingContext` at the identity substitution
(`identityAcrossConvertedHeadBinding_isSubstUnionTyped`); the identity collapses the subject and classifier
(`subst_identity_apply`).  This is the load-bearing piece the congruence-SR motive arm needs to re-type a
binder-extended branch obligation after the motive (the head binding) steps. -/
theorem HasTypeUnion.convertHeadBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {oldBinding newBinding : RawTerm scope}
    {subject classifier : RawTerm (scope + 1)}
    (typed : HasTypeUnion profile (context.cons oldBinding) subject classifier)
    (bindingConv : Conv oldBinding newBinding)
    (oldFormed : UnionClassifierIsType profile context oldBinding) :
    HasTypeUnion profile (context.cons newBinding) subject classifier := by
  have transported := typed.substRespectingContext (context.cons newBinding) RawTermSubst.identity
    (identityAcrossConvertedHeadBinding_isSubstUnionTyped context oldBinding newBinding bindingConv oldFormed)
  rwa [RawTerm.subst_identity_apply, RawTerm.subst_identity_apply] at transported

end FX1Poly.Typed
