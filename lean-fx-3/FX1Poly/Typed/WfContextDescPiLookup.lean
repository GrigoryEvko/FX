import FX1Poly.Typed.WfContextDescPi
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescPiSubstitution

/-! # FX1Poly/Typed/WfContextDescPiLookup — lookup-validity for the grown context well-formedness

Lookup-validity for the grown context: in a grown-well-formed context, the type of EVERY variable — not just
the most-recent binding — is a grown type (`IsTypeDescPi`) in the full context.  This is the `var`-arm engine
of grown classifier-validity over `WfContextDescPi`, which the master subject-reduction dispatcher threads.

  * `IsTypeDescPi.weakenUnderBinding` — `IsTypeDescPi` survives a binding extension (the grown weakening of the
    universe-typing witness, via `HasTypeDescPi.weakenUnderBinding`).
  * `WfContextDescPi.lookupIsType` — structural induction on the context: the head binding is grown-well-formed
    by `headIsType` (weakened over itself); a deeper binding by the IH on the prefix (weakened through the new
    binding), with the weakening at the grown `IsTypeDescPi`/`HasTypeDescPi` layer.

## Zero-axiom verification

Structural context induction + `HasTypeDescPi.weakenUnderBinding` (grown renaming) + the `WfContextDescPi`
`And`-projection inversions.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- `IsTypeDescPi` survives a binding extension: if `classifier` is a grown type in `context`, its weakening is
a grown type in `context.cons newBinding`.  The grown weakening of the universe-typing witness. -/
theorem IsTypeDescPi.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsTypeDescPi profile context classifier) (newBinding : RawTerm scope) :
    IsTypeDescPi profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken classifier) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact ⟨levelExpr, flag, typed.weakenUnderBinding newBinding⟩

/-- `IsTypeDescPi` survives single-substitution (the substitution dual of `weakenUnderBinding`): if `classifier`
is a grown type in `context.cons argType` and `argument : argType`, the substituted classifier is a grown type
in `context`.  The universe-code witness is `subst`-invariant.  Completes the grown type-stability pair (weaken
+ subst), the engine `piCodeInstantiationIsType` inlines for the dependent Π-elimination output. -/
theorem IsTypeDescPi.substituteUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {argType : RawTerm scope}
    {classifier : RawTerm (scope + 1)}
    (isType : IsTypeDescPi profile (context.cons argType) classifier)
    (argument : RawTerm scope)
    (argumentTyped : HasTypeDescPi profile context argument argType) :
    IsTypeDescPi profile context (RawTerm.subst0 classifier argument) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact ⟨levelExpr, flag, typed.substituteUnderBinding argument argumentTyped⟩

/-- Lookup-validity for grown well-formedness: in a grown-well-formed context, the type of every variable is a
grown type in the full context.  Structural induction on the context (the head binding via `headIsType`, a
deeper binding via the IH on the prefix), each weakened through the intervening binding.  The `var`-arm engine
of grown classifier-validity over `WfContextDescPi`. -/
theorem WfContextDescPi.lookupIsType {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    WfContextDescPi context →
      ∀ index : Fin scope, IsTypeDescPi profile context (context.lookup index) := by
  induction context with
  | empty =>
      intro _ index
      exact absurd index.isLt (Nat.not_lt_zero index.val)
  | cons restContext bindingType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          exact (WfContextDescPi.headIsType wellFormed).weakenUnderBinding bindingType
      | succ k =>
          exact (ih (WfContextDescPi.tailWellFormed wellFormed)
            ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding bindingType

end FX1Poly.Typed
