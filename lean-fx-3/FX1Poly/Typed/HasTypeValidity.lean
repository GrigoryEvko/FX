import FX1Poly.Typed.WfContext
import FX1Poly.Typed.HasTypeWeakening
import FX1Poly.Typed.HasTypeSubstitution

/-! # FX1Poly/Typed/HasTypeValidity — validity / classifier-is-a-type (P3)

The validity (a.k.a. regularity / type-correctness) theorem: the classifier
of any well-typed cell is itself a type.  In the decidable-fibration reading
(roadmap P3) this is "every `outputType` is provably a type" — what makes the
display map `Tm ↠ Ty` land in `Ty`, and a prerequisite for inversion (P8) and
the bidirectional typechecker (validity lets `infer` return a *type*, not a
raw cell).

```
HasType.classifierIsType : WfContext Γ → HasType Γ t T → IsType Γ T
```

The `WfContext Γ` hypothesis is load-bearing for exactly one arm — `var`,
whose classifier is a context lookup; the other arms (`conv`,
`universeFormation`) are unconditional.

## What this brick delivers

* `IsType.weakenUnderBinding` / `IsType.substituteUnderBinding` — the
  `IsType`-stability lemmas (TY-WF #468 remaining piece): `IsType` survives
  weakening and single-substitution.  Direct `IsType`-lifts of the `HasType`
  weakening (#456) and substitution (#457) lemmas — the universe-code
  classifier is rename/subst invariant, so the existential witness transports
  unchanged.
* `WfContext.lookupIsType` — looking up a variable in a well-formed context
  yields a type.  The engine of the `var` case: it threads
  `IsType.weakenUnderBinding` along the `lookup` recursion's weakening chain.
* `HasType.classifierIsType` — validity itself (P3), by induction on the
  derivation.

## Zero-axiom verification

`obtain` on the `IsType` existential + `induction` + `Fin` 0/successor split +
`WfContext` `And`-projections.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`.  Critically `Conv.trans`-free.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- `IsType` survives weakening: if `classifier` is a type in `context`, its
weakening is a type in `context.cons newBinding`.  The universe-code witness
is `rename`-invariant (`rename_universeCodeCell`), so the existential carries
across unchanged. -/
theorem IsType.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsType profile context classifier) (newBinding : RawTerm scope) :
    IsType profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken classifier) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact ⟨levelExpr, flag, typed.weakenUnderBinding newBinding⟩

/-- `IsType` survives single-substitution: if `classifier` is a type in
`context.cons argType` and `argument` is well-typed at `argType`, then the
substituted classifier is a type in `context`.  The universe-code witness is
`subst`-invariant (`subst_universeCodeCell`). -/
theorem IsType.substituteUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {argType : RawTerm scope}
    {classifier : RawTerm (scope + 1)}
    (isType : IsType profile (context.cons argType) classifier)
    (argument : RawTerm scope)
    (argumentTyped : HasType profile context argument argType) :
    IsType profile context (RawTerm.subst0 classifier argument) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact ⟨levelExpr, flag, typed.substituteUnderBinding argument argumentTyped⟩

/-- Looking up a variable in a well-formed context yields a type.  The
engine of validity's `var` case: each binding is a type in its own prefix
(`WfContext`), and `lookup` weakens it into the full scope — so the result is
a type by `IsType.weakenUnderBinding`, applied once per binder the recursion
tunnels. -/
theorem WfContext.lookupIsType {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    WfContext context →
      ∀ index : Fin scope, IsType profile context (context.lookup index) := by
  induction context with
  | empty =>
      intro _ index
      exact absurd index.isLt (Nat.not_lt_zero index.val)
  | cons restContext bindingType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          exact (WfContext.headIsType wellFormed).weakenUnderBinding bindingType
      | succ k =>
          exact (ih (WfContext.tailWellFormed wellFormed)
            ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding bindingType

/-- Validity (P3): the classifier of any well-typed cell is itself a type.
By induction on the derivation — `var` looks up a type in the well-formed
context, `conv` hands back its classifier-well-formedness witness verbatim,
and `universeFormation` re-fires one level up.  The `WfContext` hypothesis is
needed only for `var`. -/
theorem HasType.classifierIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContext context)
    (typed : HasType profile context subject classifier) :
    IsType profile context classifier := by
  induction typed with
  | var context index => exact WfContext.lookupIsType context wellFormed index
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihTypedPremise ihReclassifier =>
      exact ⟨levelExpr, flag, reclassifierTyped⟩
  | universeFormation context levelExpr flag =>
      exact ⟨_, _, HasType.universeFormation context levelExpr.lsucc flag⟩
  | piFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      -- the Π classifier is `Type@(lmax domainLevel codomainLevel, flag)`, a
      -- universe code, hence a type by `universeFormation` one level up
      exact ⟨_, _, HasType.universeFormation context
        (LevelExpr.lmax domainLevel codomainLevel) flag⟩

end FX1Poly.Typed
