import FX1Poly.Typed.IsTypeDecidable

/-! # FX1Poly/Typed/WfContextDecidable
    — deciding context well-formedness (completes the decidable-checking story)

The decidable-typing triad decides judgments OVER a well-formed context
(`Decidable IsType` #303, `Decidable HasType` #461, `Conv.decidableOfTyped`
#462).  This file decides the well-formedness of the context ITSELF: a raw
`TypingContext` telescope is admitted by construction (#467), and `WfContext`
(#468) is the predicate certifying every binding's type is genuinely a type in
its own prefix.  `WfContext.decidable` is its decision procedure — the
context-level checker an agentic FX user runs before any term-level query.

```
WfContext.decidable : (context : TypingContext profile scope) → Decidable (WfContext context)
```

Structural recursion on the telescope, mirroring `WfContext`'s own
computed-`def` shape (`WfContext.lean`): `.empty` is `True` (decidably so);
`.cons rest binding` is `WfContext rest ∧ IsType … binding`, decided by
recursing on `rest`, then — ONLY once the prefix is known well-formed — running
`IsType.decidableOfWellFormed` (#303) on the binding (which REQUIRES the
`WfContext rest` certificate, supplied by the recursive `isTrue` branch; this
dependency is why the check cannot be a plain `And` decision and must thread the
prefix witness).  The refutations use the definitional `And` projections
`WfContext.tailWellFormed` / `headIsType`, and the positive case the
`WfContext.cons` introducer — all propext-free (see `WfContext.lean`'s header on
the computed-`def` form).

## Zero-axiom verification

Structural recursion on the telescope + the shipped
`IsType.decidableOfWellFormed` + the definitional `WfContext`
projection/introducer helpers.  The outer `match` on the telescope handles BOTH
constructors (no impossible-index case to discharge), so it compiles to a clean
recursor with no propext-tainted equation lemma.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Decide whether a raw `TypingContext` telescope is well-formed: every
binding's type is a type (`IsType`) in the prefix that precedes it.  Structural
recursion on the telescope.  A binding's `IsType` is checked only after its
prefix is certified well-formed, because `IsType.decidableOfWellFormed` consumes
that certificate; the `isFalse` arms refute via the `And` projections, the
`isTrue` arm builds via `WfContext.cons`. -/
def WfContext.decidable {profile : PolyProfile} :
    {scope : Nat} → (context : TypingContext profile scope) →
      Decidable (WfContext context)
  | _, .empty => isTrue WfContext.emptyIsWellFormed
  | _, .cons restContext bindingType =>
      match WfContext.decidable restContext with
      | isFalse restNotWellFormed =>
          isFalse (fun wellFormed =>
            restNotWellFormed (WfContext.tailWellFormed wellFormed))
      | isTrue restWellFormed =>
          match IsType.decidableOfWellFormed restWellFormed bindingType with
          | isTrue bindingIsType =>
              isTrue (WfContext.cons restWellFormed bindingIsType)
          | isFalse bindingNotType =>
              isFalse (fun wellFormed =>
                bindingNotType (WfContext.headIsType wellFormed))

end FX1Poly.Typed
