import FX1Poly.Typed.WfContextTypedLrValid
import FX1Poly.Typed.TypedTypeValidityBoxedRename

/-! # FX1Poly/Typed/WfContextTypedLrValidLookup — lookup-validity for the typed-LR well-formed context

`WfContextTypedLrValid.lookupLrValid` is the typed-LR analogue of `WfContextDescPi.lookupIsType`: in a
typed-LR-well-formed context, the type of EVERY variable (the looked-up entry, iterated-weakened to the full
scope) is TYPED-LR-VALID (in `TypedTypeValidityBoxed` at some candidate box).  This is the lookup leg the
Abel-reflection neutral arm of the grown context-conversion piElim crux (GrownCtxConv-5, #842) consumes: a
neutral application's typing reconstructs from the looked-up function-VARIABLE's type, which must itself be
typed-LR-valid — and this lemma supplies exactly that.

## The proof

Structural induction on the context, mirroring `WfContextDescPi.lookupIsType` arm-for-arm:

  * `empty` — `Fin 0` is uninhabited.
  * `cons` head (`index = 0`) — the head binding is typed-LR-valid in the prefix
    (`WfContextTypedLrValid.headLrValid`), then weakened to the full context via
    `TypedTypeValidityBoxed.weakenUnderBinding` (#1116); the cons-lookup of index 0 computes definitionally to
    the weakened head, so the goal matches.
  * `cons` tail (`index = succ k`) — the induction hypothesis on the tail (`tailValid`) gives typed-LR-validity
    of the tail lookup, weakened by the same single-step `weakenUnderBinding`; the cons-lookup of a successor
    index computes definitionally to the weakened tail lookup.

The single-step LR-weakening folds down the telescope: every `cons` descended re-weakens the carried
derivation once, matching the de Bruijn shift accumulated by `lookup`.

## Zero-axiom verification

Structural induction + the shipped `headLrValid` / `tailValid` projections + `weakenUnderBinding` (#1116) +
`Nat`/`Fin` bound arithmetic.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Typed-LR lookup-validity.**  In a typed-LR-well-formed context, the type of every variable (the
looked-up entry, weakened to the full scope) is typed-LR-valid.  The typed-LR analogue of
`WfContextDescPi.lookupIsType`, by structural induction folding `TypedTypeValidityBoxed.weakenUnderBinding`
(#1116) down the telescope.  The lookup leg the Abel-reflection neutral arm of GrownCtxConv-5 (#842) consumes —
a neutral application's typing reconstructs from the looked-up function-variable's (LR-valid) type. -/
theorem WfContextTypedLrValid.lookupLrValid {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    WfContextTypedLrValid context →
      ∀ index : Fin scope,
        ∃ box : KripkeCandBox scope,
          TypedTypeValidityBoxed profile context (context.lookup index) box := by
  induction context with
  | empty =>
      intro _ index
      exact absurd index.isLt (Nat.not_lt_zero index.val)
  | cons restContext bindingType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          obtain ⟨_box, headValid⟩ := WfContextTypedLrValid.headLrValid wellFormed
          exact headValid.weakenUnderBinding bindingType
      | succ k =>
          obtain ⟨_box, tailValid⟩ :=
            ih (WfContextTypedLrValid.tailValid wellFormed)
              ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩
          exact tailValid.weakenUnderBinding bindingType

end FX1Poly.Typed
