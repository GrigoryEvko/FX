import FX1Poly.Typed.TypedTypeValidityBoxedRelation
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/WfContextTypedLrValid — typed-LR well-formedness of a context

`WfContextTypedLrValid` certifies that each binding of a `TypingContext` is TYPED-LR-VALID — in the boxed
typed logical relation `TypedTypeValidityBoxed` (#1110) at some candidate box — in the prefix context that
precedes it.  This STRENGTHENS `WfContextDescPi` (which only says each binding `IsTypeDescPi`): it pairs each
entry's grown validity with a reducibility candidate, exactly what the Abel-reflection neutral arm of the
grown context-conversion piElim crux (GrownCtxConv-5, #842) requires.  The architectural finding of the
black-box-validity LR (the `transportNeutralArm` finding, #1112) is that discharging GrownCtxConv-5 needs the
neutral arm to RECONSTRUCT a neutral application's typing from its var-headed spine under a WELL-FORMED context
where each entry is itself LR-valid — and THIS predicate is that well-formed context.

## Why this is now possible (the universe-arm prerequisite)

The boxed typed LR became non-vacuous-at-closed-scope only once it had a universe arm (#1114): before that it
had no scope-0 inhabitant (the `neutral` arm needs a variable, hence scope ≥ 1; the `piType` arm recurses to
that base), so this predicate would have been vacuous beyond the empty context.  `wfContextTypedLrValid_universeBinding`
(non-vacuity below) is built directly on the universe arm's closed inhabitant `smoke_closedUniverseIsBoxedTypedValid`.

## What this file ships

  * `WfContextTypedLrValid` — the predicate (structural recursion over the telescope; each entry carries an
    EXISTENTIAL candidate box so a context can be well-formed without naming the candidates).
  * `emptyIsWellFormed` / `tailValid` / `headLrValid` / `cons` — the introduction + `And`-projection
    inversions (the primitives the neutral-spine reconstruction threads through a binder).
  * `toWfContextDescPi` — ★ SOUNDNESS: typed-LR-validity REFINES formation-validity (each entry's LR-validity
    gives `IsTypeDescPi` via `TypedTypeValidityBoxed.toIsTypeDescPi`), so a typed-LR-valid context is
    grown-well-formed.  The genuine content link, by structural recursion mirroring the predicate.
  * `wfContextTypedLrValid_universeBinding` — non-vacuity: a single universe-code binding is typed-LR-valid.

The next brick (deferred): the LOOKUP lemma (looking up index `i` gives a `TypedTypeValidityBoxed` for that
entry's weakened type) needs LR-weakening under context extension — a genuinely new proof, not a projection.

## Zero-axiom verification

Structural-recursion `def` + `And` projections + `toIsTypeDescPi` (the soundness link) + a constructor-based
non-vacuity witness on the universe-arm closed inhabitant.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Typed-LR context well-formedness: each binding is TYPED-LR-VALID (in `TypedTypeValidityBoxed` at some
candidate box) in the prefix context that precedes it.  Computed by structural recursion on the telescope.
Strengthens `WfContextDescPi` (which only certifies each binding `IsTypeDescPi`) by pairing each entry's grown
validity with a reducibility candidate — the well-formed context the Abel-reflection neutral arm needs. -/
def WfContextTypedLrValid {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Prop
  | _, .empty => True
  | _, .cons restContext bindingType =>
      WfContextTypedLrValid restContext ∧
        ∃ box : KripkeCandBox _, TypedTypeValidityBoxed profile restContext bindingType box

/-- The empty context is typed-LR-well-formed. -/
theorem WfContextTypedLrValid.emptyIsWellFormed {profile : PolyProfile} :
    WfContextTypedLrValid (profile := profile) .empty :=
  trivial

/-- Inversion: the prefix of a typed-LR-well-formed `cons` context is typed-LR-well-formed. -/
theorem WfContextTypedLrValid.tailValid {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextTypedLrValid (restContext.cons bindingType)) :
    WfContextTypedLrValid restContext :=
  wellFormed.1

/-- Inversion: the most-recent binding of a typed-LR-well-formed `cons` context is typed-LR-valid in the prefix
(carries a candidate box in the boxed typed LR). -/
theorem WfContextTypedLrValid.headLrValid {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextTypedLrValid (restContext.cons bindingType)) :
    ∃ box : KripkeCandBox scope, TypedTypeValidityBoxed profile restContext bindingType box :=
  wellFormed.2

/-- Introduction: extending a typed-LR-well-formed context by a binding that is typed-LR-valid in the prefix
yields a typed-LR-well-formed context.  The primitive the neutral-spine reconstruction threads into a binder. -/
theorem WfContextTypedLrValid.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restWellFormed : WfContextTypedLrValid restContext)
    (bindingLrValid :
      ∃ box : KripkeCandBox scope, TypedTypeValidityBoxed profile restContext bindingType box) :
    WfContextTypedLrValid (restContext.cons bindingType) :=
  ⟨restWellFormed, bindingLrValid⟩

/-- **★ Soundness: typed-LR-validity REFINES formation-validity.**  Each entry's LR-validity gives
`IsTypeDescPi` via `TypedTypeValidityBoxed.toIsTypeDescPi`, so a typed-LR-valid context is grown-well-formed
(`WfContextDescPi`).  The genuine content link — the typed-LR well-formedness is strictly more than the
formation well-formedness, and this discharges the difference.  By structural recursion mirroring the predicate. -/
theorem WfContextTypedLrValid.toWfContextDescPi {profile : PolyProfile} :
    {scope : Nat} → {context : TypingContext profile scope} →
    WfContextTypedLrValid context → WfContextDescPi context
  | _, .empty, _ => trivial
  | _, .cons _restContext _bindingType, wellFormed =>
      ⟨WfContextTypedLrValid.toWfContextDescPi wellFormed.1,
       match wellFormed.2 with
       | ⟨_box, lrValid⟩ => lrValid.toIsTypeDescPi⟩

/-- `WfContextTypedLrValid` is non-vacuous: a context binding a single universe code is typed-LR-valid (the
universe code is typed-LR-valid via the closed universe inhabitant `smoke_closedUniverseIsBoxedTypedValid`,
#1114 — the inhabitant that the universe arm unlocked).  Witnesses that this predicate is genuinely inhabited
at a non-empty context, NOT vacuously true only at `.empty`. -/
theorem wfContextTypedLrValid_universeBinding {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    WfContextTypedLrValid (profile := profile)
      ((TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag)) :=
  ⟨trivial, ⟨KripkeCandBox.mk snKripkeCand,
    smoke_closedUniverseIsBoxedTypedValid levelExpr flag⟩⟩

end FX1Poly.Typed
