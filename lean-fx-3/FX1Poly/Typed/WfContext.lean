import FX1Poly.Typed.HasType

/-! # FX1Poly/Typed/WfContext — context well-formedness (TY-WF)

`TypingContext` (#467) is a RAW de Bruijn telescope: it stores binding-type
cells with NO typing constraint, by design (a typing-well-formedness field
inside `cons` would put `HasType`/`IsType` in the inductive's INDEX
signature — the mutual-index wall Lean 4 rejects).  `WfContext` is the
SEPARATE predicate that layers well-formedness OVER that raw spine: a
context is well-formed when every binding's type is genuinely a type
(`IsType`) in its own prefix context.

This is the dim-0 `.context`-sort soundness wrapper, sibling to `HasType`
(the `.term`-over-`.type` wrapper): a raw telescope is admitted by
construction; `WfContext` is the certificate that it is sound.

## A computed `def`, not an inductive

`WfContext` is defined by structural recursion on the telescope rather than
as an inductive.  That makes its inversions definitional `And` projections
(`tailWellFormed` / `headIsType` are `.1` / `.2`), which are propext-free —
whereas `cases` on a `cons`-indexed `Prop` inductive leaks `propext`
discharging the impossible `empty` case (the cons-index match-compiler
trap).  Well-formedness is a CONDITION, not a derivation object, so the
computed form is the natural choice (and mirrors `TypingContext.lookup`).

## Now non-vacuous

Until the `universeFormation` rule landed (#442), `IsType` was empty —
nothing inhabited a universe — so `WfContext` held only for the empty
context.  Now a universe-code binding is provably a type
(`wfContext_universeBinding`), so `WfContext` is meaningfully inhabited.
The well-formedness predicate has teeth exactly because the typing core
grounds `IsType`.

## Zero-axiom verification

Structural-recursion `def` + `And` projections + a constructor-based
witness.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A `TypingContext` is well-formed when each binding's type is a type
(`IsType`) in the prefix context that precedes it.  Computed by structural
recursion on the telescope; layered OVER the raw telescope, never inside it
(see the file header on the mutual-index wall). -/
def WfContext {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Prop
  | _, .empty => True
  | _, .cons restContext bindingType =>
      WfContext restContext ∧ IsType profile restContext bindingType

/-- The empty context is well-formed. -/
theorem WfContext.emptyIsWellFormed {profile : PolyProfile} :
    WfContext (profile := profile) .empty :=
  trivial

/-- Inversion: the prefix of a well-formed `cons` context is well-formed. -/
theorem WfContext.tailWellFormed {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContext (restContext.cons bindingType)) :
    WfContext restContext :=
  wellFormed.1

/-- Inversion: the most-recent binding of a well-formed `cons` context is a
type in the prefix. -/
theorem WfContext.headIsType {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContext (restContext.cons bindingType)) :
    IsType profile restContext bindingType :=
  wellFormed.2

/-- Introduction (inverse of `tailWellFormed` + `headIsType`): extending a
well-formed context by a binding that is a type in the prefix yields a
well-formed context.  The primitive a recursive type-former checker needs to
thread well-formedness into a codomain checked under `Γ.cons dom` — e.g. the
#443 Π-formation decider, where the codomain premise lives at `scope + 1`. -/
theorem WfContext.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restWellFormed : WfContext restContext)
    (bindingIsType : IsType profile restContext bindingType) :
    WfContext (restContext.cons bindingType) :=
  ⟨restWellFormed, bindingIsType⟩

/-- `WfContext` is non-vacuous: a context binding a single universe code is
well-formed, because the universe code is a type (`universeFormation`).
This is the payoff of grounding `IsType` (#442) — the well-formedness
predicate is now inhabited beyond the empty context. -/
theorem wfContext_universeBinding {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    WfContext (profile := profile)
      ((TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag)) :=
  ⟨trivial,
    ⟨levelExpr.lsucc, flag,
      HasType.universeFormation (TypingContext.empty : TypingContext profile 0)
        levelExpr flag⟩⟩

end FX1Poly.Typed
