import FX1Poly.Typed.HasType

/-! # FX1Poly/Typed/HasTypeConsistency
    — the closed-typing characterization (P10 consistency precursor, native pi/sigma-formation HasType core)

The payoff direction (polycell.md §11.8 P10): canonicity ⇒ consistency
(`HasType .empty t Empty → False`).  On the native pi/sigma-formation HasType core — `var` / `conv`
/ `universeFormation` / `piFormation` / `sigmaFormation`, all type-formers with
NO term-introduction arms yet — this takes a sharp, honest shape: **every closed
well-typed subject is itself a type.**  There are no closed proper TERMS at all
on this fragment (a proper term would be a `lam` / `pair` / `natZero` / …, none
of which has a typing arm here), so the closed `.term` layer below the universe
is empty.

```
HasType.closedSubjectIsType : HasType profile .empty t T → IsType profile .empty t
```

This is the fragment's consistency content: the only closed-typeable cells are
universe / Π / Σ CODES, each classified by a universe code — none is a closed
inhabitant of a non-universe classifier.  With a hypothetical empty type
(`gen_empty` / `never`) and term-introduction arms, the statement refines
(closed terms become "type OR canonical value").  On the native pi/sigma-formation HasType core the
degeneracy is the honest, checkable truth, and `HasType .empty t
(nonUniverseClassifier)` is structurally impossible.

## What this brick delivers

* `HasType.subjectIsVariableOrIsType` — the induction-friendly engine: in ANY
  context, a typed subject is either a variable cell or a type (`IsType`).  By
  induction on the derivation — `var` is a variable; `universeFormation` /
  `piFormation` / `sigmaFormation` each witness `IsType` from their OWN
  conclusion derivation (the universe / Π / Σ code inhabits the universe the arm
  produces); `conv` forwards its IH (same subject).  Distinct from the shape
  classification `subjectIsVariableOrTypeFormerCode` — that recovers the
  subject SHAPE; this recovers the semantic `IsType` witness (not derivable from
  the shape alone, which lacks the formation derivation).
* `HasType.closedSubjectIsType` — the closed corollary: in the empty context the
  variable case is impossible (`Fin 0`), so every closed typed subject is a type.

## Zero-axiom verification

Induction over `HasType` (constant-shape motive ⇒ `HasType.rec`, no index cast)
+ the `IsType` existential witnessed per arm + a `Fin 0` refutation via
`Nat.not_lt_zero` (NOT `Fin.cases`/`Fin.elim0` — those route through the OfNat /
casesOn propext trap, see the Fin-cases-axiom lesson).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- In any context, a typed subject is either a variable cell or a type
(`IsType`).  The induction-friendly engine of the closed-typing
characterization: each non-`conv` arm witnesses `IsType` from its own
conclusion derivation, and `conv` forwards its IH unchanged (the subject is
preserved).  Context-general so the binder-extending `piFormation` /
`sigmaFormation` arms (whose codomain IH lives in `context.cons …`) type-check
— the empty-context restriction is applied afterward in
`closedSubjectIsType`. -/
theorem HasType.subjectIsVariableOrIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    (∃ index : Fin scope, subject = variableCell index) ∨
      IsType profile context subject := by
  induction typed with
  | var context index => exact Or.inl ⟨index, rfl⟩
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihTypedPremise ihReclassifier =>
      exact ihTypedPremise
  | universeFormation context levelExpr flag =>
      exact Or.inr ⟨levelExpr.lsucc, flag,
        HasType.universeFormation context levelExpr flag⟩
  | piFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      exact Or.inr ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
        HasType.piFormation context domainCode codomainCode
          domainLevel codomainLevel flag domainTyped codomainTyped⟩
  | sigmaFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      exact Or.inr ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
        HasType.sigmaFormation context domainCode codomainCode
          domainLevel codomainLevel flag domainTyped codomainTyped⟩

/-- P10 consistency precursor (native pi/sigma-formation HasType core): every closed well-typed
subject is itself a type.  In the empty context the variable disjunct of
`subjectIsVariableOrIsType` is impossible (`Fin 0` has no inhabitant), so the
`IsType` disjunct always holds.  Fragment-specific scope: it states that the
type-former-only fragment has NO closed proper terms (the closed `.term` layer
below the universe is empty); term-introduction arms would refine it. -/
theorem HasType.closedSubjectIsType {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasType profile TypingContext.empty subject classifier) :
    IsType profile TypingContext.empty subject := by
  rcases typed.subjectIsVariableOrIsType with ⟨index, _⟩ | isTypeSubject
  · exact absurd index.isLt (Nat.not_lt_zero index.val)
  · exact isTypeSubject

end FX1Poly.Typed
