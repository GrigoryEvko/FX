import LeanFX2.Foundation.Ty

/-! # Foundation/IsClosedTy — predicate identifying scope-closed types

A type is **closed** when it has no free type-variable references and
no raw-term endpoints — i.e., it is a fixed point of `Ty.weaken` and
`Ty.subst0` modulo the trivial scope index shift.

## Why this matters

The general subject-reduction theorem
`Step.preserves_isClosedTy : Step src tgt → IsClosedTy srcType → srcType = tgtType`
(landed in a follow-up commit) replaces the per-type
`Step.preserves_ty_unit / bool / nat` cascade with a single
inductive proof.  Conv cong rules over closed-typed positions
become 5-line proofs once general SR is in place.

## Closed ctors

`unit`, `bool`, `nat` — leaf constants, trivially closed.

`arrow A B`, `listType A`, `optionType A`, `eitherType A B` —
parametric: closed iff each component is closed.

## NOT closed

* `tyVar position` — refers to a context-bound type
* `id carrier left right` — endpoints are RawTerm; depend on scope
* `piTy d c`, `sigmaTy f s` — codomain at `scope+1` depends on a
  bound variable; not invariant under arbitrary substitution

The kernel-sprint.md §1.4 plan calls out a few additional closed
ctors (`empty`, `interval`, `universe lvl`, `record fields`).  Those
land when their ctor lands; the predicate is additive — adding a
ctor adds one new constructor case here.

## Decidability

The predicate is decidable by structural recursion on the type.
Each non-closed leaf returns `isFalse`; each parametric case
recurses and combines via `Decidable.imp` / `Decidable.and`.

## Pitfalls + mitigations

* P-1 (match-compiler propext on big inductives): Full enumeration
  in the decidable instance, no wildcards.
* P-2 (multi-Nat-index propext): `level` and `scope` hoisted to the
  function header before `:` — keeps pattern arity at 1 implicit.
* P-13 (Decidable instance synthesis): manual instance, do not rely
  on typeclass auto-resolution for compound predicates.

## Audit

Every declaration verified zero-axiom via
`#print axioms LeanFX2.IsClosedTy.X`.
-/

namespace LeanFX2

/-- A type is closed when it has no free type-variable references and
no raw-term endpoints.  Closed types are invariant under `Ty.weaken`
and `Ty.subst0` modulo scope shift.

Constructor coverage matches the current `Ty` ctor set; future ctors
(`empty`, `interval`, `universe`, `record`) extend this predicate
additively. -/
inductive IsClosedTy : ∀ {level scope : Nat}, Ty level scope → Prop
  | unit       {level scope : Nat} : IsClosedTy (Ty.unit (level := level) (scope := scope))
  | bool       {level scope : Nat} : IsClosedTy (Ty.bool (level := level) (scope := scope))
  | nat        {level scope : Nat} : IsClosedTy (Ty.nat  (level := level) (scope := scope))
  | arrow      {level scope : Nat} {domainType codomainType : Ty level scope}
               (closedDomain : IsClosedTy domainType)
               (closedCodomain : IsClosedTy codomainType) :
               IsClosedTy (Ty.arrow domainType codomainType)
  | listType   {level scope : Nat} {elementType : Ty level scope}
               (closedElement : IsClosedTy elementType) :
               IsClosedTy (Ty.listType elementType)
  | optionType {level scope : Nat} {elementType : Ty level scope}
               (closedElement : IsClosedTy elementType) :
               IsClosedTy (Ty.optionType elementType)
  | eitherType {level scope : Nat} {leftType rightType : Ty level scope}
               (closedLeft : IsClosedTy leftType)
               (closedRight : IsClosedTy rightType) :
               IsClosedTy (Ty.eitherType leftType rightType)
  | «universe» {level scope : Nat} (universeLevel : UniverseLevel) :
               IsClosedTy (Ty.universe (level := level) (scope := scope) universeLevel)
  -- D1.5 new closed-ctor witnesses.  Tagless leaves (`empty`, `interval`)
  -- are unconditionally closed.  Parametric ctors recurse on their Ty
  -- components only — RawTerm payloads (path/oeq/idStrict endpoints,
  -- glue boundary, refine predicate, session protocolStep, effect tag)
  -- depend on scope, so those ctors are NOT closed and don't appear here.
  | empty {level scope : Nat} :
      IsClosedTy (Ty.empty (level := level) (scope := scope))
  | interval {level scope : Nat} :
      IsClosedTy (Ty.interval (level := level) (scope := scope))
  | equiv {level scope : Nat} {domainType codomainType : Ty level scope}
          (closedDomain : IsClosedTy domainType)
          (closedCodomain : IsClosedTy codomainType) :
          IsClosedTy (Ty.equiv domainType codomainType)
  | record {level scope : Nat} {singleFieldType : Ty level scope}
           (closedSingleField : IsClosedTy singleFieldType) :
           IsClosedTy (Ty.record singleFieldType)
  | codata {level scope : Nat} {stateType outputType : Ty level scope}
           (closedState : IsClosedTy stateType)
           (closedOutput : IsClosedTy outputType) :
           IsClosedTy (Ty.codata stateType outputType)
  | modal {level scope : Nat} {modalityTag : Nat} {carrierType : Ty level scope}
          (closedCarrier : IsClosedTy carrierType) :
          IsClosedTy (Ty.modal modalityTag carrierType)

/-! ## Decidability

Manual instance per P-13.  Each case dispatches on the Ty ctor:
* Closed leaves return `isTrue` with the matching IsClosedTy ctor
* Non-closed leaves (`tyVar`, `id`, `piTy`, `sigmaTy`) return
  `isFalse` with `nomatch` on a fabricated proof
* Parametric cases recurse on inner types and combine
-/

/-- Decide whether a type is closed.  Structural recursion on the
type.  Zero-axiom — no propext leak via the dispatch pattern. -/
def IsClosedTy.decide {level : Nat} : ∀ {scope : Nat}
    (someType : Ty level scope), Decidable (IsClosedTy someType)
  | _, .unit => .isTrue .unit
  | _, .bool => .isTrue .bool
  | _, .nat  => .isTrue .nat
  | _, .arrow domainType codomainType =>
      match IsClosedTy.decide domainType, IsClosedTy.decide codomainType with
      | .isTrue closedDomain, .isTrue closedCodomain =>
          .isTrue (.arrow closedDomain closedCodomain)
      | .isFalse openDomain, _ =>
          .isFalse (fun closedArrow => by cases closedArrow; exact openDomain ‹_›)
      | _, .isFalse openCodomain =>
          .isFalse (fun closedArrow => by cases closedArrow; exact openCodomain ‹_›)
  | _, .piTy _ _ =>
      .isFalse (fun closedPiTy => nomatch closedPiTy)
  | _, .sigmaTy _ _ =>
      .isFalse (fun closedSigmaTy => nomatch closedSigmaTy)
  | _, .tyVar _ =>
      .isFalse (fun closedTyVar => nomatch closedTyVar)
  | _, .id _ _ _ =>
      .isFalse (fun closedId => nomatch closedId)
  | _, .listType elementType =>
      match IsClosedTy.decide elementType with
      | .isTrue closedElement => .isTrue (.listType closedElement)
      | .isFalse openElement =>
          .isFalse (fun closedList => by cases closedList; exact openElement ‹_›)
  | _, .optionType elementType =>
      match IsClosedTy.decide elementType with
      | .isTrue closedElement => .isTrue (.optionType closedElement)
      | .isFalse openElement =>
          .isFalse (fun closedOpt => by cases closedOpt; exact openElement ‹_›)
  | _, .eitherType leftType rightType =>
      match IsClosedTy.decide leftType, IsClosedTy.decide rightType with
      | .isTrue closedLeft, .isTrue closedRight =>
          .isTrue (.eitherType closedLeft closedRight)
      | .isFalse openLeft, _ =>
          .isFalse (fun closedEither => by cases closedEither; exact openLeft ‹_›)
      | _, .isFalse openRight =>
          .isFalse (fun closedEither => by cases closedEither; exact openRight ‹_›)
  | _, .universe universeLevel => .isTrue (.universe universeLevel)
  -- D1.5 decidable-closed dispatch for the 13 new ctors.
  | _, .empty => .isTrue .empty
  | _, .interval => .isTrue .interval
  | _, .path _ _ _ =>
      .isFalse (fun closedPath => nomatch closedPath)
  | _, .glue _ _ =>
      .isFalse (fun closedGlue => nomatch closedGlue)
  | _, .oeq _ _ _ =>
      .isFalse (fun closedOeq => nomatch closedOeq)
  | _, .idStrict _ _ _ =>
      .isFalse (fun closedIdStrict => nomatch closedIdStrict)
  | _, .equiv domainType codomainType =>
      match IsClosedTy.decide domainType, IsClosedTy.decide codomainType with
      | .isTrue closedDomain, .isTrue closedCodomain =>
          .isTrue (.equiv closedDomain closedCodomain)
      | .isFalse openDomain, _ =>
          .isFalse (fun closedEquiv => by cases closedEquiv; exact openDomain ‹_›)
      | _, .isFalse openCodomain =>
          .isFalse (fun closedEquiv => by cases closedEquiv; exact openCodomain ‹_›)
  | _, .refine _ _ =>
      .isFalse (fun closedRefine => nomatch closedRefine)
  | _, .record singleFieldType =>
      match IsClosedTy.decide singleFieldType with
      | .isTrue closedSingleField => .isTrue (.record closedSingleField)
      | .isFalse openSingleField =>
          .isFalse (fun closedRecord => by cases closedRecord; exact openSingleField ‹_›)
  | _, .codata stateType outputType =>
      match IsClosedTy.decide stateType, IsClosedTy.decide outputType with
      | .isTrue closedState, .isTrue closedOutput =>
          .isTrue (.codata closedState closedOutput)
      | .isFalse openState, _ =>
          .isFalse (fun closedCodata => by cases closedCodata; exact openState ‹_›)
      | _, .isFalse openOutput =>
          .isFalse (fun closedCodata => by cases closedCodata; exact openOutput ‹_›)
  | _, .session _ =>
      .isFalse (fun closedSession => nomatch closedSession)
  | _, .effect _ _ =>
      .isFalse (fun closedEffect => nomatch closedEffect)
  | _, .modal _ carrierType =>
      match IsClosedTy.decide carrierType with
      | .isTrue closedCarrier => .isTrue (.modal closedCarrier)
      | .isFalse openCarrier =>
          .isFalse (fun closedModal => by cases closedModal; exact openCarrier ‹_›)

instance IsClosedTy.decidable {level scope : Nat} (someType : Ty level scope) :
    Decidable (IsClosedTy someType) :=
  IsClosedTy.decide someType

/-! ## Smoke samples

Verify the predicate computes correctly on a handful of representative
types.  Every assertion below is decidable + reduces to the expected
truth value at compile time.
-/

example : IsClosedTy (Ty.unit (level := 0) (scope := 0)) := .unit
example : IsClosedTy (Ty.bool (level := 0) (scope := 0)) := .bool
example : IsClosedTy (Ty.nat  (level := 0) (scope := 0)) := .nat

example : IsClosedTy
    (Ty.arrow (Ty.nat (level := 0) (scope := 0)) Ty.bool) :=
  .arrow .nat .bool

example : IsClosedTy
    (Ty.listType (Ty.nat (level := 0) (scope := 0))) :=
  .listType .nat

example : IsClosedTy
    (Ty.eitherType (Ty.nat (level := 0) (scope := 0)) Ty.bool) :=
  .eitherType .nat .bool

/-- A type variable is NOT closed. -/
example : ¬ IsClosedTy (Ty.tyVar (level := 0) (scope := 1) ⟨0, by decide⟩) :=
  fun closedTyVar => nomatch closedTyVar

/-- An identity type (with raw endpoints) is NOT closed even when its
carrier is. -/
example : ¬ IsClosedTy
    (Ty.id (level := 0) (scope := 0) Ty.nat RawTerm.unit RawTerm.unit) :=
  fun closedId => nomatch closedId

/-- piTy is NOT closed (the codomain depends on the bound variable). -/
example : ¬ IsClosedTy
    (Ty.piTy (level := 0) (scope := 0) Ty.nat Ty.bool) :=
  fun closedPi => nomatch closedPi

end LeanFX2
