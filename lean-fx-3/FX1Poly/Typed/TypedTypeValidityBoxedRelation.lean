import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.KripkeCandidateRenameClosure
import FX1Poly.Core.NeutralTerm

/-! # FX1Poly/Typed/TypedTypeValidityBoxedRelation
    — the CANDIDATE-INDEXED typed type-validity logical relation (design A: boxed candidate index)

## Where this sits

`TypedTypeValidityRelation.lean` (#1109) DEFINED the typed type-validity logical relation for GCC-5 (#842)
with the candidate as a stored ARGUMENT, because a function-valued `KripkeCand` cannot be a dependent index
(Lean's dependent eliminator fails to unify the eta-expanded `fun {ts} => candidate`).  That first cut
REVEALED the design constraint but is a DEAD END for the Π-FORMER arm: with the candidate an argument (not an
index), the Π-former cannot read its sub-derivations' candidates inside a constructor declaration — it cannot
build the dependent-arrow candidate `kripkeArrowDep (domain candidate) (codomain family)` from the parts.

This file resolves the firing-19 spike: ★ DESIGN A (GO) — wrap `KripkeCand` in a FIRST-ORDER structure
`KripkeCandBox` and index the relation by the BOX.  A structure-valued index is NOT function-valued, so the
eta-expansion that broke dependent elimination does not arise; `cases` fires (`toIsTypeDescPi` below), AND an
arm CAN read a sub-derivation's box index — so the Π-former threads `domainBox.run` into the dependent arrow
(`piType` arm).  The candidate is now a genuine INDEX, recoverable from outside the relation
(`indexCandidate`) — exactly what the first cut could not do.

## The arms (this firing)

  * `neutral` — a NEUTRAL type code is typed-valid at the SN Kripke candidate (`snKripkeCand`, #1108) boxed.
    The base case of the open type-level neutral reflection.
  * `piType` — a `Π` type code is typed-valid at the dependent-arrow candidate
    `kripkeArrowDep domainBox.run codomainFamily`, built by THREADING the domain sub-derivation's exposed
    candidate.  This is the arm the candidate-as-argument design (#1109) structurally could not express.

## Honest boundary (the next brick)

The `piType` arm currently takes the `codomainFamily : KripkeCodFamily scope` as FREE data alongside the
codomain sub-derivation (whose candidate is at `scope + 1`).  Tying the family to the codomain's
interpretation — the candidate-INSTANTIATION operation lifting a `KripkeCandBox (scope + 1)` to a
`KripkeCodFamily scope` indexed by the substituted argument — is the next brick.  The arm is structurally
correct (a Π's interpretation IS a dependent arrow of the domain candidate and a codomain family) and threads
the domain candidate; the codomain-family derivation is deferred, not faked.  Transport-across-context-
conversion + the fundamental theorem (completeness) follow once the family operation lands.

## Supersession note

`TypedTypeValidityBoxed` (this file) is the CANONICAL candidate-indexed design going forward;
`TypedTypeValidity` (#1109, candidate-as-argument) is retained as the first-cut that revealed the constraint
(kept per the refactor-by-addition discipline; its removal needs explicit approval).

## Zero-axiom verification

The relation is a plain inductive; soundness is a two-arm `cases`; the candidate recovery and the non-vacuity
smoke are direct.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe FX1Poly.Foundation

/-- **A first-order box around a Kripke candidate.**  Wrapping `KripkeCand` (which is FUNCTION-valued,
`∀ {targetScope}, RawRenaming … → RawTerm … → Prop`) in a structure makes it a first-order value, so it can
serve as a dependent INDEX of the relation below without triggering the function-valued-index dependent-
elimination failure (the eta-expanded `fun {ts} => candidate` unification that blocked `cases` on the
candidate-as-argument first cut #1109). -/
structure KripkeCandBox (scope : Nat) where
  /-- The wrapped Kripke candidate. -/
  run : KripkeCand scope

/-- **The candidate-INDEXED typed type-validity logical relation** (design A).  Indexed by `(context,
typeCode, candidate-box)`: the candidate is a genuine INDEX (boxed first-order), so arms can read their
sub-derivations' candidates — the capability the candidate-as-argument first cut (#1109) lacked, and the one
the Π-former needs.  The Kripke-model interpretation of a valid type code, pairing the reducibility candidate
(now an index) with the `IsTypeDescPi` typing witness. -/
inductive TypedTypeValidityBoxed (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → KripkeCandBox scope → Prop where
  /-- A NEUTRAL type code is typed-valid at the SN Kripke candidate (`snKripkeCand`, #1108) boxed, together
  with its `IsTypeDescPi` typing witness.  The base case of the open type-level neutral reflection on which the
  GCC-5 residual bottoms out; context conversion is free here because `snKripkeCand` is rename-invariant. -/
  | neutral {scope : Nat} {context : TypingContext profile scope} {typeCode : RawTerm scope}
      (neutralCode : IsNeutral typeCode)
      (validity : IsTypeDescPi profile context typeCode) :
      TypedTypeValidityBoxed profile context typeCode (KripkeCandBox.mk snKripkeCand)
  /-- A `Π` type code is typed-valid at the dependent-arrow candidate `kripkeArrowDep domainBox.run
  codomainFamily`, built by THREADING the domain sub-derivation's exposed candidate `domainBox.run` (the
  capability the boxed INDEX unlocks).  `codomainFamily` is currently free data alongside the codomain
  sub-derivation (its candidate `codomainBox` lives at `scope + 1`); tying the family to the codomain's
  interpretation is the next brick (see file header). -/
  | piType {scope : Nat} {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainBox : KripkeCandBox scope} {codomainBox : KripkeCandBox (scope + 1)}
      (codomainFamily : KripkeCodFamily scope)
      (domainValid : TypedTypeValidityBoxed profile context domainCode domainBox)
      (codomainValid :
        TypedTypeValidityBoxed profile (context.cons domainCode) codomainCode codomainBox)
      (validity : IsTypeDescPi profile context (piTyCodeCell domainCode codomainCode)) :
      TypedTypeValidityBoxed profile context (piTyCodeCell domainCode codomainCode)
        (KripkeCandBox.mk (kripkeArrowDep domainBox.run codomainFamily))

/-- **Soundness: the relation carries the grown type validity**, over BOTH arms (neutral + Π-former).  The
half that feeds the GCC-5 residual: once transport across context conversion is proved ON the relation,
`IsTypeDescPi sourceCtx (Π D C)` → (completeness) the relation → (transport) the relation at the target →
(this soundness) `IsTypeDescPi targetCtx (Π D C)`.  The two-arm `cases` FIRES — the boxed (structure-valued)
index does not trigger the dependent-elimination failure that the function-valued candidate index would. -/
theorem TypedTypeValidityBoxed.toIsTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityBoxed profile context typeCode box) :
    IsTypeDescPi profile context typeCode := by
  cases relation with
  | neutral _ validity => exact validity
  | piType _ _ _ validity => exact validity

/-- **The candidate is a readable INDEX** (the design-A unlock).  The boxed candidate is visible in the
relation's type, so it can be projected from outside — `box.run` is the type code's semantic interpretation.
This is EXACTLY what the candidate-as-argument first cut (#1109) could not provide, and the reason the Π-former
arm above can thread `domainBox.run` into the dependent arrow. -/
def TypedTypeValidityBoxed.indexCandidate {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope} {box : KripkeCandBox scope}
    (_relation : TypedTypeValidityBoxed profile context typeCode box) :
    KripkeCand scope :=
  box.run

/-- **Non-vacuity: a variable type code with a validity witness is typed-valid** at the boxed SN candidate.
The base leaf of the open type-level neutral reflection; demonstrates the relation is inhabited. -/
theorem smoke_variableTypeIsBoxedTypedValid {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (index : Fin scope)
    (validity : IsTypeDescPi profile context (.mkGen .gen_var index .childNil)) :
    TypedTypeValidityBoxed profile context (.mkGen .gen_var index .childNil)
      (KripkeCandBox.mk snKripkeCand) :=
  TypedTypeValidityBoxed.neutral (IsNeutral.var index) validity

/-! ## The canonical codomain family — closing the Π-former's free-family gap (the firing-20 next brick)

The `piType` arm leaves `codomainFamily : KripkeCodFamily scope` as a parameter.  For the type-VALIDITY logical
relation (which is what the GCC-5 residual `ConvContextPreservesPiValidity` needs — `Π D C` inhabits a
universe, NOT the membership semantics of `Π`'s inhabitants) the codomain family does NOT have to depend on
the argument: it only has to EXIST and TRANSPORT.  The canonical choice is the SN codomain family
`snKripkeCodFamily`, the codomain analogue of the SN Kripke candidate `snKripkeCand` (#1108) — so the Π-former
candidate is `kripkeArrowDep domainBox.run snKripkeCodFamily`, DERIVED, no longer free data.

★ Why the SN family and not a genuine codomain-instantiation: a genuinely-dependent codomain family
`fun ρ arg t => t ∈ ⟦codomain[binder ↦ arg]⟧` would need to INSTANTIATE the codomain candidate (a
`KripkeCand (scope + 1)`) with the TERM argument `arg`.  But `KripkeCand` is indexed by RENAMINGS
(`RawRenaming = Fin → Fin`, variable↦variable), which cannot encode a term substitution — so the renaming-
indexed Kripke candidate is structurally UNABLE to be instantiated with a term.  A substitution-indexed Kripke
candidate would be a separate, larger refactor of the shipped Kripke substrate (#1104-1108).  For type
validity the SN family suffices; the substitution-Kripke generalization is reserved for the member-level
(canonicity) semantics, off the GCC-5 critical path. -/

/-- **The SN codomain family** — the index-and-argument-ignoring codomain family whose members at every
renaming and argument are exactly the strongly-normalizing terms (the codomain analogue of `snKripkeCand`,
#1108).  The canonical codomain family for the type-validity logical relation. -/
def snKripkeCodFamily {scope : Nat} : KripkeCodFamily scope :=
  fun {_targetScope} _indexRenaming _argument term => IsStronglyNormalizing term

/-- **Rename-invariance of the SN codomain family** (transport = IDENTITY, `Iff.rfl`).  The codomain-family
twin of `snKripkeCand_transport_pointwise` (#1108): context conversion (a change of renaming index) acts as
the identity on the SN codomain family, so the Π-former candidate built from it transports freely. -/
theorem snKripkeCodFamily_transport_pointwise {scope renamedScope : Nat}
    (forwardRenaming : RawRenaming scope renamedScope)
    {targetScope : Nat} (indexRenaming : RawRenaming renamedScope targetScope)
    (argument term : RawTerm targetScope) :
    KripkeCodFamily.transport forwardRenaming (snKripkeCodFamily) indexRenaming argument term ↔
      snKripkeCodFamily indexRenaming argument term :=
  Iff.rfl

/-- **The Π-former with its codomain family DERIVED from the canonical SN family** (closes the free-`codomainFamily`
gap for type validity).  A `Π` type code is typed-valid at `kripkeArrowDep domainBox.run snKripkeCodFamily`,
built from the domain sub-derivation's exposed candidate and the CANONICAL SN codomain family — no free family
data at the call site.  The codomain-family-instantiated specialization of the `piType` arm; the form the
fundamental theorem's Π case will use to construct the relation for `Π D C` from D's and C's validities. -/
theorem piTypeViaSnCodFamily {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {domainBox : KripkeCandBox scope} {codomainBox : KripkeCandBox (scope + 1)}
    (domainValid : TypedTypeValidityBoxed profile context domainCode domainBox)
    (codomainValid :
      TypedTypeValidityBoxed profile (context.cons domainCode) codomainCode codomainBox)
    (validity : IsTypeDescPi profile context (piTyCodeCell domainCode codomainCode)) :
    TypedTypeValidityBoxed profile context (piTyCodeCell domainCode codomainCode)
      (KripkeCandBox.mk (kripkeArrowDep domainBox.run snKripkeCodFamily)) :=
  TypedTypeValidityBoxed.piType snKripkeCodFamily domainValid codomainValid validity

end FX1Poly.Typed
