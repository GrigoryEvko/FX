import FX1Poly.Tier0.FxBaseSubstWitnessScone
import FX1Poly.Core.DataReducibilityCoverage

/-! # FX1Poly/Tier0/FxBaseSubstConcreteScone
    — concrete data-canonicity scones over the term base (brick 9, capstone of the term-carrying CwR arc)

`FxBaseSubstWitnessScone.lean` (SUBSTVEC-8) shipped the GENERIC bridge `witnessScone`: any closed-scope Path-A
`SconingWitness` becomes a Tier-0 categorical `SconingObject` over the term base.  This file grounds that abstract
bridge in CONCRETE data canonicity, by feeding the shipped data-reducibility candidates
(`DataReducibilityCoverage.lean`, SN-082) through it.  Each candidate becomes a `reducibilityScone` (SN-092, the
identity-fundamental instance — candidate membership IS the well-typed predicate, so the witness is the honest
"candidate member ⟹ strongly normalizing" sconing witness, via CR1), and `witnessScone` lifts it to a concrete
predicate-carrying categorical scone whose semantic domain is the type's canonical closed terms.  It is the
term-base categorical analog of the Core track's `BoolCanonicityViaSconing` / `ConsistencyViaSconing`.

## What lands here (all zero-axiom)

  * `boolValueScone : SconingObject fxBaseSubstCategory fxBaseSubstGlobalSections` — the concrete scone whose
    semantic domain is the BOOL-canonical closed terms (`CanonicalFormsPredicate boolIsValue`), realized into the
    global sections.
  * `boolValueScone_semanticIsStronglyNormalizing` — its semantic domain consists of STRONGLY-NORMALIZING closed
    terms (the canonicity content extracted through `witnessScone_semanticIsCanonical` = CR1).
  * `boolValueScone_inhabited` — NON-VACUITY: the bool-value scone's semantic domain is inhabited (`boolTrueCell`),
    so this is not a scone over an empty predicate.
  * **`emptyValueScone`** — the CONSISTENCY scone: the scone whose semantic domain is the EMPTY-canonical closed
    terms.
  * **`emptyValueScone_semanticIsUninhabited`** — its semantic domain is EMPTY (no closed member, via
    `emptyFamilyCandidateHasNoClosedMember`): the categorical consistency core, a non-trivial sconing object whose
    semantic domain is the genuine bottom.

## Honest scope boundary

These are CONCRETE instances of the SUBSTVEC-8 bridge at two shipped data candidates (bool = inhabited canonical
data; empty = the uninhabited consistency bottom), demonstrating the categorical scone genuinely carries real
data-type canonicity predicates.  The `reducibilityScone` here uses the IDENTITY fundamental (`isWellTyped :=
candidate`), so the scone's `isWellTyped` is candidate-membership, NOT the kernel's `HasTypeDescPi` typing — wiring
the DEEP fundamental (every closed well-typed term of `bool` is a bool-value) is a separate step that consumes the
closed typed fundamental theorem.  The same construction applies to all ten `DataFormerFamily` candidates; bool +
empty are the representative inhabited / bottom poles.

## Zero-axiom verification

`boolValueScone` / `emptyValueScone` are `witnessScone (reducibilityScone family.hasReducibilityCandidate
(fun _ h => h))` — composition of the shipped `DataFormerFamily.hasReducibilityCandidate` (SN-082) + `reducibilityScone`
(SN-092) + `witnessScone` (SUBSTVEC-8).  `_semanticIsStronglyNormalizing` is `witnessScone_semanticIsCanonical`
(isCanonical = `IsStronglyNormalizing`).  `_inhabited` destructs `boolFamilyCandidateInhabited` into a subtype
element.  `_semanticIsUninhabited` applies `emptyFamilyCandidateHasNoClosedMember` to the subtype's `property`.
No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Core.StepStar

/-- **A concrete predicate-carrying Tier-0 scone: the bool-canonical closed terms.**  Feed the shipped bool
reducibility candidate (with the identity fundamental) through the SUBSTVEC-8 bridge; its semantic domain is the
BOOL-canonical closed terms (`CanonicalFormsPredicate boolIsValue`), realized into the global sections. -/
def boolValueScone : SconingObject fxBaseSubstCategory fxBaseSubstGlobalSections :=
  witnessScone (reducibilityScone
    (DataFormerFamily.boolFamily.hasReducibilityCandidate (scope := 0))
    (fun _term hMember => hMember))

/-- The bool-value scone's semantic domain consists of STRONGLY-NORMALIZING closed terms — the canonicity content
extracted through the witness (CR1: a reducibility-candidate member is strongly normalizing). -/
theorem boolValueScone_semanticIsStronglyNormalizing (member : boolValueScone.semanticDomain) :
    IsStronglyNormalizing member.val :=
  witnessScone_semanticIsCanonical
    (reducibilityScone (DataFormerFamily.boolFamily.hasReducibilityCandidate (scope := 0))
      (fun _term hMember => hMember)) member

/-- **Non-vacuity:** the bool-value scone's semantic domain is inhabited (`boolTrueCell` is a bool-canonical closed
term), so the scone is over a genuinely-inhabited canonicity predicate, not an empty one. -/
theorem boolValueScone_inhabited : Nonempty boolValueScone.semanticDomain :=
  match boolFamilyCandidateInhabited (scope := 0) with
  | ⟨closedMember, isMember⟩ => ⟨⟨closedMember, isMember⟩⟩

/-- **The consistency scone: the empty-canonical closed terms.**  Feed the shipped empty reducibility candidate
through the SUBSTVEC-8 bridge; its semantic domain is the EMPTY-canonical closed terms (the genuine bottom). -/
def emptyValueScone : SconingObject fxBaseSubstCategory fxBaseSubstGlobalSections :=
  witnessScone (reducibilityScone
    (DataFormerFamily.emptyFamily.hasReducibilityCandidate (scope := 0))
    (fun _term hMember => hMember))

/-- **The categorical consistency core:** the empty-value scone's semantic domain is EMPTY — there is no closed
member of the empty type's canonical-forms candidate (`emptyFamilyCandidateHasNoClosedMember`).  A non-trivial
sconing object whose semantic domain is the genuine bottom. -/
theorem emptyValueScone_semanticIsUninhabited (member : emptyValueScone.semanticDomain) : False :=
  emptyFamilyCandidateHasNoClosedMember member.property

end FX1Poly.Tier0
