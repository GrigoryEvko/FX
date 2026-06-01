import FX1Poly.Core.ReducibleMember

/-! # FX1Poly/Core/ReducibleTypeClosed
    — the pointwise-saturation of `ReducibleType`, carrying the CANONICAL candidate (choice-free piIntro)

The fundamental theorem's `piIntro` arm (`IsReducibleMember.abstraction`) needs the codomain's
reducibility candidate as a UNIFORM FUNCTION of the argument (`codomainCandidate : RawTerm → (RawTerm →
Prop)`), but the type-formation induction hypothesis only supplies it EXISTENTIALLY (for each argument,
SOME candidate is reducible — `∀ arg, ∃ cand, ReducibleType (subst0 cod arg) cand`).  Turning that into a
uniform function is a CHOICE obstruction.  The standard resolution is the CANONICAL candidate — a type's
own member-predicate `IsReducibleMember typeCode` — chosen WITHOUT choice because it is definitionally a
function of the type.  But the bare inductive `ReducibleType` cannot host it: the `neutral` arm hard-codes
`IsStronglyNormalizing`, so `ReducibleType A (IsReducibleMember A)` is NOT derivable (there is no
pointwise-congruence arm, and adding one cascades through every `cases ReducibleType` site).

`ReducibleTypeClosed` is the non-cascading fix — the POINTWISE-SATURATION of `ReducibleType`:

  `ReducibleTypeClosed typeCode candidate := ∃ baseCandidate,
      ReducibleType typeCode baseCandidate ∧ PointwiseIff baseCandidate candidate`.

It is closed under pointwise-iff BY CONSTRUCTION (no inductive change), so it DOES carry the canonical
member-predicate candidate (`closedAtMemberPredicate`), while every base `ReducibleType` is included
(`toClosed`).  Because `ReducibleType` is functional up to pointwise-iff (`ReducibleType.deterministic`),
`ReducibleTypeClosed typeCode candidate` holds IFF `candidate` is pointwise-equal to the type's unique base
candidate — so the saturation adds exactly the pointwise-closure and nothing else.  The level-free FT's
choice-free `piIntro` is then built over this saturated layer (subsequent tasks add the piType / neutral /
abstraction rules over `ReducibleTypeClosed`, each inheriting from `ReducibleType` + a pointwise transport).

## Zero-axiom verification

`toClosed` is the reflexive witness (`PointwiseIff` refl is `fun _ => Iff.rfl`); `closedAtMemberPredicate`
is the existential triple whose pointwise leg is the forward inclusion (a member witness) and the backward
projection through `ReducibleType.deterministic` (the type's candidate is unique up to pointwise-iff).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **The pointwise-saturation of the dependent reducibility relation.**  A type-code denotes `candidate`
in the saturated relation when it denotes SOME pointwise-equivalent base candidate in `ReducibleType`.
This is closed under pointwise-iff by construction (the property `ReducibleType` lacks), which is exactly
what lets it host the canonical member-predicate candidate the choice-free `piIntro` needs. -/
def ReducibleTypeClosed {scope : Nat} (typeCode : RawTerm scope)
    (candidate : RawTerm scope → Prop) : Prop :=
  ∃ baseCandidate : RawTerm scope → Prop,
    ReducibleType typeCode baseCandidate ∧ PointwiseIff baseCandidate candidate

/-- Every base reducible type is a saturated reducible type at the same candidate (the reflexive
inclusion: pick the base candidate itself, with the reflexive pointwise witness). -/
theorem ReducibleType.toClosed {scope : Nat} {typeCode : RawTerm scope}
    {candidate : RawTerm scope → Prop} (reducible : ReducibleType typeCode candidate) :
    ReducibleTypeClosed typeCode candidate :=
  ⟨candidate, reducible, fun _term => Iff.rfl⟩

/-- **The canonical candidate is a saturated candidate (the choice-free `piIntro` keystone).**  A
reducible type's OWN member-predicate `IsReducibleMember typeCode` is a `ReducibleTypeClosed` candidate —
the canonical, choice-free candidate function the codomain's existential type-induction-hypothesis
supplies to the binder arm.  Pointwise: forward, a candidate member exhibits itself as a reducible member
(`⟨candidate, reducible, ·⟩`); backward, a reducible member's witnessing candidate coincides with `candidate`
by `ReducibleType.deterministic`.  Unprovable for bare `ReducibleType` (the `neutral` arm hard-codes
`IsStronglyNormalizing`); the saturation is precisely what supplies it. -/
theorem ReducibleType.closedAtMemberPredicate {scope : Nat} {typeCode : RawTerm scope}
    {candidate : RawTerm scope → Prop} (reducible : ReducibleType typeCode candidate) :
    ReducibleTypeClosed typeCode (IsReducibleMember typeCode) :=
  ⟨candidate, reducible, fun term =>
    ⟨fun candidateHolds => ⟨candidate, reducible, candidateHolds⟩,
     fun memberHolds =>
       have ⟨_witnessCandidate, witnessReducible, witnessHolds⟩ := memberHolds
       (ReducibleType.deterministic witnessReducible reducible term).mp witnessHolds⟩⟩

end FX1Poly.Core
