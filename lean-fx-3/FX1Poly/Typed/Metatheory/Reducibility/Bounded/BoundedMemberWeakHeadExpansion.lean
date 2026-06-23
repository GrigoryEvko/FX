import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedPiIntroArm
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.AppWeakHeadFunctionStrongNormalization

/-! # FX1Poly/Typed/BoundedMemberWeakHeadExpansion
    — every bound-reducible candidate is closed under member weak-head expansion (the data-eliminator FT keystone)

`ReducibleTypeAtBounded.headExpansionClosed` ships the β-only `HeadExpansionClosed` (the λ FT arm's need).  The
native data-eliminator fundamental-theorem rows need MORE: a bound-reducible type's candidate must absorb a
member redex under ANY `WeakHeadStep` (β, root-ι, or scrutinee-congruence) — so the ι-contractum branch of a
`boolElim` value membership lifts back to the eliminator cell, and the scrutinee-congruence chain lifts back to a
neutral scrutinee.

`ReducibleTypeAtBounded.memberWeakHeadExpansion`: for any bound-reducible `(typeCode, candidate)` and any
`source ↝ʰ reduct` with `source` strongly normalizing and `reduct` a candidate member, `source` is a candidate
member.  This is the bounded analogue of the denote backbone `memberWeakHeadExpansionModuloPi`, but with the Π
arm DISCHARGED (not isolated) — the arm the denote backbone left open, closed here by the new SN spine
`appWeakHeadFunction_isStronglyNormalizing` (it must establish `SN (app source argument)`, which `SN source ∧ SN
argument` alone cannot give).

The induction is on the bounded `ReducibleTypeStepBounded` derivation (NOT the forgotten denote one): the
non-Π/universe arms reuse the per-candidate weak-head expansions (`emptyTaitCandidate_…`, `dataTaitCandidate_…`,
`CarrierCombinator.assemble_…`); `universeCode` reattaches the lower candidate by
`denoteBelowFamilyBounded_backwardWeakHeadStep`; `piType` is the genuinely-hard arm, where membership at the
arrow candidate is established per argument by the codomain IH on the `appCongruence` weak-head step, with the
application's SN supplied by the new spine and the components' SN read off the bounded
`ReducibleTypeAtBounded.isReducibilityCandidate` (the clean, bound-gated CR — the forgotten denote CR is
unavailable because the below-family's neutral inclusion is vacuous at/above the bound).

## Zero-axiom verification

One `ReducibleTypeStepBounded.rec`; the Π arm composes `appWeakHeadFunction_isStronglyNormalizing` +
`WeakHeadStep.appCongruence` + the bounded `isReducibilityCandidate`; the data arms reuse the shipped
per-candidate weak-head expansions; `universeCode` via `denoteBelowFamilyBounded_backwardWeakHeadStep`;
`ofPointwiseIff` transports both ways.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Every bound-reducible candidate is member-weak-head-expansion-closed.**  For a bound-reducible
`(typeCode, candidate)`, a candidate member of the contractum `reduct` (given `source ↝ʰ reduct` and `source`
strongly normalizing) is a candidate member of the redex `source`.  Induction on the bounded reducibility: the
data/empty arms reuse the shipped per-candidate weak-head expansions, `universeCode` reattaches the lower
candidate, and `piType` lands the arrow candidate per argument via the codomain IH on the `appCongruence`
weak-head step — the application's SN coming from the general weak-head SN spine. -/
theorem ReducibleTypeAtBounded.memberWeakHeadExpansion {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeStepBounded env (denoteBelowFamilyBounded env bound) bound typeCode candidate) :
    ∀ {source reduct : RawTerm (scope + 1)}, WeakHeadStep source reduct → IsStronglyNormalizing source →
      candidate reduct → candidate source := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse _notEmpty _notFlat =>
      intro source _reduct _weakHeadStep sourceStronglyNormalizing _member
      exact sourceStronglyNormalizing
  | @piType domainCode codomainCode domainCandidate codomainCandidate domainReducible
      codomainReducible _domainInductiveHypothesis codomainInductiveHypothesis =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      intro argument argumentInDomain
      have reductApplicationMember :
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons reduct (.childCons argument .childNil))) :=
        member argument argumentInDomain
      have applicationWeakHeadStep :
          WeakHeadStep
            (.mkGen .gen_app () (.childCons source (.childCons argument .childNil)))
            (.mkGen .gen_app () (.childCons reduct (.childCons argument .childNil))) :=
        WeakHeadStep.appCongruence weakHeadStep
      have argumentStronglyNormalizing : IsStronglyNormalizing argument :=
        (ReducibleTypeAtBounded.isReducibilityCandidate
          (domainReducible : ReducibleTypeAtBounded env bound domainCode domainCandidate)).stronglyNormalizing
          argumentInDomain
      have reductApplicationStronglyNormalizing :
          IsStronglyNormalizing
            (.mkGen .gen_app () (.childCons reduct (.childCons argument .childNil))) :=
        (ReducibleTypeAtBounded.isReducibilityCandidate
          ((codomainReducible argument argumentInDomain) :
            ReducibleTypeAtBounded env bound (RawTerm.subst0 codomainCode argument)
              (codomainCandidate argument))).stronglyNormalizing reductApplicationMember
      have sourceApplicationStronglyNormalizing :
          IsStronglyNormalizing
            (.mkGen .gen_app () (.childCons source (.childCons argument .childNil))) :=
        appWeakHeadFunction_isStronglyNormalizing sourceStronglyNormalizing weakHeadStep
          argumentStronglyNormalizing reductApplicationStronglyNormalizing
      exact codomainInductiveHypothesis argument argumentInDomain applicationWeakHeadStep
        sourceApplicationStronglyNormalizing reductApplicationMember
  | universeCode levelExpr _flag _belowBound =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact ⟨sourceStronglyNormalizing,
        match member.2 with
        | ⟨lowerCandidate, lowerMember⟩ =>
            ⟨lowerCandidate,
              denoteBelowFamilyBounded_backwardWeakHeadStep env bound
                (LevelExpr.denote levelExpr env) lowerMember weakHeadStep⟩⟩
  | dataEmpty =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact emptyTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing member
  | dataFlat _flatPinned _notCarrierAware =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing member
  | dataTermIndexed =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing member
  | dataFlatCarrierAware _firstReducible _secondReducible _firstInductiveHypothesis
      _secondInductiveHypothesis =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact CarrierCombinator.assemble_memberWeakHeadExpansion _ _ _ weakHeadStep
        sourceStronglyNormalizing member
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact (pointwiseIff source).mp
        (innerInductiveHypothesis weakHeadStep sourceStronglyNormalizing
          ((pointwiseIff reduct).mpr member))

end FX1Poly.Typed
