import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedPiIntroArm
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.AppWeakHeadFunctionStrongNormalization
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierModelAssembler

/-! # FX1Poly/Typed/BoundedMemberWeakHeadExpansion
    — every bound-reducible candidate is closed under member weak-head expansion (the data-eliminator FT keystone)

This file ships TWO bounded-native closures: `ReducibleTypeAtBounded.memberWeakHeadExpansion` (any `WeakHeadStep`)
and `ReducibleTypeAtBounded.headExpansionClosed` (the β-only `HeadExpansionClosed`, the λ FT arm's need).  Both are
fresh inductions over the real bounded relation — NOT forget-bridge transfers to the pure-denote model, which is
the point: the projection-based Sigma candidate `projectionPairCandidate` (stored at the `pairLike` arm by
`assembleModel`) makes head-expansion DEPEND on the components' member-weak-head-expansion, available ONLY here at
the bounded family at `scope + 1`, where the universe gate makes CR1/MWHE unconditional.  The pure-denote
head-expansion FAILS for that candidate (denote neutral-inclusion is vacuous above the bound), so the bounded-native
proof — placed here, downstream of MWHE — is what discharges the fst/snd reach residues.

The native data-eliminator fundamental-theorem rows need the FULL MWHE: a bound-reducible type's candidate must
absorb a member redex under ANY `WeakHeadStep` (β, root-ι, or scrutinee-congruence) — so the ι-contractum branch of
a `boolElim` value membership lifts back to the eliminator cell, and the scrutinee-congruence chain lifts back to a
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
  | dataBridgeCarrierAware _carrierReducible _carrierInductiveHypothesis =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact bridgeReducibleCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing
        member
  | dataFlatCarrierAware _firstReducible _secondReducible firstInductiveHypothesis
      secondInductiveHypothesis =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact CarrierCombinator.assembleModel_memberWeakHeadExpansion _ _ _
        firstInductiveHypothesis secondInductiveHypothesis
        weakHeadStep sourceStronglyNormalizing member
  | dataUnaryCarrierAware _elementReducible _elementInductiveHypothesis =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact UnaryCarrierCombinator.assembleModel_memberWeakHeadExpansion _ _
        weakHeadStep sourceStronglyNormalizing member
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      intro source reduct weakHeadStep sourceStronglyNormalizing member
      exact (pointwiseIff source).mp
        (innerInductiveHypothesis weakHeadStep sourceStronglyNormalizing
          ((pointwiseIff reduct).mpr member))

/-- **★ Every bound-reducible candidate is head-expansion-closed (BOUNDED-NATIVE).**  A fresh induction over the
real bounded relation `ReducibleTypeAtBounded env bound` (NOT the forget-bridge transfer), structured exactly like
the pure-denote `headExpansionClosed` arms — but where the denote version FAILS, this one WORKS: the
`dataFlatCarrierAware` arm supplies the two component carriers' member-weak-head-expansion FUNCTIONS to
`assembleModel_headExpansionClosed` directly from `ReducibleTypeAtBounded.memberWeakHeadExpansion` on the component
derivations.  This discharges the head-expansion of the projection-based Sigma candidate `projectionPairCandidate`
(stored at the `pairLike` arm by `assembleModel`), which needs the component MWHE — available ONLY at the bounded
family at `scope + 1`, where the universe gate `belowBound` makes CR1/MWHE unconditional (the pure-denote model's
neutral-inclusion is vacuous above the bound, so its candidacy/MWHE were unsuppliable).  The `universeCode` arm
discharges the lower-candidate leg via `denoteBelowFamilyBounded_backwardWeakHeadStep` on `WeakHeadStep.betaSpine`
(bound-free, vacuous above the bound); the `piType` arm absorbs the extra application argument into the spine
(`applySpineApp_append`), no MWHE needed.  Stated at `scope + 1` (the MWHE scope); the live consumer
(`fundamentalPiIntroAtBoundedSucc`) reads it at the +1-closing substitution target.

## Zero-axiom verification

One `ReducibleTypeStepBounded.rec`; the data/empty/bridge arms reuse the shipped per-candidate head-expansions, the
`dataFlatCarrierAware` arm composes `assembleModel_headExpansionClosed` + `ReducibleTypeAtBounded.member\
WeakHeadExpansion`, the `universeCode` arm reassembles via the anonymous constructor (no `funext`), the `piType`
arm via `applySpineApp_append`, `ofPointwiseIff` transports pointwise.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`. -/
theorem ReducibleTypeAtBounded.headExpansionClosed {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeStepBounded env (denoteBelowFamilyBounded env bound) bound typeCode candidate) :
    HeadExpansionClosed candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse _notEmpty _notFlat =>
      exact isStronglyNormalizing_headExpansionClosed
  | @piType _domainCode _codomainCode _domainCandidate codomainCandidate _domainReducible
      _codomainReducible _domainInductiveHypothesis codomainInductiveHypothesis =>
      intro domainAnn body argument spine domainAnnSN argumentSN contractumReducible
      intro extraArgument extraArgumentReducible
      have contractumAtExtendedSpine :
          codomainCandidate extraArgument
            (RawTerm.applySpineApp (RawTerm.subst0 body argument) (spine ++ [extraArgument])) := by
        rw [applySpineApp_append]
        exact contractumReducible extraArgument extraArgumentReducible
      have redexAtExtendedSpine :
          codomainCandidate extraArgument
            (RawTerm.applySpineApp
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
                  (.childCons argument .childNil)))
              (spine ++ [extraArgument])) :=
        (codomainInductiveHypothesis extraArgument extraArgumentReducible)
          domainAnnSN argumentSN contractumAtExtendedSpine
      rw [applySpineApp_append] at redexAtExtendedSpine
      exact redexAtExtendedSpine
  | universeCode levelExpr _flag _belowBound =>
      intro _domainAnn _body _argument _spine domainAnnSN argumentSN contractumMember
      obtain ⟨contractumStronglyNormalizing, lowerCandidate, lowerContractum⟩ := contractumMember
      exact ⟨betaSpineHeadExpansion domainAnnSN argumentSN contractumStronglyNormalizing,
        lowerCandidate,
        denoteBelowFamilyBounded_backwardWeakHeadStep env bound (LevelExpr.denote levelExpr env)
          lowerContractum WeakHeadStep.betaSpine⟩
  | dataEmpty =>
      exact emptyTaitCandidate_headExpansionClosed
  | dataFlat _flatPinned _notCarrierAware _notTermIndexed =>
      exact dataTaitCandidate_headExpansionClosed
  | dataFlatCarrierAware firstReducible secondReducible _firstInductiveHypothesis _secondInductiveHypothesis =>
      exact CarrierCombinator.assembleModel_headExpansionClosed _ _ _
        (ReducibleTypeAtBounded.memberWeakHeadExpansion firstReducible)
        (ReducibleTypeAtBounded.memberWeakHeadExpansion secondReducible)
  | dataUnaryCarrierAware _elementReducible _elementInductiveHypothesis =>
      exact UnaryCarrierCombinator.assembleModel_headExpansionClosed _ _
  | dataTermIndexed =>
      exact dataTaitCandidate_headExpansionClosed
  | dataBridgeCarrierAware _carrierReducible _carrierInductiveHypothesis =>
      exact bridgeReducibleCandidate_headExpansionClosed
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis.respectsPointwiseIff (fun term => pointwiseIff term)

end FX1Poly.Typed
