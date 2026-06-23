import FX1Poly.Core.Metatheory.Canonicity.BridgeCanonicalFormsCandidate
import FX1Poly.Core.Eliminators.Core.DataTaitFocusTrichotomy
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.PathApplicationStrongNormalizationForward
import FX1Poly.Core.Substrate.Neutral.NeutralTerm

/-! # FX1Poly/Core/PathApplicationGeneralCandidateMember
    — dependent `pathApp` (endpoint-β) over a `dataTaitCandidate isPathLamValue` path lands in the carrier candidate

The bridge-eliminator companion to `idJDependentReducibleMember`: `pathApp path argument` (the endpoint
application of a path to an interval point) lands its cell in an ARBITRARY result candidate (the carrier of
the bridge type at the endpoint), with the path scrutinee arriving as a member of the head-expansion-closed
`dataTaitCandidate isPathLamValue`.

**Why this member is BESPOKE, not the shared `dependentDataEliminatorMemberFromValueDispatch` skeleton.**
Every structural data eliminator (`boolElim`, `natElim`, `optionMatch`, `idJ`, …) contracts on its constructor
to a PASSIVE branch (`idJ … (refl w) ↝ baseCase`), so the eliminator cell is strongly normalizing the instant
the scrutinee is — the skeleton's `spineStronglyNormalizing` is UNCONDITIONAL.  `pathApp` is different: it is a
genuine β-elimination, `pathApp (pathLam body) arg ↝ body[arg]`, a substitution-redex carrying the Ω blowup
obstruction.  SN of the path and the argument alone does NOT give SN of the cell; the load-bearing forward-SN
fact `isStronglyNormalizing_pathApplicationCell_ofEndpointBetaContractionsStronglyNormalizing` carries an
ESSENTIAL endpoint-β side-condition (every contractum `body[arg]` reachable from the path is SN).  So the
skeleton does not apply, and this member inlines the same well-founded `Acc` dispatch with one change: the cell
SN is established PER FOCUS from brick-2a, its side-condition discharged UNIFORMLY from the member's own residue
— the conditioned contractum membership `contractumMemberIfReachesPathLam` — plus CR1 (result-candidate members
are SN), threaded along the descent invariant `StepStar path focus`.

The dispatch is otherwise identical to the skeleton: each focus is a value (`pathLam body` — fire endpoint-β,
head-expand with the residue contractum), a weak-head reduct (recurse on the smaller reduct, head-expand the
path congruence), or a neutral (`IsNeutral.pathApp` ⟹ CR3).  The per-focus side-condition holds for ANY focus
reachable from the path, regardless of its trichotomy class, so the cell SN is computed once, before the split.

## Zero-axiom verification

A well-founded `Acc StepSuccessor` induction on the path threading `StepStar path focus`, dispatching on
`dataTaitFocusTrichotomyOfValueHead`, with the per-focus cell SN from brick-2a (side-condition from the residue
+ CR1 + `StepStar.trans_compose`) and the value case firing `WeakHeadStep.pathBeta` (`fires := rfl`, the
table-native endpoint-β).  No `induction` on data, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated by the `FX1Poly.Core` namespace sweep in
`FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **★ Dependent `pathApp` reducibility: the endpoint application lands in the carrier candidate.**  The
endpoint-β (β-elimination) companion to `idJDependentReducibleMember`.  The path scrutinee arrives as a member
of the head-expansion-closed `dataTaitCandidate isPathLamValue`; the CONTRACTUM `body[argument]` is a result
member WHEN the path reaches `pathLam body` (the conditioning the bounded row discharges from the carrier's
reducibility — the analogue of `idJ`'s `baseCaseMemberIfReachesRefl`, but for a genuine substitution-redex).

Unlike `idJ`, `pathApp` is a β-redex, so its cell SN is CONDITIONAL: it needs every reachable contractum to be
SN.  This is supplied uniformly from the residue (`contractumMemberIfReachesPathLam`) plus CR1
(`resultCandidateMembersStronglyNormalizing`), threaded along the descent invariant `StepStar path focus` — the
single departure from the shared skeleton.  The value handler fires `WeakHeadStep.pathBeta` and transports the
conditioned contractum; the neutral handler routes through `IsNeutral.pathApp` and CR3. -/
theorem pathAppDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (resultCandidateMembersStronglyNormalizing :
      ∀ {member : RawTerm scope}, resultCandidate member → IsStronglyNormalizing member)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {path argument : RawTerm scope}
    (argumentStronglyNormalizing : IsStronglyNormalizing argument)
    (pathMember : dataTaitCandidate isPathLamValue path)
    (contractumMemberIfReachesPathLam : ∀ body : RawTerm (scope + 1),
        StepStar path (pathLamValueCell body) → resultCandidate (RawTerm.subst0 body argument)) :
    resultCandidate
      (.mkGen .gen_pathApp () (.childCons path (.childCons argument .childNil))) := by
  suffices general : ∀ {focus : RawTerm scope}, Acc StepSuccessor focus →
      dataTaitCandidate isPathLamValue focus → StepStar path focus →
      resultCandidate
        (.mkGen .gen_pathApp () (.childCons focus (.childCons argument .childNil))) from
    general pathMember.stronglyNormalizing pathMember (StepStar.refl path)
  intro focus accessible
  induction accessible with
  | intro currentFocus _predecessorsAccessible inductiveHypothesis =>
      intro member reaches
      -- The endpoint-β side-condition for THIS focus, discharged uniformly from the residue + CR1: any
      -- `pathLam body` the focus reaches is reached by the path (compose `reaches`), so the residue gives the
      -- contractum's result-candidate membership and CR1 turns it into SN.  Independent of the focus's class.
      have endpointBetaContractionsStronglyNormalizing :
          ∀ body : RawTerm (scope + 1),
            StepStar currentFocus (.mkGen .gen_pathLam () (.childCons body .childNil)) →
            IsStronglyNormalizing (RawTerm.subst0 body argument) := by
        intro body focusReachesPathLam
        exact resultCandidateMembersStronglyNormalizing
          (contractumMemberIfReachesPathLam body
            (StepStar.trans_compose reaches focusReachesPathLam))
      have cellStronglyNormalizing :
          IsStronglyNormalizing
            (.mkGen .gen_pathApp ()
              (.childCons currentFocus (.childCons argument .childNil))) :=
        isStronglyNormalizing_pathApplicationCell_ofEndpointBetaContractionsStronglyNormalizing
          member.stronglyNormalizing argumentStronglyNormalizing
          endpointBetaContractionsStronglyNormalizing
      rcases dataTaitFocusTrichotomyOfValueHead
          (valueHead := isPathLamValueHead) (candidateValue := isPathLamValue)
          (conclusionValue := isPathLamConstructorHead)
          (fun valueIsPathLam => isPathLamValueHead_ofIsPathLamValue valueIsPathLam)
          (fun rootIsPathLam => isPathLamConstructorHead_ofValueHead rootIsPathLam)
          member with
        focusIsConstructorHead | ⟨focusReduct, focusWeakHead⟩ | focusNeutral
      · -- Value: the focus is `pathLam body`.  Fire endpoint-β; head-expand with the residue contractum.
        obtain ⟨body, focusIsPathLam⟩ := focusIsConstructorHead
        subst focusIsPathLam
        exact headExpand (WeakHeadStep.pathBeta (fires := rfl))
          (contractumMemberIfReachesPathLam body reaches) cellStronglyNormalizing
      · -- Weak-head reduct: recurse on the smaller reduct, then head-expand the path congruence.
        have reductMember : dataTaitCandidate isPathLamValue focusReduct :=
          member.closedUnderStep focusWeakHead.toStep
        have reductReaches : StepStar path focusReduct :=
          StepStar.trans_compose reaches (StepStar.single focusWeakHead.toStep)
        have cellReductMember :
            resultCandidate
              (.mkGen .gen_pathApp ()
                (.childCons focusReduct (.childCons argument .childNil))) :=
          inductiveHypothesis focusReduct focusWeakHead.toStep reductMember reductReaches
        exact headExpand (WeakHeadStep.pathAppCongruence focusWeakHead) cellReductMember
          cellStronglyNormalizing
      · -- Neutral: the cell is neutral (principal path stuck); CR3.
        exact memberOfStronglyNormalizingNeutral cellStronglyNormalizing
          (IsNeutral.pathApp focusNeutral)

end FX1Poly.Core
