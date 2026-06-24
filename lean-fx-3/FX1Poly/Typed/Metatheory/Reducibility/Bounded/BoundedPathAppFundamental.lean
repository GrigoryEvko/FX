import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedBridgeShape
import FX1Poly.Core.Eliminators.Core.PathApplicationGeneralCandidateMember
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Canonicity.BridgeCanonicalFormsCandidate
import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Typed.Cell.UnionCellSubstitution

/-! # FX1Poly/Typed/BoundedPathAppFundamental
    — the bounded DEPENDENT `pathApp` (endpoint-β) member arm (DEP-APP bridge, table-independent engine half)

The bridge-eliminator twin of `idJMemberAtBounded`: `pathApp path argument` (the endpoint application of a path
to an interval point) is a bound-reducible member of the carrier type, given

  * the carrier type is bound-reducible (candidate `resultCandidate`),
  * the interval argument is strongly normalizing,
  * the path is a head-expansion-closed `dataTaitCandidate isPathLamValue` member, AND
  * the **reach-conditioned contractum member** (`contractumMemberIfReachesPathLam`): the endpoint-β contractum
    `body[argument]` is a bound-reducible carrier member WHEN the path reaches `pathLam body`.

The single departure from `idJMemberAtBounded` is the contractum conditioning.  `idJ` contracts on `refl`
DIRECTLY to a passive base case, so its conditioned member is the base case as-is.  `pathApp` is a genuine
β-elimination — `pathApp (pathLam body) arg ↝ body[arg]` is a SUBSTITUTION — so the conditioned member is the
substituted contractum, and the Core member `pathAppDependentReducibleMember` additionally needs CR1 of the
result candidate (`resultCandidateMembersStronglyNormalizing`) to discharge the endpoint-β side-condition of
the per-focus cell SN.  Both are supplied here from the carrier candidate's
`ReducibleTypeAtBounded.isReducibilityCandidate` (CR1 + CR3) and `memberWeakHeadExpansion` (head expansion),
with the conditioned contractum transported into the candidate by `ReducibleTypeAtBounded.deterministic`
exactly as the `idJ` base case is.

This is the table-independent member half; the elim-FT ROW (`fundamentalPathAppElimRowAtBoundedSucc`, the
last missing elim row) sources the path member and the contractum residue from the bridge type's reducibility
and feeds them here — pending the carrier-aware bridge candidate (FTGEN-INTERVAL / FTGEN-GEL), the residue's
genuine source.

## Zero-axiom verification

A pure wiring of the Core `pathAppDependentReducibleMember` against the carrier candidate's CR1/CR3, head
expansion, and `deterministic` transport — no induction, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

open StepStar

/-- **The bounded `pathApp` (endpoint-β) member arm.**  Given the carrier type is bound-reducible (candidate
`resultCandidate`), the interval argument is strongly normalizing, the path is a head-expansion-closed
`dataTaitCandidate isPathLamValue` member, and the endpoint-β contractum is a bound-reducible carrier member
WHEN the path reaches `pathLam body`, the `pathApp` cell is a bound-reducible member of the carrier type.
Instantiates the Core `pathAppDependentReducibleMember` at `resultCandidate`: CR1 / CR3 are the candidate's
`isReducibilityCandidate` projections, head expansion is `memberWeakHeadExpansion`, and the conditioned
contractum is transported into `resultCandidate` by `ReducibleTypeAtBounded.deterministic` (the genuine
β-elimination's substitution contractum — no passive branch). -/
theorem pathAppMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {path argument carrierType : RawTerm (closingScope + 1)}
    {resultCandidate : RawTerm (closingScope + 1) → Prop}
    (carrierReducible : ReducibleTypeAtBounded env bound carrierType resultCandidate)
    (argumentStronglyNormalizing : IsStronglyNormalizing argument)
    (pathMember : dataTaitCandidate isPathLamValue path)
    (contractumMemberIfReachesPathLam : ∀ body : RawTerm (closingScope + 1 + 1),
        StepStar path (pathLamValueCell body) →
        IsReducibleMemberAtBounded env bound carrierType (RawTerm.subst0 body argument)) :
    IsReducibleMemberAtBounded env bound carrierType (pathAppCell path argument) := by
  refine ⟨resultCandidate, carrierReducible, ?_⟩
  refine pathAppDependentReducibleMember resultCandidate
    (fun member =>
      (ReducibleTypeAtBounded.isReducibilityCandidate carrierReducible).stronglyNormalizing member)
    (fun weakHeadStep contractumMember redexStronglyNormalizing =>
      ReducibleTypeAtBounded.memberWeakHeadExpansion carrierReducible weakHeadStep
        redexStronglyNormalizing contractumMember)
    (fun neutralStronglyNormalizing neutral =>
      (ReducibleTypeAtBounded.isReducibilityCandidate carrierReducible).memberOfStronglyNormalizingNeutral
        neutralStronglyNormalizing neutral)
    argumentStronglyNormalizing
    pathMember
    (fun body reaches => ?_)
  obtain ⟨candidateContractum, candidateContractumReducible, contractumInCandidate⟩ :=
    contractumMemberIfReachesPathLam body reaches
  exact (ReducibleTypeAtBounded.deterministic candidateContractumReducible carrierReducible
    (RawTerm.subst0 body argument)).mp contractumInCandidate

/-- **The bounded `pathApp` (endpoint-β) elim engine.**  The `FundamentalConclusionAtBoundedSucc` twin of
`fundamentalPiElimAtBoundedSucc` (the `app` engine): from the path's fundamental conclusion at its bridge type
`bridgeTypeCell carrierCode left right` and the interval argument's at `intervalTypeCell`, the endpoint
application `pathApp path argument` is a +1-closing fundamental member of the (constant) carrier `carrierCode`.

Under every closing substitution, the path's bridge-typed membership is inverted by
`ReducibleTypeAtBounded.bridgeTypeInversion` (the bounded bridge-shape inversion) into the carrier candidate's
reducibility plus the `bridgeReducibleCandidate IsStronglyNormalizing` shape; the carrier candidate IS the
output type's candidate (the bridge carrier is the pathApp output type, `pathAppElimRule.outputType`).  The
path member then supplies `pathAppMemberAtBounded`'s `pathMember` (its first conjunct,
`bridgeReducibleCandidate.pathMember`) and the endpoint-β contractum residue
(`bridgeReducibleCandidate.contractumMemberAt` at the SN interval point) — exactly the residue the carrier-aware
bridge candidate was built to supply.  The argument SN is the candidate CR1 of its bounded membership. -/
theorem fundamentalPathAppElimAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (context : TypingContext profile scope)
    {path argument carrierCode leftEndpoint rightEndpoint : RawTerm scope}
    (pathConclusion : FundamentalConclusionAtBoundedSucc env bound context path
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint))
    (argumentConclusion :
        FundamentalConclusionAtBoundedSucc env bound context argument intervalTypeCell) :
    FundamentalConclusionAtBoundedSucc env bound context (pathAppCell path argument) carrierCode := by
  intro _targetScope substitution envReducible
  have pathMemberRaw := pathConclusion substitution envReducible
  rw [subst_bridgeTypeCell] at pathMemberRaw
  obtain ⟨_bridgeCandidate, bridgeReducible, pathInBridge⟩ := pathMemberRaw
  obtain ⟨carrierCandidate, carrierReducible, bridgePointwise⟩ :=
    ReducibleTypeAtBounded.bridgeTypeInversion bridgeReducible
  have pathBridgeMember : bridgeReducibleCandidate IsStronglyNormalizing carrierCandidate
      (RawTerm.subst substitution path) := (bridgePointwise _).mp pathInBridge
  obtain ⟨_argumentCandidate, argumentReducible, argumentInArgumentCandidate⟩ :=
    argumentConclusion substitution envReducible
  have argumentStronglyNormalizing : IsStronglyNormalizing (RawTerm.subst substitution argument) :=
    (ReducibleTypeAtBounded.isReducibilityCandidate argumentReducible).stronglyNormalizing
      argumentInArgumentCandidate
  rw [subst_pathAppCell]
  exact pathAppMemberAtBounded env bound carrierReducible argumentStronglyNormalizing
    pathBridgeMember.pathMember
    (fun body reaches =>
      ⟨carrierCandidate, carrierReducible,
        pathBridgeMember.contractumMemberAt argumentStronglyNormalizing reaches⟩)

end FX1Poly.Typed
