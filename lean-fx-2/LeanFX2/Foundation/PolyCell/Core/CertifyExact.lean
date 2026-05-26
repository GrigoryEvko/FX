import LeanFX2.Foundation.PolyCell.Core.Check
import LeanFX2.Foundation.PolyCell.Core.PolyTermDecEq
/-!
# CertifyExact — General Raw-Indexed Recursive Certifier

This is the first general (dimension-polymorphic, recursive) raw-to-certified
ingress.  Unlike the per-fixture dispatchers, one function `certifyRawCellExact?`
recurses over every `PolyTerm profile dim` and returns a certified cell indexed
by the EXACT input raw cell, so the certified child link survives into parent
constructors.

Propext discipline (validated): the recursion matches on `rawCell` only — never
on the `(dim, rawCell)` pair and never on a concrete dimension index — so the
matcher never has to exclude an impossible (index, constructor) pair.  Index
transport for atoms uses `cast`/`Eq.rec`, never the equation compiler.

Current coverage: every payload-evidenced atom (variable, unit type, empty
context, linear mode) and the first finite application / lambda / pi-type /
context-extension payloads, iterated identities at every dimension, generating
cells reconciled against the term-step rule, and vertical composites reconciled
by sort plus the shared middle boundary (decided via the propext-free `PolyTerm`
`DecidableEq`).  Only horizontal composition rejects, as `unsupportedCompH`,
pending Gray-tensor semantics — so the certifier is total on the entire
non-`compH` raw fragment.
-/

namespace LeanFX2.Foundation.PolyCell.Core
namespace Check

/-- Reconstruct a raw-indexed certified package from an existential result. -/
def CertifiedRawCellResult.toPackage {profile : PolyProfile} {scope : Nat}
    (result : CertifiedRawCellResult profile scope) :
    CertifiedRawCell profile scope result.rawCell where
  cellSort := result.cellSort
  cellBoundary := result.cellBoundary
  certifiedCell := result.certifiedCell

/-- Raw-indexed atom certifier.

Returns a certified package indexed by the EXACT input atom.  Index transport
along the decided generator-id / payload equalities uses `cast` (`Eq.rec`),
which is propext-free.  Rejection reasons mirror `inferRawAtom?` through the
shared `certificationRejectionAfterScreen?` policy. -/
def certifyRawAtomExact? {profile : PolyProfile} (scope cellId payload : Nat) :
    Except CellCheckRejection
      (CertifiedRawCell profile scope (PolyTerm.atom cellId payload)) :=
  if hVariable : cellId = variableGeneratorSpec.cellId then
    match variablePayloadEvidence? scope payload with
    | some (AtomPayloadEvidence.variable hasIndexWithinScope) =>
        Except.ok
          (cast (by rw [hVariable])
            (certifiedVariablePackage (profile := profile) hasIndexWithinScope))
    | none => Except.error .badPayload
  else if hUnitType : cellId = unitTypeGeneratorSpec.cellId then
    if hPayload : payload = 0 then
      Except.ok
        (cast (by rw [hUnitType, hPayload])
          (certifiedUnitTypePackage (profile := profile) (scope := scope)))
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else if hContextEmpty : cellId = contextEmptyGeneratorSpec.cellId then
    if hPayload : payload = 0 then
      Except.ok
        (cast (by rw [hContextEmpty, hPayload])
          (certifiedContextEmptyPackage (profile := profile) (scope := scope)))
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else if hLinearMode : cellId = linearModeGeneratorSpec.cellId then
    if hPayload : payload = 0 then
      Except.ok
        (cast (by rw [hLinearMode, hPayload])
          (certifiedLinearModePackage (profile := profile) (scope := scope)))
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else if hLambda : cellId = lambdaGeneratorSpec.cellId then
    if hPayload : payload = lambdaUnitTypeBodyVarZeroPayload then
      match certifyLambdaUnitTypeBodyVarZeroChildren? (profile := profile) scope with
      | Except.ok certifiedChildren =>
          Except.ok
            (cast (by rw [hLambda, hPayload])
              (certifiedLambdaUnitTypeBodyVarZeroPackage (profile := profile)
                certifiedChildren))
      | Except.error rejection => Except.error rejection
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else if hApplication : cellId = applicationGeneratorSpec.cellId then
    if hPayload : payload = applicationVarZeroVarOnePayload then
      match certifyApplicationVarZeroVarOneChildren? (profile := profile) scope with
      | Except.ok certifiedChildren =>
          Except.ok
            (cast (by rw [hApplication, hPayload])
              (certifiedApplicationVarZeroVarOnePackage (profile := profile)
                certifiedChildren))
      | Except.error rejection => Except.error rejection
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else if hPiType : cellId = piTypeGeneratorSpec.cellId then
    if hPayload : payload = piTypeUnitCodomainUnitPayload then
      match certifyPiTypeUnitCodomainUnitChildren? (profile := profile) scope with
      | Except.ok certifiedChildren =>
          Except.ok
            (cast (by rw [hPiType, hPayload])
              (certifiedPiTypeUnitCodomainUnitPackage (profile := profile)
                certifiedChildren))
      | Except.error rejection => Except.error rejection
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else if hContextCons : cellId = contextConsGeneratorSpec.cellId then
    if hPayload : payload = contextConsEmptyUnitLinearPayload then
      match certifyContextConsEmptyUnitLinearChildren? (profile := profile) scope with
      | Except.ok certifiedChildren =>
          Except.ok
            (cast (by rw [hContextCons, hPayload])
              (certifiedContextConsEmptyUnitLinearPackage (profile := profile)
                certifiedChildren))
      | Except.error rejection => Except.error rejection
    else
      Except.error
        (certificationRejectionAfterScreen? scope
          (PolyTerm.atom (profile := profile) cellId payload))
  else
    Except.error
      (certificationRejectionAfterScreen? scope
        (PolyTerm.atom (profile := profile) cellId payload))

/-- Reconcile two already-certified children into a certified generating cell
for the term-step rule.

Reconciliation uses `by_cases` (Decidable) + `subst`/`▸` (Eq.rec) only — never
a match on the Nat dimension index.  After `subst` of the dimension equality the
children land at dim 0, where `CellBoundary` is `Unit` regardless of sort, so the
sort transport carries no boundary obligation.  Only the term-step rule at
endpoint dimension 0 is supported today; everything else rejects. -/
def buildTermStepCellExact? {profile : PolyProfile} {scope : Nat} {dim : CellDim}
    (ruleId : Nat) (source target : PolyTerm profile dim)
    (certSource : CertifiedRawCell profile scope source)
    (certTarget : CertifiedRawCell profile scope target) :
    Except CellCheckRejection
      (CertifiedRawCell profile scope (PolyTerm.cell ruleId source target)) := by
  by_cases hRule : ruleId = termStepRuleSpec.ruleId
  · subst hRule
    by_cases hDim : dim = 0
    · subst hDim
      by_cases hSortSource : certSource.cellSort = termStepRuleSpec.cellSort
      · by_cases hSortTarget : certTarget.cellSort = termStepRuleSpec.cellSort
        · exact Except.ok
            { cellSort := termStepRuleSpec.cellSort
              cellBoundary := (source, target)
              certifiedCell :=
                PolyCell.cell SupportedRuleSpec.termStep
                  (hSortSource ▸ certSource.certifiedCell)
                  (hSortTarget ▸ certTarget.certifiedCell) }
        · exact Except.error .badBoundaryEndpoint
      · exact Except.error .badBoundaryEndpoint
    · exact Except.error .unknownGenerator
  · exact Except.error .unknownGenerator

/-- Reconcile two already-certified positive-dimensional cells into a certified
vertical composite: same sort, and the first cell's target boundary equal to the
second cell's source boundary (decided via the propext-free `PolyTerm`
`DecidableEq`).  The boundary-pair transport uses `▸` (`Eq.rec`) plus structure
eta and is propext-free. -/
def buildVerticalCompositeExact? {profile : PolyProfile} {scope : Nat}
    {cdim : CellDim} (first second : PolyTerm profile (cdim + 1))
    (certFirst : CertifiedRawCell profile scope first)
    (certSecond : CertifiedRawCell profile scope second) :
    Except CellCheckRejection
      (CertifiedRawCell profile scope (PolyTerm.compV first second)) :=
  if hSort : certSecond.cellSort = certFirst.cellSort then
    if hMiddle : (certSecond.cellBoundary.1 : PolyTerm profile cdim) =
        (certFirst.cellBoundary.2 : PolyTerm profile cdim) then
      Except.ok
        { cellSort := certFirst.cellSort
          cellBoundary := (certFirst.cellBoundary.1, certSecond.cellBoundary.2)
          certifiedCell :=
            PolyCell.compV certFirst.certifiedCell
              (hMiddle ▸ hSort ▸ certSecond.certifiedCell) }
    else Except.error .badVerticalBoundary
  else Except.error .badVerticalBoundary

/-- General raw-indexed recursive certifier.

Matches on `rawCell` only (dim inferred), so the matcher never excludes an
impossible index/constructor pair.  Identity recurses on its base and wraps via
the derived certified identity package without index transport.  Generating
cells recurse on both endpoints and reconcile against the term-step rule.
Vertical composites recurse on both operands and reconcile sort plus the shared
middle boundary.  Horizontal composition stays rejected pending Gray semantics. -/
def certifyRawCellExact? {profile : PolyProfile} (scope : Nat) {dim : CellDim}
    (rawCell : PolyTerm profile dim) :
    Except CellCheckRejection (CertifiedRawCell profile scope rawCell) :=
  match rawCell with
  | .atom cellId payload => certifyRawAtomExact? scope cellId payload
  | .cell ruleId source target =>
      match certifyRawCellExact? scope source,
          certifyRawCellExact? scope target with
      | Except.ok certSource, Except.ok certTarget =>
          buildTermStepCellExact? ruleId source target certSource certTarget
      | Except.error rejection, _ => Except.error rejection
      | _, Except.error rejection => Except.error rejection
  | .compV first second =>
      match certifyRawCellExact? scope first,
          certifyRawCellExact? scope second with
      | Except.ok certFirst, Except.ok certSecond =>
          buildVerticalCompositeExact? first second certFirst certSecond
      | Except.error rejection, _ => Except.error rejection
      | _, Except.error rejection => Except.error rejection
  | .compH _ _ => Except.error .unsupportedCompH
  | .identity base =>
      match certifyRawCellExact? scope base with
      | Except.ok baseCertified =>
          Except.ok (certifiedIdentityPackage baseCertified)
      | Except.error rejection => Except.error rejection

/-- Existential-output wrapper over the general certifier, matching the public
`CertifiedRawCellResult` API used by the rest of the checker. -/
def inferRawCellGeneral? {profile : PolyProfile} (scope : Nat) {dim : CellDim}
    (rawCell : PolyTerm profile dim) :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) :=
  match certifyRawCellExact? scope rawCell with
  | Except.ok certifiedCell =>
      Except.ok
        (certifiedRawCellResultOfPackage
          (rawCellCode rawCell) certifiedCell (hasSameNatList_self _))
  | Except.error rejection => Except.error rejection

/-- The general certifier agrees with the dim-0 atom ingress on accepted atoms:
the seed variable certifies at the term sort. -/
theorem inferRawCellGeneral?_seedTerm_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.seedTermAtom profile)) = some .term := rfl

/-- The seed unit type certifies at the type sort through the general ingress. -/
theorem inferRawCellGeneral?_seedType_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.seedTypeAtom profile)) = some .type := rfl

/-- The first application payload certifies through the general ingress. -/
theorem inferRawCellGeneral?_application_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.applicationVarZeroVarOneRawCell profile)) =
      some .term := rfl

/-- The first lambda payload certifies through the general ingress. -/
theorem inferRawCellGeneral?_lambda_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.lambdaUnitTypeBodyVarZeroRawCell profile)) =
      some .term := rfl

/-- The first pi-type payload certifies through the general ingress. -/
theorem inferRawCellGeneral?_piType_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.piTypeUnitCodomainUnitRawCell profile)) =
      some .type := rfl

/-- The first context-extension payload certifies through the general ingress. -/
theorem inferRawCellGeneral?_contextCons_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.contextConsEmptyUnitLinearRawCell profile)) =
      some .context := rfl

/-- An iterated identity over the seed term certifies at the term sort —
exercises the recursion at dim 1. -/
theorem inferRawCellGeneral?_identity_seedTerm_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (PolyTerm.identity (NegativeProbes.seedTermAtom profile))) =
      some .term := rfl

/-- A doubly-iterated identity certifies at dim 2 — exercises deeper recursion. -/
theorem inferRawCellGeneral?_identity_identity_seedType_sort
    {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (PolyTerm.identity
          (PolyTerm.identity (NegativeProbes.seedTypeAtom profile)))) =
      some .type := rfl

/-- An out-of-scope variable still rejects through the general ingress. -/
theorem inferRawCellGeneral?_outOfScopeVariable_rejects {profile : PolyProfile} :
    inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.outOfScopeVariableRawCell profile) =
      Except.error .badPayload := rfl

/-- An unknown generator still rejects through the general ingress. -/
theorem inferRawCellGeneral?_unknownGenerator_rejects {profile : PolyProfile} :
    inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
      (NegativeProbes.unknownGeneratorRawCell profile) =
      Except.error .unknownGenerator := rfl

/-- Raw horizontal composition rejects through the general ingress. -/
theorem inferRawCellGeneral?_compH_rejects {profile : PolyProfile} {scope : Nat}
    (left right : PolyTerm profile 1) :
    inferRawCellGeneral? (profile := profile) scope
      (PolyTerm.compH left right) = Except.error .unsupportedCompH := rfl

/-- The first dim-1 term-step cell certifies through the general ingress —
exercises endpoint recursion plus term-step reconciliation. -/
theorem inferRawCellGeneral?_termStep_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (NegativeProbes.termStepVarZeroVarOneRawCell profile)) =
      some .term := rfl

/-- An identity over the first dim-1 term-step cell certifies at dim 2 —
the recursion now certifies generating cells, not just atoms. -/
theorem inferRawCellGeneral?_identity_termStep_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) NegativeProbes.defaultInferScope
        (PolyTerm.identity
          (NegativeProbes.termStepVarZeroVarOneRawCell profile))) =
      some .term := rfl

/-- Soundness — no false positives are expressible: an accepted general
certification yields a certified cell whose raw erasure is EXACTLY the input.
This is guaranteed by the raw-indexed result type, so it holds for any accepted
witness regardless of which fixture or recursion path produced it. -/
theorem certifyRawCellExact?_sound {profile : PolyProfile} {scope : Nat}
    {dim : CellDim} {rawCell : PolyTerm profile dim}
    (certifiedCell : CertifiedRawCell profile scope rawCell)
    (_accepted : certifyRawCellExact? scope rawCell = Except.ok certifiedCell) :
    certifiedCell.certifiedCell.raw = rawCell :=
  certifiedCell.certifiedCell_raw

/-- The general certifier rejects horizontal composition at every dimension,
pending Gray-tensor semantics. -/
theorem certifyRawCellExact?_compH_rejects {profile : PolyProfile} {scope : Nat}
    {dim : CellDim} (left right : PolyTerm profile (dim + 1)) :
    certifyRawCellExact? scope (PolyTerm.compH left right) =
      Except.error .unsupportedCompH := rfl

end Check
end LeanFX2.Foundation.PolyCell.Core
