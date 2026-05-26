import LeanFX2.Foundation.PolyCell.Core.Check
/-!
# CertifyExact — General Raw-Indexed Recursive Certifier (coverage)

The general (dimension-polymorphic, recursive) raw-to-certified certifier
`certifyRawCellExact?` and its existential wrapper `inferRawCellGeneral?` are
now defined in `Check.lean` so the legacy public dim-0 / term-step ingress
(`inferRawCell?`, `inferTermStepVarZeroVarOne?`) can delegate to them — a single
certification source of truth.  This file holds the general-certifier coverage
theorems plus the soundness statement.

Unlike the per-fixture dispatchers, one function `certifyRawCellExact?` recurses
over every `PolyTerm profile dim` and returns a certified cell indexed by the
EXACT input raw cell, so the certified child link survives into parent
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
