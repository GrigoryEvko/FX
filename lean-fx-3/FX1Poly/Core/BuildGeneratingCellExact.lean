import FX1Poly.Core.CertifiedRawCell
import FX1Poly.Core.CheckResult

/-! # Foundation/PolyCell/Core/BuildGeneratingCellExact — generating cell builder

This file ships `buildGeneratingCellExact?`: the reconciler that
takes already-certified source and target cells + a ruleId and
constructs a certified dim-(n+1) generating cell, or rejects with
a specific reason.

## The reconciliation steps

`buildGeneratingCellExact?` performs four Decidable checks before
building the certified cell:

1. **Rule admission**: is `ruleId` the admitted termStepRuleSpec's
   ruleId (= 0)?  Currently only termStepRuleSpec is admitted;
   future rules add new `by_cases` branches here.

2. **Source sort**: does the certified source's sort match
   `termStepRuleSpec.cellSort` (`.term`)?

3. **Target sort**: does the certified target's sort match?

4. **Endpoint dim equality**: does `source.dim = target.dim`?

If any check fails, returns a specific rejection.  If all pass,
builds the PolyCell.generatingCell via the proven transport
pattern.

## The transport pattern — cases + by_cases + subst + generalize

The transport recipe for value-level dim handling:

1. `by_cases hRuleId : ruleId = termStepRuleSpec.ruleId` +
   `subst hRuleId` to replace ruleId throughout
2. `cases certifiedSource` and `cases certifiedTarget` to destructure
   the existential struct fields into free variables
3. `by_cases hSourceSort/hTargetSort` + `subst` for sort
   reconciliation
4. `by_cases hDimEq : source.dim = target.dim` for endpoint dim
   equality
5. `generalize hTargetDim : target.dim = td at hDimEq targetBoundary
   targetCert` + `subst hDimEq` to make `target.dim` definitionally
   `source.dim` in the relevant hypotheses

After these steps, `sourceCert` and `targetCert` have types matching
exactly what `PolyCell.generatingCell` expects.  No `▸` chains;
the dependent boundary/cert transport is handled entirely by
`generalize + subst`.

## Why the generalize-subst trick on target.dim

After by_cases hDimEq + the pos branch, we have:
* sourceCert : PolyCell ... source.dim scope sourceBoundary source
* targetCert : PolyCell ... target.dim scope targetBoundary target
* hDimEq : source.dim = target.dim

PolyCell.generatingCell expects both certs at `source.dim`.
Direct `▸` along hDimEq would require a multi-arg motive over
the dependent boundary+cell pair.  Instead:

```
generalize hTargetDim : target.dim = td at hDimEq targetBoundary targetCert
subst hDimEq  -- replaces td := source.dim everywhere
```

After: targetBoundary and targetCert have `source.dim` in their
types DEFINITIONALLY.  `hTargetDim : target.dim = source.dim` survives
as the `HasEqualDim source target` witness (via `.symm`).

## Zero-axiom verification

All tactics are propext-free:
* `by_cases` with Decidable (Nat.decEq + CellSort.decEq)
* `subst` via Eq.ndrec
* `cases` on a single-ctor struct (no wildcards)
* `generalize` via Eq.ndrec
* `exact` with direct constructor applications

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Build a certified dim-(n+1) generating cell from a ruleId, raw
source and target, and their already-certified packages.

This is the dispatcher for the `.generatingCell` case of the
recursive certifier.  Currently admits only ruleId 0 (the
termStepRuleSpec rule); further rules add new `by_cases` branches.

Returns a raw-indexed `CertifiedRawCell` whose rawCell is exactly
`.generatingCell ruleId source target` (the input shape). -/
def buildGeneratingCellExact? {profile : PolyProfile} {scope : Nat}
    (ruleId : Nat) (source target : RawCell scope)
    (certifiedSource : CertifiedRawCell profile scope source)
    (certifiedTarget : CertifiedRawCell profile scope target) :
    Except CellCheckRejection
      (CertifiedRawCell profile scope
        (.generatingCell ruleId source target)) := by
  -- Step 1: Rule admission (currently only termStepRuleSpec)
  by_cases hRuleId : ruleId = termStepRuleSpec.ruleId
  case neg => exact .error .unknownGenerator
  case pos =>
    subst hRuleId
    -- Step 2: Destructure both certified packages
    cases certifiedSource with
    | mk sourceSort sourceBoundary sourceCert =>
      cases certifiedTarget with
      | mk targetSort targetBoundary targetCert =>
        -- Step 3a: Source sort reconciliation
        by_cases hSourceSort :
          sourceSort = termStepRuleSpec.cellSort
        case neg => exact .error .badBoundaryEndpoint
        case pos =>
          subst hSourceSort
          -- Step 3b: Target sort reconciliation
          by_cases hTargetSort :
            targetSort = termStepRuleSpec.cellSort
          case neg => exact .error .badBoundaryEndpoint
          case pos =>
            subst hTargetSort
            -- Step 4: Endpoint dim equality
            by_cases hDimEq : source.dim = target.dim
            case neg => exact .error .badBoundaryEndpoint
            case pos =>
              -- Step 5: Make target.dim definitionally source.dim
              -- via generalize + subst
              generalize hTargetDim : target.dim = td at hDimEq targetBoundary targetCert
              subst hDimEq
              -- Now everything aligns; build the certified cell
              let cell : PolyCell profile _ _ scope _ _ :=
                PolyCell.generatingCell
                  termStepRuleSpec
                  SupportedRuleSpec.termStep
                  hTargetDim.symm
                  sourceCert
                  targetCert
              exact Except.ok {
                sort := termStepRuleSpec.cellSort,
                boundary := CellBoundary.endpoints source target,
                certifiedCell := cell
              }

end FX1Poly.Core
