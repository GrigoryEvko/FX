import LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellV2
import LeanFX2.Foundation.PolyCell.Core.CheckResult

/-! # Foundation/PolyCell/Core/BuildGeneratingCellExactV2 — generating cell builder

This file ships `buildGeneratingCellExactV2?`: the reconciler that
takes already-certified source and target cells + a ruleId and
constructs a certified dim-(n+1) generating cell, or rejects with
a specific reason.

Direct v2 counterpart to v1's `buildTermStepCellExact?`
(`Core/Check.lean:1796`).

## The reconciliation steps

`buildGeneratingCellExactV2?` performs four Decidable checks before
building the certified cell:

1. **Rule admission**: is `ruleId` the admitted termStepRuleSpecV2's
   ruleId (= 0)?  Currently only termStepRuleSpecV2 is admitted;
   future rules add new `by_cases` branches here.

2. **Source sort**: does the certified source's sort match
   `termStepRuleSpecV2.cellSort` (`.term`)?

3. **Target sort**: does the certified target's sort match?

4. **Endpoint dim equality**: does `source.dim = target.dim`?

If any check fails, returns a specific rejection.  If all pass,
builds the PolyCellV2.generatingCell via the proven transport
pattern.

## The transport pattern — cases + by_cases + subst + generalize

This is the canonical v1-proven recipe (`buildTermStepCellExact?`),
extended for v2's value-level dim handling:

1. `by_cases hRuleId : ruleId = termStepRuleSpecV2.ruleId` +
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
exactly what `PolyCellV2.generatingCell` expects.  No `▸` chains;
the dependent boundary/cert transport is handled entirely by
`generalize + subst`.

## Why the generalize-subst trick on target.dim

After by_cases hDimEq + the pos branch, we have:
* sourceCert : PolyCellV2 ... source.dim scope sourceBoundary source
* targetCert : PolyCellV2 ... target.dim scope targetBoundary target
* hDimEq : source.dim = target.dim

PolyCellV2.generatingCell expects both certs at `source.dim`.
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

namespace LeanFX2.Foundation.PolyCell.Core

/-- Build a certified dim-(n+1) generating cell from a ruleId, raw
source and target, and their already-certified packages.

This is the dispatcher for the `.generatingCell` case of the
recursive certifier (#162).  Currently admits only ruleId 0 (the
termStepRuleSpecV2 rule); future rules add new `by_cases` branches.

Returns a raw-indexed `CertifiedRawCellV2` whose rawCell is exactly
`.generatingCell ruleId source target` (the input shape). -/
def buildGeneratingCellExactV2? {profile : PolyProfile} {scope : Nat}
    (ruleId : Nat) (source target : RawCellV2 scope)
    (certifiedSource : CertifiedRawCellV2 profile scope source)
    (certifiedTarget : CertifiedRawCellV2 profile scope target) :
    Except CellCheckRejection
      (CertifiedRawCellV2 profile scope
        (.generatingCell ruleId source target)) := by
  -- Step 1: Rule admission (currently only termStepRuleSpecV2)
  by_cases hRuleId : ruleId = termStepRuleSpecV2.ruleId
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
          sourceSort = termStepRuleSpecV2.cellSort
        case neg => exact .error .badBoundaryEndpoint
        case pos =>
          subst hSourceSort
          -- Step 3b: Target sort reconciliation
          by_cases hTargetSort :
            targetSort = termStepRuleSpecV2.cellSort
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
              let cell : PolyCellV2 profile _ _ scope _ _ :=
                PolyCellV2.generatingCell
                  termStepRuleSpecV2
                  SupportedRuleSpecV2.termStep
                  hTargetDim.symm
                  sourceCert
                  targetCert
              exact Except.ok {
                sort := termStepRuleSpecV2.cellSort,
                boundary := CellBoundaryV2.endpoints source target,
                certifiedCell := cell
              }

end LeanFX2.Foundation.PolyCell.Core
