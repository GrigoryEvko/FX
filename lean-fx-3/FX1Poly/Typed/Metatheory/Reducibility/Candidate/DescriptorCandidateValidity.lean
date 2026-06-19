import FX1Poly.Typed.Metatheory.Reducibility.Candidate.CandidateShapeValidity

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/DescriptorCandidateValidity
    — the generic candidate-validity dispatch (FTGEN-4 core): descriptor shape ⟹ a VALIDATED candidate

The generic formation FT arm needs, from a former's descriptor shape, a reducibility candidate that is a
Girard CR.  For the PREMISE-FREE shapes (all the data-like families) that candidate is the unconditional weak
Tait set, so the formation-arm validity holds with NO premises.  This file packages exactly that: a partial
denotation `descriptorClosedCandidate` from `ReducibilityCandidateDesc` to a candidate, defined on the
premise-free shapes, and ONE generic theorem `descriptorClosedCandidate_valid` proving every candidate it
produces is `CandidateValidity`.  This is the value the FT formation arm (and TYTAB-4) consume: "former X is
FT-covered" reduces to "candidateDescOf X is a premise-free shape (or its premises are supplied)".

## Coverage

`descriptorClosedCandidate` is `some` on: `neutralSaturated`, `inductiveSaturated` (incl. the empty list =
the empty type), `dependentSum`, `identitySaturated`, `relationalSaturated` (gelCode in-arc frontier),
`strictPropIrrelevant` (sprop in-arc frontier).  It is `none` on the PREMISE-NEEDING shapes
(`dependentProduct` — Π needs domain+codomain candidates; `derivedUnfold` — needs the unfolding's candidate;
`universeCandidate` — needs the universe interface) and on the reserved deep frontier
(`coinductiveSaturated` / `quotientByRelation` / `propTruncated` / `modalCandidate`).  The premise-needing
shapes' validity is the conditional `isDependentArrowReducible_isReducibilityCandidate` (Π) / the universe
candidate (Core) / `derivedUnfoldCandidate_valid` (FTGEN-1) — supplied by the dependent FT arms, not here.

## Zero-axiom verification

A 13-arm `match` (no wildcard — well under the propext-leak threshold) + a `cases`-on-shape proof routing
each `some` arm to its FTGEN-1/FTGEN-2 validity and discharging each `none` arm by `nomatch` (the impossible
`none = some` equation).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- **The premise-free candidate denotation.**  Maps each premise-free `ReducibilityCandidateDesc` shape to
its reducibility candidate (from FTGEN-1/FTGEN-2); `none` on the premise-needing and reserved shapes. -/
def descriptorClosedCandidate {scope : Nat} :
    ReducibilityCandidateDesc → Option (RawTerm scope → Prop)
  | .neutralSaturated => some (neutralSaturatedCandidate scope)
  | .dependentProduct => none
  | .dependentSum => some (dependentSumCandidate scope)
  | .inductiveSaturated constructors => some (inductiveSaturatedCandidate constructors)
  | .coinductiveSaturated _ => none
  | .identitySaturated _ => some (identitySaturatedCandidate scope)
  | .universeCandidate => none
  | .derivedUnfold _ => none
  | .relationalSaturated => some (relationalSaturatedCandidate scope)
  | .quotientByRelation => none
  | .propTruncated _ => none
  | .modalCandidate _ => none
  | .strictPropIrrelevant => some (strictPropIrrelevantCandidate scope)

/-- **★ The generic candidate-validity dispatch.**  Every candidate the premise-free denotation produces is a
Girard reducibility candidate — discharged uniformly by routing each shape to its FTGEN-1/FTGEN-2 validity.
This is the consumable core of the FT formation arm for the premise-free former families: data (any
constructor set), the empty type, dependent-sum (weak), identity, the relational/gel frontier, and the
strict-prop frontier all get formation-candidate validity with NO premises. -/
theorem descriptorClosedCandidate_valid {scope : Nat}
    (desc : ReducibilityCandidateDesc) (candidate : RawTerm scope → Prop)
    (denotes : descriptorClosedCandidate desc = some candidate) :
    CandidateValidity candidate := by
  cases desc with
  | neutralSaturated =>
      injection denotes with denotesEq; exact denotesEq ▸ neutralSaturatedCandidate_valid
  | dependentProduct => nomatch denotes
  | dependentSum =>
      injection denotes with denotesEq; exact denotesEq ▸ dependentSumCandidate_valid
  | inductiveSaturated constructors =>
      injection denotes with denotesEq; exact denotesEq ▸ inductiveSaturatedCandidate_valid constructors
  | coinductiveSaturated _ => nomatch denotes
  | identitySaturated _ =>
      injection denotes with denotesEq; exact denotesEq ▸ identitySaturatedCandidate_valid
  | universeCandidate => nomatch denotes
  | derivedUnfold _ => nomatch denotes
  | relationalSaturated =>
      injection denotes with denotesEq; exact denotesEq ▸ relationalSaturatedCandidate_valid
  | quotientByRelation => nomatch denotes
  | propTruncated _ => nomatch denotes
  | modalCandidate _ => nomatch denotes
  | strictPropIrrelevant =>
      injection denotes with denotesEq; exact denotesEq ▸ strictPropIrrelevantCandidate_valid

/-- The premise-free shapes the dispatch covers, by `rfl` on a representative of each — the formation-arm
roster for the no-premise former families. -/
theorem descriptorClosedCandidate_coversNeutral {scope : Nat} :
    descriptorClosedCandidate (scope := scope) .neutralSaturated
      = some (neutralSaturatedCandidate scope) := rfl
theorem descriptorClosedCandidate_coversRelational {scope : Nat} :
    descriptorClosedCandidate (scope := scope) .relationalSaturated
      = some (relationalSaturatedCandidate scope) := rfl
theorem descriptorClosedCandidate_coversStrictProp {scope : Nat} :
    descriptorClosedCandidate (scope := scope) .strictPropIrrelevant
      = some (strictPropIrrelevantCandidate scope) := rfl
/-- The premise-needing `dependentProduct` correctly has no premise-free candidate (its validity is the
conditional Π arm). -/
theorem descriptorClosedCandidate_dependentProduct_none {scope : Nat} :
    descriptorClosedCandidate (scope := scope) .dependentProduct = none := rfl

end FX1Poly.Typed
