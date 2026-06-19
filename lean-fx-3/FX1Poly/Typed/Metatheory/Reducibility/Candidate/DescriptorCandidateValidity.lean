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

/-- **The generator-keyed premise-free candidate dispatch.**  Compose the two halves of the FTGEN-1/FTGEN-2
pipeline — `candidateDescOf` (generator -> descriptor shape) then `descriptorClosedCandidate` (premise-free
shape -> validated candidate) — into the single lookup the generic formation FT arm actually keys on: given a
type-former cell's root generator, the premise-free reducibility candidate it inhabits (when one exists).  It
is `some` exactly on the premise-free formers (the data families bool/nat/list/option/either/sum/unit/empty/
interval, dependent-sum sigma/product, identity, the relational gel/bridge frontier, the strict-prop
frontier) and `none` on the premise-needing formers (Π/arrow -> dependentProduct, equiv -> derivedUnfold,
universe), whose validity the conditional/dependent FT arms supply. -/
def closedCandidateOfGenerator {scope : Nat} (generator : Generator) :
    Option (RawTerm scope → Prop) :=
  (candidateDescOf generator).bind (descriptorClosedCandidate (scope := scope))

/-- **★ The generator-keyed candidate dispatch is validity-sound.**  Whenever the generator dispatch yields a
candidate, that candidate is a Girard reducibility candidate — routed through `descriptorClosedCandidate_valid`
on the underlying shape.  This is the consumable the generic FT formation arm uses directly: it has a cell, it
reads off the candidate from the cell's generator, and validity is guaranteed with no per-former proof. -/
theorem closedCandidateOfGenerator_valid {scope : Nat}
    (generator : Generator) (candidate : RawTerm scope → Prop)
    (denotes : closedCandidateOfGenerator generator = some candidate) :
    CandidateValidity candidate := by
  dsimp only [closedCandidateOfGenerator] at denotes
  cases hDesc : candidateDescOf generator with
  | none => rw [hDesc] at denotes; nomatch denotes
  | some desc =>
      rw [hDesc] at denotes
      exact descriptorClosedCandidate_valid desc candidate denotes

/-! ### Coverage + boundary of the generator dispatch (by `rfl`) -/

theorem closedCandidateOfGenerator_natCode {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_natCode
      = some (inductiveSaturatedCandidate natCandidateSpecs) := rfl
theorem closedCandidateOfGenerator_boolCode {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_boolCode
      = some (inductiveSaturatedCandidate boolCandidateSpecs) := rfl
theorem closedCandidateOfGenerator_eitherCode {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_eitherCode
      = some (inductiveSaturatedCandidate coproductCandidateSpecs) := rfl
theorem closedCandidateOfGenerator_sigmaTyCode {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_sigmaTyCode
      = some (dependentSumCandidate scope) := rfl
theorem closedCandidateOfGenerator_idCode {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_idCode
      = some (identitySaturatedCandidate scope) := rfl
theorem closedCandidateOfGenerator_gelCode {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_gelCode
      = some (relationalSaturatedCandidate scope) := rfl
theorem closedCandidateOfGenerator_sprop {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_sprop
      = some (strictPropIrrelevantCandidate scope) := rfl
/-- Π / arrow are premise-needing — the generator dispatch correctly yields no premise-free candidate (their
validity is the dependent-arrow FT arm). -/
theorem closedCandidateOfGenerator_piTyCode_none {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_piTyCode = none := rfl
/-- `equiv` unfolds to Σ (`derivedUnfold`) — premise-needing, so no premise-free candidate here. -/
theorem closedCandidateOfGenerator_equivCode_none {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_equivCode = none := rfl
/-- A non-former (here a constructor) gets no candidate — its reducibility is the intro/elim obligation. -/
theorem closedCandidateOfGenerator_lam_none {scope : Nat} :
    closedCandidateOfGenerator (scope := scope) .gen_lam = none := rfl

end FX1Poly.Typed
