import FX1Poly.Core.Rewriting.RuleTables.Eta.TableBetaEtaRootNormalize
import FX1Poly.Typed.Equality.Eta.TableBetaEtaRootConfluence

/-! # TableBetaEtaRootConvDecidable — the TABLE-NATIVE union beta-eta
conversion decider on the well-formed-typed fragment

The third and final brick of the TABLE-NATIVE union beta-eta decider:
a computable `Decidable` instance for the canonical union conversion
`ConvTableBetaEtaRoot` (join form over `StepTable ∪ StepEtaRootTable`)
on the well-formed-typed fragment, with ZERO dependence on the bespoke
`Step.betaEta`/`reduceOnceBetaEta`/`normalizeBetaEta`.

The metatheory legs are ALL shipped; this brick is pure assembly:

* SN — `HasTypeDescPi.tableBetaEtaRootStronglyNormalizing` supplies the
  two `Acc (UnionSuccessor StepTable StepEtaRootTable)` certificates
  (via `WfContextDescPi.ofWfContextDesc`) that drive PIECE 2's
  normalizer;
* CR — `HasTypeDescPi.tableBetaEtaRootConfluenceTypedNative` joins any
  two union reducts of a typed subject;
* UNF / rigidity — `unionStarEqOfNormal` collapses a union chain out of
  a union-normal term.

The decider normalizes both sides (PIECE 2) and compares the two normal
forms by the propext-free `instDecidableEqRawTerm`; the iff
(`ConvTableBetaEtaRoot ↔ normal-forms-equal`) is the CR + rigidity
characterization restated for the union (the generic
`ConvOverTable.iff_normalize_eq` cannot be reused: it assumes a FREE
`Confluent`, but union confluence holds only for reducts of a typed
subject).  The Core `StepTableBetaEtaRootUnion` and the Typed
`StepTableBetaEtaRoot` are the same `Or` definitionally, so the
PIECE 2 normal-form witness feeds `unionStarEqOfNormal` directly.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConvDecidable.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- Union stars compose (the head-extension brick the decider's
characterization needs; structural recursion on the second chain). -/
theorem unionStarTrans {scope : Nat}
    {sourceTerm middleTerm targetTerm : RawTerm scope}
    (firstStar : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      sourceTerm middleTerm)
    (secondStar : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      middleTerm targetTerm) :
    UnionStar (StepTable (scope := scope)) StepEtaRootTable sourceTerm
      targetTerm := by
  induction secondStar with
  | refl => exact firstStar
  | tailLeft _ stepToReduct ih => exact .tailLeft ih stepToReduct
  | tailRight _ stepToReduct ih => exact .tailRight ih stepToReduct

/-! ## The union conversion relation -/

/-- **The canonical TABLE-NATIVE union beta-eta conversion** (join
form): the two sides reach a shared common reduct over
`StepTable ∪ StepEtaRootTable` — the exact JOIN shape the native typed
Church-Rosser (`tableBetaEtaRootConfluenceTypedNative`) concludes, lifted
to relate the two ORIGINAL terms.  ZERO bespoke `Step.betaEta`. -/
def ConvTableBetaEtaRoot {scope : Nat} (leftTerm rightTerm : RawTerm scope) :
    Prop :=
  ∃ commonReduct : RawTerm scope,
    UnionStar (StepTable (scope := scope)) StepEtaRootTable leftTerm
        commonReduct
      ∧ UnionStar (StepTable (scope := scope)) StepEtaRootTable rightTerm
          commonReduct

/-! ## Conversion is normal-form equality on the typed fragment -/

/-- **Union conversion = normal-form equality** on the well-formed-typed
fragment.  Forward: CR joins the shared common reduct against each
side's normal form, rigidity collapses the normal-form leg, so each
normal form is a reduct of the common reduct; a second CR on the common
reduct joins the two normal forms, both rigid, hence equal.  Backward:
the shared normal form IS a common reduct. -/
theorem ConvTableBetaEtaRoot.iff_normalForms_eq {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {leftTerm leftClassifier rightTerm rightClassifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm leftClassifier)
    (rightTyped : HasTypeDescPi profile context rightTerm rightClassifier)
    (leftTerminates :
      Acc (UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable)
        leftTerm)
    (rightTerminates :
      Acc (UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable)
        rightTerm) :
    ConvTableBetaEtaRoot leftTerm rightTerm ↔
      RawTerm.normalizeTableBetaEtaRoot leftTerm leftTerminates
        = RawTerm.normalizeTableBetaEtaRoot rightTerm rightTerminates := by
  have wellFormedPi := WfContextDescPi.ofWfContextDesc contextWellFormed
  have leftToNormal :=
    RawTerm.normalizeTableBetaEtaRoot_reachesNormalForm leftTerm
      leftTerminates
  have rightToNormal :=
    RawTerm.normalizeTableBetaEtaRoot_reachesNormalForm rightTerm
      rightTerminates
  have leftNormal :=
    RawTerm.normalizeTableBetaEtaRoot_isNormalForm leftTerm leftTerminates
  have rightNormal :=
    RawTerm.normalizeTableBetaEtaRoot_isNormalForm rightTerm rightTerminates
  constructor
  · intro convertible
    obtain ⟨commonReduct, leftToCommon, rightToCommon⟩ := convertible
    -- CR on `leftTerm`: join `commonReduct` and `leftNF`; rigidity makes
    -- `leftNF` the meet, so `commonReduct →* leftNF`.
    obtain ⟨leftMeet, commonToLeftMeet, leftNormalToLeftMeet⟩ :=
      HasTypeDescPi.tableBetaEtaRootConfluenceTypedNative wellFormedPi
        leftTyped leftToCommon leftToNormal
    obtain rfl := unionStarEqOfNormal leftNormal leftNormalToLeftMeet
    have rightToLeftNormal :=
      unionStarTrans rightToCommon commonToLeftMeet
    -- CR on `rightTerm`: join `leftNF` and `rightNF`; both rigid, equal.
    obtain ⟨finalMeet, leftNormalToFinal, rightNormalToFinal⟩ :=
      HasTypeDescPi.tableBetaEtaRootConfluenceTypedNative wellFormedPi
        rightTyped rightToLeftNormal rightToNormal
    exact (unionStarEqOfNormal leftNormal leftNormalToFinal).trans
      (unionStarEqOfNormal rightNormal rightNormalToFinal).symm
  · intro normalsEq
    exact ⟨RawTerm.normalizeTableBetaEtaRoot leftTerm leftTerminates,
      leftToNormal, normalsEq ▸ rightToNormal⟩

/-! ## The decider -/

/-- ★★★ **Decidable TABLE-NATIVE union beta-eta conversion on the
well-formed-typed fragment.**  Derive both SN certificates from
`tableBetaEtaRootStronglyNormalizing` (through
`WfContextDescPi.ofWfContextDesc`), normalize both sides with PIECE 2,
and decide by `instDecidableEqRawTerm` on the two normal forms; the iff
(`ConvTableBetaEtaRoot ↔ normal-forms-equal`) discharges soundness via
the native typed Church-Rosser + rigidity.  ZERO dependence on the
bespoke `Step.betaEta`/`reduceOnceBetaEta`/`normalizeBetaEta`. -/
def ConvTableBetaEtaRoot.decidableOfWfTyped {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {leftTerm leftClassifier rightTerm rightClassifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm leftClassifier)
    (rightTyped : HasTypeDescPi profile context rightTerm rightClassifier) :
    Decidable (ConvTableBetaEtaRoot leftTerm rightTerm) :=
  let wellFormedPi := WfContextDescPi.ofWfContextDesc contextWellFormed
  let leftTerminates :=
    HasTypeDescPi.tableBetaEtaRootStronglyNormalizing wellFormedPi leftTyped
  let rightTerminates :=
    HasTypeDescPi.tableBetaEtaRootStronglyNormalizing wellFormedPi rightTyped
  decidable_of_iff _
    (ConvTableBetaEtaRoot.iff_normalForms_eq contextWellFormed leftTyped
      rightTyped leftTerminates rightTerminates).symm

end FX1Poly.Typed
