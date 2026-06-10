import FX1Poly.Typed.NormalUniverseClassificationUnique
import FX1Poly.Typed.GrownWfOpenStronglyNormalizing
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! # Conv-lifted universe-classification uniqueness (E2.8)

The Conv-lift of the normal-subject negotiation master: two CONVERTIBLE subjects, each grown-
classified at a universe code, agree on (level, flag) — under grown context well-formedness
(the honest precondition: open SN needs it).

Route: `stronglyNormalizingOfWfContextDescPi` normalizes both subjects (`RawTerm.normalize` +
its reaches/isNormal equations); `subjectReductionStar` re-types each normal form at its pin;
the Conv chain between the normal forms collapses to a SINGLE term (both join ends are normal,
so the apex is each of them by `StepStar.eq_of_noStep`); `normalUniverseClassificationUnique`
negotiates at that shared normal form.

Consumer: the flag-coherent pair extraction (E3) — given the plateau's Conv-pinned classifier
and the condition pair's classification, this lemma forces the (level, flag) agreement that
lets the caller's `invertLam` components select the condition pair's flag. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Conv-lifted universe-classification uniqueness**: convertible subjects classified at
universe codes carry EQUAL (level, flag) — wf-conditioned (open SN), table-generic. -/
theorem HasTypeDescPi.convUniverseClassificationUnique {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {firstSubject secondSubject : RawTerm scope}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (contextWellFormed : WfContextDescPi context)
    (subjectsConvertible : Conv firstSubject secondSubject)
    (firstClassified : HasTypeDescPi profile context firstSubject
      (universeCodeCell firstLevel firstFlag))
    (secondClassified : HasTypeDescPi profile context secondSubject
      (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag := by
  have firstNormalizes := HasTypeDescPi.stronglyNormalizingOfWfContextDescPi
    contextWellFormed firstClassified
  have secondNormalizes := HasTypeDescPi.stronglyNormalizingOfWfContextDescPi
    contextWellFormed secondClassified
  have firstChain : StepStar firstSubject (RawTerm.normalize firstSubject firstNormalizes) :=
    RawTerm.normalize_reducesTo firstSubject firstNormalizes
  have secondChain : StepStar secondSubject (RawTerm.normalize secondSubject secondNormalizes) :=
    RawTerm.normalize_reducesTo secondSubject secondNormalizes
  have firstNormal : RawTerm.isStepNormalForm (RawTerm.normalize firstSubject firstNormalizes) :=
    RawTerm.normalize_isStepNormalForm firstSubject firstNormalizes
  have secondNormal :
      RawTerm.isStepNormalForm (RawTerm.normalize secondSubject secondNormalizes) :=
    RawTerm.normalize_isStepNormalForm secondSubject secondNormalizes
  have firstNormalFormTyped := HasTypeDescPi.subjectReductionStar
    contextWellFormed firstClassified firstChain
  have secondNormalFormTyped := HasTypeDescPi.subjectReductionStar
    contextWellFormed secondClassified secondChain
  have normalFormsConvertible :
      Conv (RawTerm.normalize firstSubject firstNormalizes)
        (RawTerm.normalize secondSubject secondNormalizes) :=
    Conv.trans
      (Conv.sym ⟨RawTerm.normalize firstSubject firstNormalizes, firstChain,
        StepStar.refl _⟩)
      (Conv.trans subjectsConvertible
        ⟨RawTerm.normalize secondSubject secondNormalizes, secondChain, StepStar.refl _⟩)
  obtain ⟨apex, firstNormalFormToApex, secondNormalFormToApex⟩ := normalFormsConvertible
  have apexEqualsFirst : apex = RawTerm.normalize firstSubject firstNormalizes :=
    StepStar.eq_of_noStep
      (fun stepReduct stepFromFirst =>
        RawTerm.isStepNormalForm_blocks_step firstNormal stepReduct stepFromFirst)
      firstNormalFormToApex
  have apexEqualsSecond : apex = RawTerm.normalize secondSubject secondNormalizes :=
    StepStar.eq_of_noStep
      (fun stepReduct stepFromSecond =>
        RawTerm.isStepNormalForm_blocks_step secondNormal stepReduct stepFromSecond)
      secondNormalFormToApex
  have normalFormsEqual : RawTerm.normalize secondSubject secondNormalizes
      = RawTerm.normalize firstSubject firstNormalizes :=
    apexEqualsSecond.symm.trans apexEqualsFirst
  rw [normalFormsEqual] at secondNormalFormTyped
  exact HasTypeDescPi.normalUniverseClassificationUnique firstNormal
    firstNormalFormTyped secondNormalFormTyped

end FX1Poly.Typed
