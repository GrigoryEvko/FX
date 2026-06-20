import FX1Poly.Typed.Metatheory.Canonicity.Core.NatNumeralUnionCanonicity
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate

/-! # FX1Poly/Typed/NatUnionReducesToNumeral
    — the REDUCES-to-numeral form of Nat canonicity over the single union judgment, parameterized on
    the deferred union SN/SR arc, zero-axiom

`HasTypeUnion.closedNormalNatNumeral` (the [[NatNumeralUnionCanonicity]] headline) classifies an
ALREADY-normal union-typed term at `natTypeCell` as a deep numeral (`IsNatNumeral`).  Its own header
records that "the reduces-to-numeral form over the union returns with the deferred union SR/SN arc": a
closed union-typed nat term is only known to BE a numeral once it is normal; turning an ARBITRARY closed
union-typed nat term into one that REDUCES to a numeral needs strong normalization (to reach a normal
form) and subject reduction (to keep that normal form typed).

This file assembles exactly that step at the reducibility-CANDIDATE level, where the assembly is clean
and needs no separate subject-reduction-along-the-chain replay.  The head-expansion-closed data candidate
is

  `dataTaitCandidate IsNatNumeral subject  :=  IsStronglyNormalizing subject ∧
     ∀ nf, StepStar subject nf → isStepNormalForm nf → (IsNatNumeral nf ∨ IsNeutral nf)`

(`FX1Poly/Core/.../DataTaitCandidate.lean`, uniform in the value predicate — instantiated here at
`IsNatNumeral`).  Membership is therefore assembled from precisely the two pieces the deferred arc owns:

  * **`subjectStronglyNormalizing`** — union SN of the subject (the dominant missing lever; absent over
    `HasTypeUnion`, the union analogue of `HasTypeDescPi.closedStronglyNormalizing`).
  * **`reachableNormalFormsTyped`** — union SR along reductions, in the only form the classifier needs:
    every reachable normal form is itself union-typed at `natTypeCell` and bridge-fragment-free.  (Bundled
    rather than split into "SR step" + "fragment preservation" because that bundle is exactly what
    `closedNormalNatNumeral` consumes.)

Given those two, every reachable normal form is a deep numeral via `closedNormalNatNumeral` (the
left/`IsNatNumeral` disjunct — the neutral disjunct never fires), so the subject is a candidate member;
`dataTaitCandidate.closedReducesToValue` then extracts canonicity: the subject REDUCES to a numeral.

## Honest scope — what this is and is NOT

This is the machine-checked REDUCTION of unconditional closed-Nat canonicity to the deferred union SN/SR
arc (FTGEN-14 / the "deferred union SR/SN arc" named at `NatNumeralUnionCanonicity.lean`).  It is NOT
itself unconditional: the two premises ARE the open arc.  The payoff is that once union SN and the
along-reduction typing land for the nat lane, `closedNatReducesToNumeralFromNormalization` becomes
premise-free by direct application — the canonicity capstone is then a one-liner, not a fresh proof.  The
premises are satisfiable on the already-normal fragment (a closed numeral is its own only reachable normal
form, SN-trivially via `IsStronglyNormalizing.ofIsStepNormalForm`), so the statement is non-vacuous; the
substance pending the arc is the NON-normal (computing) fragment, exactly where raw `natElim` is
partial-class and SN must come from reducibility.

The `pathApp` / `pathLam` exclusion riding inside `reachableNormalFormsTyped` is the honest core-`Step`
fragment boundary inherited verbatim from `closedNormalNatNumeral` (the bridge/interval rows live outside
core β/ι); it drops once endpoint-β lands in core `Step`.

## Zero-axiom

`dataTaitCandidate.closedReducesToValue` (per-term confluence over `Acc`, axiom-clean) composed with the
union deep canonical-forms theorem and a two-arm projection.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditNatUnionReducesToNumeral.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **Closed-Nat data-candidate membership from normalization.**  A closed term whose union-SN holds and
whose every reachable normal form is union-typed at `natTypeCell` (bridge-fragment-free) is a member of the
head-expansion-closed Nat data candidate `dataTaitCandidate IsNatNumeral`.  The first conjunct is the
supplied SN; the second classifies each reachable normal form as a deep numeral via the union headline
`closedNormalNatNumeral` (the neutral disjunct is never taken). -/
theorem HasTypeUnion.closedNatDataCandidateFromNormalization {profile : PolyProfile}
    {subject : RawTerm 0}
    (subjectStronglyNormalizing : IsStronglyNormalizing subject)
    (reachableNormalFormsTyped :
      ∀ normalForm : RawTerm 0, StepStar subject normalForm →
        RawTerm.isStepNormalForm normalForm →
        HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
            normalForm natTypeCell ∧
          RawTerm.containsGeneratorBool .gen_pathApp normalForm = false ∧
          RawTerm.containsGeneratorBool .gen_pathLam normalForm = false) :
    dataTaitCandidate IsNatNumeral subject := by
  refine ⟨subjectStronglyNormalizing, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨normalFormTyped, normalFormAppFree, normalFormLamFree⟩ :=
    reachableNormalFormsTyped normalForm reaches normalFormIsNormal
  exact Or.inl (HasTypeUnion.closedNormalNatNumeral normalFormTyped normalFormIsNormal
    normalFormAppFree normalFormLamFree)

/-- **★ Closed-Nat canonicity REDUCES-to-numeral over the single union judgment.**  Given union SN of the
subject and along-reduction nat-typing of its reachable normal forms, the subject reduces to a deep
numeral.  This is the reduces-to form `NatNumeralUnionCanonicity` defers to the union SN/SR arc: the
membership `closedNatDataCandidateFromNormalization` fed to `dataTaitCandidate.closedReducesToValue`.  Once
the deferred arc supplies the two premises, this becomes premise-free closed-Nat canonicity. -/
theorem HasTypeUnion.closedNatReducesToNumeralFromNormalization {profile : PolyProfile}
    {subject : RawTerm 0}
    (subjectStronglyNormalizing : IsStronglyNormalizing subject)
    (reachableNormalFormsTyped :
      ∀ normalForm : RawTerm 0, StepStar subject normalForm →
        RawTerm.isStepNormalForm normalForm →
        HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
            normalForm natTypeCell ∧
          RawTerm.containsGeneratorBool .gen_pathApp normalForm = false ∧
          RawTerm.containsGeneratorBool .gen_pathLam normalForm = false) :
    ∃ value : RawTerm 0, StepStar subject value ∧ IsNatNumeral value ∧
      RawTerm.isStepNormalForm value :=
  dataTaitCandidate.closedReducesToValue
    (HasTypeUnion.closedNatDataCandidateFromNormalization (profile := profile)
      subjectStronglyNormalizing reachableNormalFormsTyped)

end FX1Poly.Typed
