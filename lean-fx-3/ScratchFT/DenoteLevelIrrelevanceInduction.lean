import FX1Poly.Typed.DenoteKeyedUniverseDomainPi

/-! Scratch: the denote-keyed level-irrelevance INDUCTION backbone — the denote analogue of the fuel
`IsReducibleTypeAtAllLevels.ofReducibleTypeStep` (ReducibleTypeAtAllLevelsInduction.lean).  Induct on
`ReducibleTypeStepDenote env lowerAt typeCode candidate` with the level-independent motive
`IsReducibleTypeAtAllDenoteLevels env typeCode` (= ∀ level, IsReducibleTypeAtDenote env level typeCode);
discharge neutral / universeCode / whnfExpand / ofPointwiseIff unconditionally (each level-uniform in the
denote model), leaving `piType` as the supplied `piArm`.  The universe-domain piArm (last ticks) discharges the
hard impredicative case of that hypothesis. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- The denote-keyed "reducible at all levels" notion — analogue of `IsReducibleTypeAtAllLevels`. -/
def IsReducibleTypeAtAllDenoteLevels {scope : Nat} (env : Nat → Nat) (typeCode : RawTerm scope) : Prop :=
  ∀ level : Nat, IsReducibleTypeAtDenote env level typeCode

/-- Leaf: a weak-head-normal non-Π non-universe code is reducible at every denote level (candidate = SN, the
`neutral` arm, level-uniform). -/
theorem IsReducibleTypeAtAllDenoteLevels.ofNeutral {scope : Nat} {env : Nat → Nat} {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode) :
    IsReducibleTypeAtAllDenoteLevels env typeCode :=
  fun _level => ⟨IsStronglyNormalizing, ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse⟩

/-- Leaf: a universe code `Type@e` is reducible at every denote level (anti-vacuity, `universeCode` arm). -/
theorem IsReducibleTypeAtAllDenoteLevels.ofUniverseCode {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope) :=
  fun level => universeCode_isReducibleAtDenote env level levelExpr flag

/-- Closure: a redex inherits its weak-head contractum's all-level reducibility (the `whnfExpand` arm). -/
theorem IsReducibleTypeAtAllDenoteLevels.headExpand {scope : Nat} {env : Nat → Nat}
    {typeCode reduct : RawTerm scope} (weakHeadStep : WeakHeadStep typeCode reduct)
    (reductReducible : IsReducibleTypeAtAllDenoteLevels env reduct) :
    IsReducibleTypeAtAllDenoteLevels env typeCode := by
  intro level
  obtain ⟨candidate, candidateReducible⟩ := reductReducible level
  exact ⟨candidate, ReducibleTypeStepDenote.whnfExpand weakHeadStep candidateReducible⟩

/-- **Level-irrelevance by induction on the denote-keyed reducibility derivation, Π arm isolated.**  Denote
analogue of the fuel `IsReducibleTypeAtAllLevels.ofReducibleTypeStep`: every `ReducibleTypeStepDenote` arm but
`piType` is discharged unconditionally (redex via `headExpand`, neutral via `ofNeutral`, universe via
`ofUniverseCode`, congruence via the IH); `piType` is the supplied `piArm`.  The induction motive
`IsReducibleTypeAtAllDenoteLevels env typeCode` is level-independent, avoiding the indexed-match propext leak. -/
theorem IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (piArm : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env lowerAt domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) →
        IsReducibleTypeAtAllDenoteLevels env domainCode →
        (∀ argument : RawTerm scope, domainCandidate argument →
          IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) →
        IsReducibleTypeAtAllDenoteLevels env
          (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    IsReducibleTypeAtAllDenoteLevels env typeCode := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact IsReducibleTypeAtAllDenoteLevels.headExpand weakHeadStep reductInductiveHypothesis
  | neutral noWeakHeadStep notPiType notUniverse =>
      exact IsReducibleTypeAtAllDenoteLevels.ofNeutral noWeakHeadStep notPiType notUniverse
  | @piType domainCode codomainCode domainCandidate codomainCandidate domainReducible
      codomainReducible domainInductiveHypothesis codomainInductiveHypothesis =>
      exact piArm codomainCandidate domainReducible codomainReducible
        domainInductiveHypothesis codomainInductiveHypothesis
  | universeCode levelExpr flag =>
      exact IsReducibleTypeAtAllDenoteLevels.ofUniverseCode env levelExpr flag
  | ofPointwiseIff _innerReducible _pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis

end FX1Poly.Typed

#print axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.ofNeutral
#print axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.ofUniverseCode
#print axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.headExpand
#print axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote
