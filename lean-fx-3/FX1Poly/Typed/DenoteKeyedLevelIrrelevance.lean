import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedLevelIrrelevance
    — type-level level-irrelevance by induction on the denote-keyed reducibility derivation

This is the denote-keyed analogue of the fuel-model `IsReducibleTypeAtAllLevels.ofReducibleTypeStep`
(`ReducibleTypeAtAllLevelsInduction.lean`).  Where the fuel induction had to leave the universe-domain Π arm
as a genuine fixpoint it provably could not close (its frontier note), the denote model's universe arm decodes
at the FIXED classifier level, so the hard `piType` arm is dischargeable for the impredicative universe domain
by `DenoteKeyedUniverseDomainPi.universeDomainPi_reducibleAtAllDenoteLevels` — this file isolates the same
`piType`-as-hypothesis induction backbone over the denote relation.

The "all-levels" notion is `IsReducibleTypeAtAllDenoteLevels env typeCode := ∀ level, IsReducibleTypeAtDenote
env level typeCode`.  The induction on `ReducibleTypeStepDenote env lowerAt typeCode candidate` discharges four
of the five arms unconditionally, each LEVEL-UNIFORM in the denote model:

  * `whnfExpand` — a redex inherits its weak-head contractum's all-level reducibility (`headExpand`: rewrap the
    contractum's per-level candidate through the `whnfExpand` constructor at each level);
  * `neutral` — a weak-head-normal non-Π non-universe code is all-level reducible with the SN candidate
    (`ofNeutral`: the `neutral` constructor does not reference the lower family, so it fires at every level);
  * `universeCode` — a universe code `Type@e` is all-level reducible (`ofUniverseCode`: the denote universe arm
    fires unconditionally, `universeCode_isReducibleAtDenote`, no fuel-0 vacuity);
  * `ofPointwiseIff` — the inner derivation is on the SAME code, so its induction hypothesis is the goal;
  * `piType` — the supplied `piArm` (general over arbitrary domain).  Its impredicative universe-domain instance
    is what the fuel model could not close; the denote model closes it via the level-stable universe candidate.

So `ofReducibleTypeStepDenote` is the inductive backbone of denote-keyed type-level level-irrelevance: a proof
of the `piArm` alone (universe-domain instance + neutral/data-domain instance) completes level-irrelevance for
every denote-reducible type.

## Zero-axiom verification

The three leaves are anonymous-constructor wrappers of the `ReducibleTypeStepDenote.{neutral, whnfExpand}`
constructors and `universeCode_isReducibleAtDenote`; the backbone is one `induction` on
`ReducibleTypeStepDenote` with the level-independent motive `IsReducibleTypeAtAllDenoteLevels env typeCode`
(avoiding the indexed-match propext leak).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- The denote-keyed "reducible at all levels" notion — the analogue of `IsReducibleTypeAtAllLevels`: a type
code is reducible at EVERY denote-keyed ambient level. -/
def IsReducibleTypeAtAllDenoteLevels {scope : Nat} (env : Nat → Nat) (typeCode : RawTerm scope) : Prop :=
  ∀ level : Nat, IsReducibleTypeAtDenote env level typeCode

/-- **Neutral leaf.**  A weak-head-normal non-Π non-universe code is reducible at every denote level, with the
strong-normalization candidate — the `neutral` constructor does not reference the lower family, so it fires
uniformly across levels. -/
theorem IsReducibleTypeAtAllDenoteLevels.ofNeutral {scope : Nat} {env : Nat → Nat} {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode) :
    IsReducibleTypeAtAllDenoteLevels env typeCode :=
  fun _level => ⟨IsStronglyNormalizing, ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse⟩

/-- **Universe leaf.**  A universe code `Type@levelExpr` is reducible at every denote level — the denote
universe arm fires unconditionally (`universeCode_isReducibleAtDenote`), with no fuel-0 vacuity. -/
theorem IsReducibleTypeAtAllDenoteLevels.ofUniverseCode {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope) :=
  fun level => universeCode_isReducibleAtDenote env level levelExpr flag

/-- **Weak-head-expansion closure.**  A redex inherits its weak-head contractum's all-level reducibility: at
each level, rewrap the contractum's candidate through the `whnfExpand` constructor. -/
theorem IsReducibleTypeAtAllDenoteLevels.headExpand {scope : Nat} {env : Nat → Nat}
    {typeCode reduct : RawTerm scope} (weakHeadStep : WeakHeadStep typeCode reduct)
    (reductReducible : IsReducibleTypeAtAllDenoteLevels env reduct) :
    IsReducibleTypeAtAllDenoteLevels env typeCode := by
  intro level
  obtain ⟨candidate, candidateReducible⟩ := reductReducible level
  exact ⟨candidate, ReducibleTypeStepDenote.whnfExpand weakHeadStep candidateReducible⟩

/-- **Level-irrelevance by induction on the denote-keyed reducibility derivation, Π arm isolated.**  Every
`ReducibleTypeStepDenote` arm but `piType` is discharged unconditionally (redex via `headExpand`, neutral via
`ofNeutral`, universe via `ofUniverseCode`, congruence via the induction hypothesis); the `piType` arm is the
supplied `piArm` (general over the domain).  The level-independent motive `IsReducibleTypeAtAllDenoteLevels env
typeCode` makes the full (non-partial) induction propext-clean.

This is the denote analogue of the fuel `IsReducibleTypeAtAllLevels.ofReducibleTypeStep`.  The crucial
difference: the fuel `piArm` for an impredicative universe domain was an irreducible fixpoint; here it is
dischargeable (`DenoteKeyedUniverseDomainPi.universeDomainPi_reducibleAtAllDenoteLevels` for the
universe-domain instance), because the denote universe candidate is level-stable. -/
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
