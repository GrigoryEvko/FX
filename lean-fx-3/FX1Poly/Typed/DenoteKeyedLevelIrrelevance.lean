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

This file also ships the NON-universe half of the `piArm`:
  * `uniformDomainPi_reducibleAtEveryDenoteLevel` — the `piArm` for any domain whose candidate is a single
    predicate uniform across ALL levels (neutral / data / non-universe-containing former domains); at each
    level `piType` assembles the dependent arrow from the uniform domain candidate.
  * `neutralDomainPi_reducibleAtEveryDenoteLevel` — the witnessing instance: a neutral domain has the
    literally-uniform candidate `IsStronglyNormalizing` (the `neutral` arm).
The complementary universe-domain instance (candidate uniform only above `denote e env`) is
`DenoteKeyedUniverseDomainPi.universeDomainPi_reducibleAtEveryDenoteLevel`.

And the MEMBER-level complement (toward the denote #672 member-extension):
  * `uniformType_memberStableAcrossDenoteLevels` — a member of any type reducible with a single all-level
    uniform candidate is level-stable (via `ReducibleTypeAtDenote.deterministic`); the non-universe analogue
    of `DenoteKeyedUniverseDomainPi.universeDomainPi_memberStableAcrossDenoteLevels`.
  * `neutralType_memberStableAcrossDenoteLevels` — the witnessing neutral-type instance.

## Zero-axiom verification

The three leaves are anonymous-constructor wrappers of the `ReducibleTypeStepDenote.{neutral, whnfExpand}`
constructors and `universeCode_isReducibleAtDenote`; the backbone is one `induction` on
`ReducibleTypeStepDenote` with the level-independent motive `IsReducibleTypeAtAllDenoteLevels env typeCode`
(avoiding the indexed-match propext leak); the two `piArm` instances are `piType`-constructor wrappers (the
neutral one delegating to the uniform-candidate one); the two member-stability theorems are
`ReducibleTypeAtDenote.deterministic` + reassembly (the neutral one delegating to the uniform one).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
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
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (notEmpty : typeCode.rootGenerator ≠ Generator.gen_emptyCode) :
    IsReducibleTypeAtAllDenoteLevels env typeCode :=
  fun _level => ⟨IsStronglyNormalizing,
    ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse notEmpty⟩

/-- **Empty-code leaf.**  The empty type code `emptyTypeCell` is reducible at every denote level, with the
head-expansion-closed empty Tait candidate `emptyTaitCandidate` — the dedicated `dataEmpty` constructor does
not reference the lower family or the level, so it fires uniformly across levels (the candidate-bridge twin of
`ofNeutral` / `ofUniverseCode`). -/
theorem IsReducibleTypeAtAllDenoteLevels.ofDataEmpty {scope : Nat} {env : Nat → Nat} :
    IsReducibleTypeAtAllDenoteLevels env (emptyTypeCell (scope := scope)) :=
  fun _level => ⟨emptyTaitCandidate, ReducibleTypeStepDenote.dataEmpty⟩

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
  | neutral noWeakHeadStep notPiType notUniverse notEmpty =>
      exact IsReducibleTypeAtAllDenoteLevels.ofNeutral noWeakHeadStep notPiType notUniverse notEmpty
  | @piType domainCode codomainCode domainCandidate codomainCandidate domainReducible
      codomainReducible domainInductiveHypothesis codomainInductiveHypothesis =>
      exact piArm codomainCandidate domainReducible codomainReducible
        domainInductiveHypothesis codomainInductiveHypothesis
  | universeCode levelExpr flag =>
      exact IsReducibleTypeAtAllDenoteLevels.ofUniverseCode env levelExpr flag
  | dataEmpty =>
      exact IsReducibleTypeAtAllDenoteLevels.ofDataEmpty
  | ofPointwiseIff _innerReducible _pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis

/-- **Uniform-candidate-domain `piArm`.**  If the domain `domainCode` is reducible with a SINGLE candidate
`domainCandidate` at every denote level, and the codomain is reducible (under domain membership) at every
level with codomain-candidate function `codomainCandidate`, then `Π domainCode codomainCode` is reducible at
every denote level.  At each level `piType` assembles the dependent arrow directly — the uniform domain
candidate makes the codomain obligation the same shape at every level.  This is the `piArm` for every domain
whose candidate does NOT drift with the level (neutral types, data types, non-universe-containing formers); the
universe domain — whose candidate is uniform only ABOVE `denote e env` — is the complementary case handled by
`DenoteKeyedUniverseDomainPi.universeDomainPi_reducibleAtEveryDenoteLevel`.  Choice-free: the codomain
candidate is supplied as data (the fundamental-theorem-side existential extraction is a separate concern). -/
theorem uniformDomainPi_reducibleAtEveryDenoteLevel {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  fun level => ⟨_, ReducibleTypeStepDenote.piType codomainCandidate (domainReducible level)
    (fun argument argumentInDomain => codomainReducible level argument argumentInDomain)⟩

/-- **Neutral-domain `piArm` (the witnessing instance of the uniform-candidate piArm).**  A weak-head-normal
non-Π non-universe DOMAIN has the literally-uniform candidate `IsStronglyNormalizing` at every level (the
`neutral` arm references neither the lower family nor the level), so `uniformDomainPi_reducibleAtEveryDenoteLevel`
applies.  The denote analogue of the fuel `IsReducibleTypeAtAllLevels.piTypeOfNeutralDomain` — domains that are
type variables or stuck applications. -/
theorem neutralDomainPi_reducibleAtEveryDenoteLevel {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (notEmpty : domainCode.rootGenerator ≠ Generator.gen_emptyCode)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), IsStronglyNormalizing argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  uniformDomainPi_reducibleAtEveryDenoteLevel env IsStronglyNormalizing
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse notEmpty)
    codomainCandidate codomainReducible

/-- **Member-stability for a uniform-candidate type — the member-level complement of the uniform-candidate
piArm.**  If `typeCode` is reducible with a SINGLE candidate `candidate` at every denote level, then a reducible
member at one level is a reducible member at every level: the source-level candidate agrees pointwise with the
uniform `candidate` by `ReducibleTypeAtDenote.deterministic`, so the member sits in `candidate`, reducible at
the target level.  Unconditional (no level threshold), since the candidate never drifts.  This is the
non-universe analogue of `DenoteKeyedUniverseDomainPi.universeDomainPi_memberStableAcrossDenoteLevels` (which
holds only ABOVE `denote e env`); together they give member-stability across the denote-reducible type shapes,
the denote-keyed content of the #672 member-extension. -/
theorem uniformType_memberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (uniformReducible : ∀ level : Nat, ReducibleTypeAtDenote env level typeCode candidate)
    {term : RawTerm scope} {sourceLevel : Nat}
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel typeCode term)
    (targetLevel : Nat) :
    IsReducibleMemberAtDenote env targetLevel typeCode term := by
  obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAtSource
  have candidatesAgree :=
    ReducibleTypeAtDenote.deterministic sourceReducible (uniformReducible sourceLevel)
  exact ⟨candidate, uniformReducible targetLevel, (candidatesAgree term).mp memberInSource⟩

/-- **Member-stability for a neutral type (witnessing instance).**  A weak-head-normal non-Π non-universe type
has the literally-uniform candidate `IsStronglyNormalizing` at every level (the `neutral` arm), so its members
are level-stable.  Type variables and stuck applications used as classifiers. -/
theorem neutralType_memberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (notEmpty : typeCode.rootGenerator ≠ Generator.gen_emptyCode)
    {term : RawTerm scope} {sourceLevel : Nat}
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel typeCode term)
    (targetLevel : Nat) :
    IsReducibleMemberAtDenote env targetLevel typeCode term :=
  uniformType_memberStableAcrossDenoteLevels env
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse notEmpty)
    memberAtSource targetLevel

/-- **Member-stability for a uniform-domain Π TYPE.**  If the domain `domainCode` is reducible with a
single level-uniform candidate at every level, and the codomain is reducible (under domain membership)
with a level-uniform candidate function, then the Π type's OWN candidate
`fun functionTerm => ∀ argument, domainCandidate argument → codomainCandidate argument (app …)` is itself
level-uniform — so `uniformType_memberStableAcrossDenoteLevels` applies and a reducible member at one
level is reducible at every level.  This lifts member-stability from the neutral/uniform LEAF types
(`neutralType_/uniformType_memberStableAcrossDenoteLevels`) to the Π FORMER, for the non-universe-domain
case the cumulativity obstruction (`DenoteKeyedCumulativityObstruction`) does NOT block — the member-stable
fragment of the denote #672 member-extension, now covering dependent arrows over member-stable domains. -/
theorem uniformDomainPiType_memberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    {term : RawTerm scope} {sourceLevel : Nat}
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term)
    (targetLevel : Nat) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term :=
  uniformType_memberStableAcrossDenoteLevels env
    (fun level => ReducibleTypeStepDenote.piType codomainCandidate (domainReducible level)
      (fun argument argumentInDomain => codomainReducible level argument argumentInDomain))
    memberAtSource targetLevel

/-- **Neutral-domain Π member-stability (the witnessing instance).**  A weak-head-normal non-Π non-universe
DOMAIN has the literally-uniform candidate `IsStronglyNormalizing` at every level (the `neutral` arm), so
the uniform-domain Π member-stability applies.  The member-level analogue of
`neutralDomainPi_reducibleAtEveryDenoteLevel`; dependent arrows whose domain is a type variable or stuck
application have level-stable members. -/
theorem neutralDomainPiType_memberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (notEmpty : domainCode.rootGenerator ≠ Generator.gen_emptyCode)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), IsStronglyNormalizing argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    {term : RawTerm scope} {sourceLevel : Nat}
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term)
    (targetLevel : Nat) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term :=
  uniformDomainPiType_memberStableAcrossDenoteLevels env IsStronglyNormalizing
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse notEmpty)
    codomainCandidate codomainReducible memberAtSource targetLevel

end FX1Poly.Typed
