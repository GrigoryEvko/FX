import FX1Poly.Typed.DenoteKeyedUniverseDomainPi
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate
import FX1Poly.Typed.DenoteKeyedReducibilitySmoke

/-! # FX1Poly/Typed/DenoteKeyedUniverseDomainPiArm
    — the universeCode arm of the ofReducibleTypeStepDenote piArm case-split (toward SN-043/#752)

The `ofReducibleTypeStepDenote` piArm (`DenoteKeyedLevelIrrelevance.lean`) is discharged by `cases` on the
domain step `domainReducible : ReducibleTypeStepDenote env lowerAt domainCode domainCandidate`.  The neutral and
uniform-candidate arms are the adapters in `DenoteKeyedGeneralDomainPiArm.lean`.  THIS file is the `universeCode`
arm — the domain is a universe code `Type@innerLevelExpr`, the one case the neutral/uniform adapters cannot reach
(the universe membership candidate DRIFTS with the level: empty below the inner decoded level, real above).

## The threshold

The A2 bridge `universeMemberReducibleAtLevel` invokes the backbone at `lowerAt = denoteBelowFamily env
outerLevel` for the OUTER classifier's decoded level `outerLevel`.  The backbone's universeCode-arm domain
candidate is then `universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr`.  This arm needs
the threshold `denote innerLevelExpr env < outerLevel` — the inner universe strictly below the outer classifier.
That holds for any WELL-TYPED Π by the Π-formation level constraint (`Type@innerLevelExpr : Type@outerLevel`
forces `denote innerLevelExpr env < outerLevel`), so it is carried here as an explicit gated hypothesis rather
than a defect.  The complementary high-inner-universe case (`denote innerLevelExpr env ≥ outerLevel`, where the
backbone's codomain IH is vacuous yet high output levels have non-empty domain) is unreachable for well-typed
input and is NOT discharged here — see the ledger diagnosis.

## The construction (no codomain member-stability needed)

`IsReducibleTypeAtAllDenoteLevels` is assembled PER OUTPUT LEVEL — each level an independent `piType` node — so
the codomain candidate may DRIFT across levels (the canonical member-predicate at that level).  No codomain
uniformity / member-stability is required, unlike the uniform-domain arm.  At each output level the domain
sub-case splits on the inner-vs-output threshold:
  * above (`denote innerLevelExpr env < outputLevel`): the domain membership decodes to `SN ∧ reducible-as-type
    at the inner level`; by the gated threshold the backbone's domain candidate decodes to the SAME predicate,
    so the codomain IH fires, and its canonical member-predicate is the codomain candidate;
  * at-or-below (`outputLevel ≤ denote innerLevelExpr env`): the domain candidate is empty, so the codomain
    obligation is discharged vacuously.

## Decode lemmas

`universeDenotePredicate_belowFamily_aboveThreshold` / `_empty` decode the `lowerAt`-keyed universe membership
predicate `universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr` into the threshold form
(`denoteBelowFamily_eq_reducible` above, `denoteBelowFamily_eq_empty_of_ge` at/below) — the reusable bridges any
universe-domain reducibility argument needs.

## Zero-axiom verification

All three declarations: `unfold` + `rw` (decode lemmas), `intro` + `refine` `piType` + `by_cases` + decode-rewrite
(the arm).  No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega` (checked: depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Above-threshold decode of the lowerAt-keyed universe membership predicate.**  When the inner universe's
decoded level is strictly below the outer classifier level, `universeDenotePredicate env (denoteBelowFamily env
outerLevel) innerLevelExpr` decodes EXACTLY to "strongly-normalizing ∧ reducible-as-a-type at the inner decoded
level" — the below-family at the inner index IS the reducibility relation there (`denoteBelowFamily_eq_reducible`). -/
theorem universeDenotePredicate_belowFamily_aboveThreshold {scope : Nat} (env : Nat → Nat)
    (outerLevel : Nat) (innerLevelExpr : LevelExpr)
    (innerBelow : LevelExpr.denote innerLevelExpr env < outerLevel)
    (typeCode : RawTerm scope) :
    universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr typeCode
      = (IsStronglyNormalizing typeCode ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote innerLevelExpr env) typeCode) := by
  unfold universeDenotePredicate IsReducibleTypeAtDenote
  rw [denoteBelowFamily_eq_reducible env outerLevel (LevelExpr.denote innerLevelExpr env) innerBelow]

/-- **Empty decode of the lowerAt-keyed universe membership predicate.**  When the inner universe's decoded level
is at or above the outer classifier level, the below-family at the inner index is the EMPTY relation
(`denoteBelowFamily_eq_empty_of_ge`), so no type is a member: `universeDenotePredicate env (denoteBelowFamily env
outerLevel) innerLevelExpr` is uninhabited. -/
theorem universeDenotePredicate_belowFamily_empty {scope : Nat} (env : Nat → Nat)
    (outerLevel : Nat) (innerLevelExpr : LevelExpr)
    (innerAtOrAbove : outerLevel ≤ LevelExpr.denote innerLevelExpr env)
    (typeCode : RawTerm scope) :
    ¬ universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr typeCode := by
  intro membership
  obtain ⟨_strongNormalizing, _candidate, candidateMember⟩ := membership
  rw [denoteBelowFamily_eq_empty_of_ge env outerLevel (LevelExpr.denote innerLevelExpr env)
    innerAtOrAbove] at candidateMember
  exact candidateMember

/-- **The universeCode arm of the ofReducibleTypeStepDenote piArm (threshold-gated).**  When the domain is a
universe code `Type@innerLevelExpr` strictly below the outer classifier level (the well-typed-guaranteed
threshold), the dependent Π `Π (X : Type@innerLevelExpr). codomainCode` is denote-reducible at every level — fed
by the backbone's existential-candidate codomain IH keyed on the universe membership.  Assembled per output level:
above the inner level the domain membership decodes and the codomain IH fires with its canonical member-predicate;
at or below the inner level the domain is empty and the codomain obligation is vacuous.  The universeCode arm of
the #752 case-split (the neutral/uniform arms are in `DenoteKeyedGeneralDomainPiArm.lean`); the composite/
threshold-drift arm and the high-inner-universe case remain. -/
theorem universeDomainPiArmFromInductiveHypotheses {scope : Nat} (env : Nat → Nat) (outerLevel : Nat)
    (innerLevelExpr : LevelExpr) (innerFlag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (innerBelowOuter : LevelExpr.denote innerLevelExpr env < outerLevel)
    (codomainInductiveHypothesis : ∀ argument : RawTerm scope,
        universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr argument →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil)
          (.childCons codomainCode .childNil))) := by
  intro outputLevel
  refine ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env outputLevel (RawTerm.subst0 codomainCode argument))
    (ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag)
    (fun argument argumentInDomain => ?_)⟩
  by_cases aboveAtOutput : LevelExpr.denote innerLevelExpr env < outputLevel
  · have backboneMembership :
        universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr argument := by
      rw [universeDenotePredicate_belowFamily_aboveThreshold env outerLevel innerLevelExpr innerBelowOuter]
      rw [universeDenotePredicate_belowFamily_aboveThreshold env outputLevel innerLevelExpr aboveAtOutput]
        at argumentInDomain
      exact argumentInDomain
    exact (codomainInductiveHypothesis argument backboneMembership outputLevel).reducibleMemberCandidate
  · exact absurd argumentInDomain (universeDenotePredicate_belowFamily_empty env outputLevel innerLevelExpr
      (Nat.not_lt.mp aboveAtOutput) argument)

/-- **Universe-domain `memberStableToOuter` instance (threshold-gated).**  A denote-reducible member of the
universe code `Type@innerLevelExpr` at any source level is a member at the fixed `outerLevel`, given the
well-typedness threshold `denote innerLevelExpr env < outerLevel`.  A member at the source forces `denote
innerLevelExpr env < sourceLevel` (else the universe candidate is empty there, `_empty`); the source membership
decodes (`_aboveThreshold`) to `SN ∧ reducible-as-type at the inner level`, which is EXACTLY the candidate at
`outerLevel` (also above the inner level), so the member transports.  This is the `memberStableToOuter` the
unified `piArmFromMemberStabilityToOuterLevel` consumes for a universe-code domain — the unified-piArm route to
the universeCode arm. -/
theorem universeDomainMemberStableToOuter {scope : Nat} (env : Nat → Nat) (outerLevel : Nat)
    (innerLevelExpr : LevelExpr) (innerFlag : UniverseFlag)
    (innerBelowOuter : LevelExpr.denote innerLevelExpr env < outerLevel)
    (sourceLevel : Nat) (argument : RawTerm scope)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil) argument) :
    IsReducibleMemberAtDenote env outerLevel
      (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil) argument := by
  obtain ⟨sourceCandidate, sourceReducible, candidateArgument⟩ := memberAtSource
  have universeArgument : universeDenotePredicate env (denoteBelowFamily env sourceLevel)
      innerLevelExpr argument :=
    (ReducibleTypeAtDenote.deterministic sourceReducible
      (ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag) argument).mp candidateArgument
  by_cases innerBelowSource : LevelExpr.denote innerLevelExpr env < sourceLevel
  · rw [universeDenotePredicate_belowFamily_aboveThreshold env sourceLevel innerLevelExpr innerBelowSource]
      at universeArgument
    refine ⟨universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr,
      ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag, ?_⟩
    rw [universeDenotePredicate_belowFamily_aboveThreshold env outerLevel innerLevelExpr innerBelowOuter]
    exact universeArgument
  · exact absurd universeArgument (universeDenotePredicate_belowFamily_empty env sourceLevel innerLevelExpr
      (Nat.not_lt.mp innerBelowSource) argument)

/-- **A universe code is NOT all-levels member-stable — the precise #672 residual boundary.**  `compositeDomain
MemberStableToOuter` (`DenoteKeyedGeneralDomainPiArm.lean`) reduces a composite domain's member-stability to its
COMPONENTS' all-levels both-directions member-stability.  This theorem shows that boundary is sharp: a universe
code `Type@innerLevelExpr` is NOT all-levels member-stable, so a composite domain CONTAINING a universe-code
component (the threshold-drift case) canNOT have its component satisfy the composite arm's premise — those domains
remain the open #672 residual, NOT closed by the member-stability route.

The witness: `var index` is a reducible member of `Type@innerLevelExpr` at the level just above the inner decoded
level (it decodes to `SN (var index) ∧ reducible-as-type at the inner level` — `var` is SN with no steps and is
a `neutral` reducible type), but at level 0 the universe candidate is EMPTY (`denoteBelowFamily env 0` is the
everywhere-False base), so `var index` is NOT a member there.  Member-stability from the high level to level 0
would carry the high member down to the empty low candidate — contradiction.

This is the rigorous refutation of the over-broad reading "the composite arm absorbs the drift": the drift lives
at the universe LEAVES, where member-stability genuinely FAILS below the threshold (vacuous low-level
inhabitation of any Π over the universe code does not lift).  Closing the threshold-drift composites needs a
DIFFERENT argument than all-levels member-stability — the level-indexed candidate must track the threshold per
component, the genuine open #672 heart. -/
theorem universeCodeNotAllLevelsMemberStable {scope : Nat} (env : Nat → Nat)
    (innerLevelExpr : LevelExpr) (innerFlag : UniverseFlag) (index : Fin scope) :
    ¬ (∀ (sourceLevel targetLevel : Nat) (argument : RawTerm scope),
        IsReducibleMemberAtDenote env sourceLevel
          (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil) argument →
        IsReducibleMemberAtDenote env targetLevel
          (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil) argument) := by
  intro stability
  have memberHigh : IsReducibleMemberAtDenote env (LevelExpr.denote innerLevelExpr env + 1)
      (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil)
      (.mkGen .gen_var index .childNil) := by
    refine ⟨universeDenotePredicate env
      (denoteBelowFamily env (LevelExpr.denote innerLevelExpr env + 1)) innerLevelExpr,
      ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag, ?_⟩
    rw [universeDenotePredicate_belowFamily_aboveThreshold env (LevelExpr.denote innerLevelExpr env + 1)
      innerLevelExpr (Nat.lt_succ_self _)]
    exact ⟨isStronglyNormalizing_of_noStep (fun _reduct step => noStep_var index step),
      smoke_neutralVariable_isReducibleAtDenote env (LevelExpr.denote innerLevelExpr env) index⟩
  obtain ⟨candidateZero, reducibleZero, candidateVar⟩ :=
    stability (LevelExpr.denote innerLevelExpr env + 1) 0 (.mkGen .gen_var index .childNil) memberHigh
  have universeZero : universeDenotePredicate env (denoteBelowFamily env 0) innerLevelExpr
      (.mkGen .gen_var index .childNil) :=
    (ReducibleTypeAtDenote.deterministic reducibleZero
      (ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag) _).mp candidateVar
  exact universeDenotePredicate_belowFamily_empty env 0 innerLevelExpr (Nat.zero_le _)
    (.mkGen .gen_var index .childNil) universeZero

end FX1Poly.Typed
