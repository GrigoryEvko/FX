import FX1Poly.Typed.DenoteKeyedUniverseDomainPi
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate

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

end FX1Poly.Typed
