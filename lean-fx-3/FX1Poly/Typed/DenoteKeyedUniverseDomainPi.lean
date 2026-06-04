import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! # FX1Poly/Typed/DenoteKeyedUniverseDomainPi
    — the denote-keyed model closes the universe-domain Π former that the external-fuel model could not

`ReducibleTypeAtAllLevelsInduction.lean` (the fuel-model level-irrelevance induction) reduces type-level
positive level-irrelevance to ONE open arm, `piArm`, and its frontier note records the COMMITTED conclusion
that this arm — for a **dependent universe domain** `Π (X : Type@e). C[X]` — cannot be closed within the
external-`Nat`-fuel reducibility model.  The precise obstruction:

  * `IsReducibleTypeAt 0 (Π Type@e C)` is VACUOUS (the fuel-0 universe domain is the empty candidate), so it
    carries no information about `C` on real members and cannot feed the non-vacuous level-`1+` codomain
    obligation;
  * universe membership at level `k` admits every code reducible-at-`(k-1)`, so the candidates at successive
    levels GENUINELY DIFFER, and the `existsCongr` step cannot bridge `0 ↔ 1` at any finite fuel;
  * structural induction on the code is circular (domain members of `Type@e` are not sub-codes of the Π).

The frontier note's prescription is a NON-FUEL reformulation that recurses on the type code's **universe
level**, so the domain members of `Type@e` (level `≤ e`) become strictly smaller than `Type@e` (level `e+1`).
`DenoteKeyedReducibility.lean` is exactly that reformulation: the `universeCode` arm decodes membership at the
FIXED classifier level `LevelExpr.denote levelExpr env`, not at the ambient fuel.  Its headline
`universeMembership_levelIrrelevant` proves that, at every ambient level strictly above `denote levelExpr env`,
the `Type@levelExpr` candidate is the SAME decode-at-`denote levelExpr env` set — the candidate does NOT drift
with the level.  That is the exact negation of the fuel obstruction's "candidates at successive levels
genuinely differ."

This file harvests that into the two facts the fuel `piArm` lacked:

* `universeDomainCandidate_levelStable` — one fixed candidate is the `Type@levelExpr` candidate at every
  ambient level above `denote levelExpr env`.  The conceptual heart: in the denote model the universe-domain
  candidate is level-INVARIANT, so the `0 ↔ 1` bridge that fuel could not build is a single rewrite.
* `universeDomainPi_reducibleAtAllDenoteLevels` — the dependent universe-domain Π `Π (X : Type@e). C[X]` is
  reducible-as-a-type at EVERY ambient level above `denote levelExpr env`, with ONE uniform codomain-candidate
  function across all those levels.  Because the domain candidate is the level-stable fixed decode-set, a
  SINGLE codomain obligation (the codomain reducible under that fixed domain membership) discharges the
  `piType` constructor at every level simultaneously — no across-level member-extension is needed, so the
  circularity that defeated the fuel `piArm` never arises.
* `universeDomainPi_uniformCandidateAtAllDenoteLevels` — the uniform-candidate strengthening: ONE candidate
  (the dependent-arrow predicate over the fixed decode-set domain candidate) witnesses reducibility at every
  level above `denote levelExpr env`.  Pulls the existential outside the level quantifier — the form
  member-stability consumes.
* `universeDomainPi_memberStableAcrossDenoteLevels` — the #672-shaped payoff: a reducible MEMBER of
  `Π (X : Type@e). C[X]` at one level above `denote levelExpr env` is a reducible member at EVERY such level.
  The denote-keyed analogue of `IsReducibleMemberAtAllPositiveLevels` for the impredicative universe-domain Π,
  via the uniform candidate + `ReducibleTypeAtDenote.deterministic`.
* `universeDomainPi_reducibleAtEveryDenoteLevel` — totalises the type-level result to `∀ level`
  (`IsReducibleTypeAtAllDenoteLevels`, the backbone `piArm` shape): genuine levels reuse the above, low levels
  (`level ≤ denote levelExpr env`) are vacuous since the domain candidate is empty there.

This is the denote-keyed `piArm` content at the type-former level AND its member-stability corollary: the
universe-domain Π is reducible at every denote level (and uniformly above the domain's level) and its members
are level-stable, all of which the fuel model provably could not establish.  It is the load-bearing step toward
discharging the actual SN-043 gate `HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes` over the
non-fuel relation.

## Zero-axiom verification

All five theorems are direct applications of `universeMembership_levelIrrelevant` (the headline
level-irrelevance, itself `ofPointwiseIff`-clean), the `ReducibleTypeStepDenote.piType` / `.universeCode`
constructors, `ReducibleTypeAtDenote.deterministic` (member-stability), and `denoteBelowFamily_eq_empty_of_ge`
(the vacuous low-level case).  No `induction`, no `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Universe-domain candidate stability (the negation of the fuel obstruction).**  A single fixed candidate —
the decode-at-`denote levelExpr env` set — is the candidate of `Type@levelExpr` at EVERY ambient level strictly
above `denote levelExpr env`.  Where the external-fuel model has genuinely different universe candidates at
successive levels (so no `0 ↔ 1` bridge exists), the denote model decodes at the fixed classifier level, so the
candidate is literally level-invariant.  Both witnesses are one `universeMembership_levelIrrelevant`. -/
theorem universeDomainCandidate_levelStable {scope : Nat} (env : Nat → Nat) (level1 level2 : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (firstLevelAbove : LevelExpr.denote levelExpr env < level1)
    (secondLevelAbove : LevelExpr.denote levelExpr env < level2) :
    ∃ candidate : RawTerm scope → Prop,
      ReducibleTypeAtDenote env level1
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil) candidate ∧
      ReducibleTypeAtDenote env level2
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil) candidate :=
  ⟨fun member => IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member,
    universeMembership_levelIrrelevant env level1 levelExpr flag firstLevelAbove,
    universeMembership_levelIrrelevant env level2 levelExpr flag secondLevelAbove⟩

/-- **The denote-keyed universe-domain Π, reducible at every level above `denote levelExpr env`, with a
UNIFORM codomain candidate.**  This is the precise content the external-fuel `piArm` could not reach: the
dependent universe-domain Π `Π (X : Type@e). C[X]` is reducible-as-a-type at every ambient level above the
domain's decoded level `denote levelExpr env`, using ONE codomain-candidate function across all those levels.

Why this works here and not in the fuel model: the domain candidate is the level-stable fixed decode-set
(`universeMembership_levelIrrelevant`), so a SINGLE codomain obligation — the codomain reducible under that
fixed domain membership — discharges the `piType` constructor at every level simultaneously.  No
member-extension across levels is needed (the fuel obstruction), because the domain candidate never drifts. -/
theorem universeDomainPi_reducibleAtAllDenoteLevels {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ∀ argument : RawTerm scope,
        (IsStronglyNormalizing argument ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
          ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) :
    ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      IsReducibleTypeAtDenote env level
        (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons codomainCode .childNil))) := by
  intro level levelAbove
  exact ⟨_, ReducibleTypeStepDenote.piType codomainCandidate
    (universeMembership_levelIrrelevant env level levelExpr flag levelAbove)
    (fun argument argumentInDomain => codomainReducible level levelAbove argument argumentInDomain)⟩

/-- **Uniform-candidate form: ONE candidate works at every level above `denote levelExpr env`.**  Pulls the
existential of `universeDomainPi_reducibleAtAllDenoteLevels` OUTSIDE the level quantifier: the dependent
universe-domain Π `Π (X : Type@e). C[X]` has a SINGLE candidate (the dependent-arrow predicate over the fixed
decode-set domain candidate) that witnesses its reducibility at every ambient level above `denote levelExpr
env`.  This is the form member-stability consumes — a member of THAT candidate is a member at every such level
by definition, with no candidate to re-derive per level.  Possible precisely because the domain candidate is
level-stable (`universeMembership_levelIrrelevant`), so the dependent-arrow candidate is itself level-stable. -/
theorem universeDomainPi_uniformCandidateAtAllDenoteLevels {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ∀ argument : RawTerm scope,
        (IsStronglyNormalizing argument ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
          ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) :
    ∃ candidate : RawTerm scope → Prop, ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ReducibleTypeAtDenote env level
        (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons codomainCode .childNil)))
        candidate := by
  refine ⟨fun functionTerm => ∀ argument : RawTerm scope,
    (IsStronglyNormalizing argument ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
      codomainCandidate argument
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))), ?_⟩
  intro level levelAbove
  exact ReducibleTypeStepDenote.piType codomainCandidate
    (universeMembership_levelIrrelevant env level levelExpr flag levelAbove)
    (fun argument argumentInDomain => codomainReducible level levelAbove argument argumentInDomain)

/-- **Member-stability for the universe-domain Π — the #672-shaped payoff over the denote relation.**  A
reducible member of `Π (X : Type@e). C[X]` at ONE level above `denote levelExpr env` is a reducible member at
EVERY level above it.  This is the denote-keyed analogue of `IsReducibleMemberAtAllPositiveLevels` (the content
of #672 `HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes`) for the impredicative
universe-domain Π — the one type former the external-fuel model provably could not stabilise.

The proof is the uniform candidate plus determinism: the source-level candidate agrees (pointwise) with the
uniform candidate by `ReducibleTypeAtDenote.deterministic`, so the member lies in the uniform candidate, which
is reducible at the target level.  No across-level member transport, no fuel induction. -/
theorem universeDomainPi_memberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ∀ argument : RawTerm scope,
        (IsStronglyNormalizing argument ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
          ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument))
    {functionTerm : RawTerm scope}
    {sourceLevel : Nat} (sourceLevelAbove : LevelExpr.denote levelExpr env < sourceLevel)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons codomainCode .childNil))) functionTerm)
    {targetLevel : Nat} (targetLevelAbove : LevelExpr.denote levelExpr env < targetLevel) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons codomainCode .childNil))) functionTerm := by
  obtain ⟨uniformCandidate, uniformReducible⟩ :=
    universeDomainPi_uniformCandidateAtAllDenoteLevels env levelExpr flag codomainCandidate codomainReducible
  obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAtSource
  have candidatesAgree :=
    ReducibleTypeAtDenote.deterministic sourceReducible (uniformReducible sourceLevel sourceLevelAbove)
  exact ⟨uniformCandidate, uniformReducible targetLevel targetLevelAbove,
    (candidatesAgree functionTerm).mp memberInSource⟩

/-- **The universe-domain Π is reducible at EVERY denote level — total `IsReducibleTypeAtAllDenoteLevels`.**
This is the shape the level-irrelevance backbone's `piArm` consumes (`∀ level`, not `∀ level > denote e env`).
The genuine levels (`> denote levelExpr env`) reuse `universeDomainPi_reducibleAtAllDenoteLevels`; the low
levels (`level ≤ denote levelExpr env`) are vacuous: there the domain `Type@e` candidate is the EMPTY predicate
(`denoteBelowFamily_eq_empty_of_ge` makes the decode-at-`denote e env` family empty when `denote e env ≥
level`), so the `piType` constructor fires with the codomain obligation discharged vacuously from the empty
domain membership.  So the dependent universe-domain Π `Π (X : Type@e). C[X]` is reducible-as-a-type at every
ambient denote level, completing the type-level half of the universe-domain `piArm`. -/
theorem universeDomainPi_reducibleAtEveryDenoteLevel {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ∀ argument : RawTerm scope,
        (IsStronglyNormalizing argument ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
          ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons codomainCode .childNil))) := by
  intro level
  by_cases levelAbove : LevelExpr.denote levelExpr env < level
  · exact universeDomainPi_reducibleAtAllDenoteLevels env levelExpr flag codomainCandidate
      codomainReducible level levelAbove
  · have levelLe : level ≤ LevelExpr.denote levelExpr env := Nat.not_lt.mp levelAbove
    refine ⟨_, ReducibleTypeStepDenote.piType (fun _ => IsStronglyNormalizing)
      (ReducibleTypeStepDenote.universeCode levelExpr flag) (fun _argument argumentInDomain => ?_)⟩
    obtain ⟨_argumentSN, _candidate, candidateInEmptyFamily⟩ := argumentInDomain
    rw [denoteBelowFamily_eq_empty_of_ge env level (LevelExpr.denote levelExpr env) levelLe]
      at candidateInEmptyFamily
    exact candidateInEmptyFamily.elim

/-- **Member-stability for the universe LEAF above its decoded level — the leaf twin of
`universeDomainPi_memberStableAcrossDenoteLevels`.**  A reducible member of `Type@levelExpr` (a type code
classified by that universe) at ONE ambient level above `denote levelExpr env` is a reducible member at
EVERY level above it.  Where `DenoteKeyedLevelIrrelevance`'s `uniformType_/neutralType_memberStableAcross
DenoteLevels` cover only types whose candidate is uniform across ALL levels, the universe candidate is
uniform only ABOVE `denote levelExpr env` (below, it is the empty decode-set), so this needs the
above-the-bound restriction — exactly as the Π version does.

The proof is the universe twin of the Π member-stability: the fixed decode-at-`denote levelExpr env`
candidate (`universeMembership_levelIrrelevant`) is the universe's candidate at both the source and target
levels; `ReducibleTypeAtDenote.deterministic` reconciles the source member's candidate with it, so the
member sits in the fixed candidate, reducible at the target.  Choice-free (the candidate is canonical, not
existentially extracted), no across-level transport.  Completes the universe-leaf half of the denote #672
member-extension in the BOUNDED regime (the gap regime is the obstruction, see
`DenoteKeyedCumulativityObstruction`). -/
theorem universeLeafMemberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    {typeMember : RawTerm scope} {sourceLevel : Nat}
    (sourceLevelAbove : LevelExpr.denote levelExpr env < sourceLevel)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeMember)
    {targetLevel : Nat} (targetLevelAbove : LevelExpr.denote levelExpr env < targetLevel) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeMember := by
  obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAtSource
  have candidatesAgree := ReducibleTypeAtDenote.deterministic sourceReducible
    (universeMembership_levelIrrelevant env sourceLevel levelExpr flag sourceLevelAbove)
  exact ⟨_, universeMembership_levelIrrelevant env targetLevel levelExpr flag targetLevelAbove,
    (candidatesAgree typeMember).mp memberInSource⟩

end FX1Poly.Typed
