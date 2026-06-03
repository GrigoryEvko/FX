import FX1Poly.Typed.DenoteKeyedReducibility

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

This is the denote-keyed `piArm` content at the type-former level: the universe-domain Π is uniformly
reducible, which the fuel model provably could not establish.  It is the load-bearing step toward discharging
the actual SN-043 gate `HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes` over the non-fuel
relation.

## Zero-axiom verification

Both theorems are direct applications of `universeMembership_levelIrrelevant` (the headline level-irrelevance,
itself `ofPointwiseIff`-clean) and the `ReducibleTypeStepDenote.piType` / `.universeCode` constructors.  No
`induction`, no `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
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

end FX1Poly.Typed
