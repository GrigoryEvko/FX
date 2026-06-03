import FX1Poly.Typed.FundamentalAtAllVectorPremises
import FX1Poly.Typed.FundamentalAtAllPositiveArguments
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.FundamentalLevelIndexed

/-! # FX1Poly/Typed/FormationEngineFundamental
    — the formation-engine fundamental theorem, arm by arm (#674; the SN-027 Kripke residual)

The Kripke route reduces SN-027 (`HasTypeDescPi → reducible / SN`) to a SINGLE obligation
(`FormationEngineFundamentalReduction.lean`): the formation-engine fundamental theorem

```
formationFundamental :
  ∀ {scope context subject classifier},
    HasTypeDesc profile context subject classifier → IsFundamentalConclusionAtVector context subject classifier
```

`HasTypeDesc` is the four-constructor formation sub-engine — `var` / `conv` / `universeFormation` /
`genFormation` — with NO `piIntro` / `piElim`.  This file assembles `formationFundamental` arm by arm; each arm
is a standalone theorem so it can be gated and reviewed independently, and the final assembly is one `induction`.

Unlike the refined-motive-via-`ValidTyping` route (whose conjunct-2 is provably unsatisfiable for type variables,
`ValidTypingVariableLevelPinned.lean`), the conclusion here is the REDUCIBILITY-keyed
`IsFundamentalConclusionAtVector` (`IsReducibleMemberAt`), so the `var` arm reads the environment
(`ReducibleEnvVec.lookupReducible`) rather than pinning a `ValidTyping` level — no wall.

## What is proved (so far)

* `formationFundamentalUniverseFormationArm` — the `universeFormation` arm: `Type@e` is a reducible member of
  `Type@(lsucc e)` at every positive level.  The universe code is closed (no children, no binders), so `subst`
  is the identity and the arm is `IsReducibleMemberAt.universeFormation` under the substitution — independent of
  the environment-level vector.
* `formationFundamentalConvArm` — the `conv` arm (binary helper over the two inductive premises): subject member
  of `classifier` + reclassifier member of `Type@levelExpr` + a conversion give the subject as a member of the
  reclassifier, via `castAlongConvUnderSubst`.  Level-preserving — no level mismatch.

* `formationFundamentalVarArmOfAllPositiveMember` — the `var` arm with its residual ISOLATED.
  `IsFundamentalConclusionAtVector` concludes at an ARBITRARY `predLevel + 1`, but `ReducibleEnvVec` supplies
  each variable at its single STORED level only.  Since `IsReducibleMemberAt level T t = ∃ candidate,
  ReducibleTypeAt level T candidate ∧ candidate t`, the level-dependence lives ENTIRELY in `ReducibleTypeAt level
  T`, whose cross-positive-level extension is the universe-domain-Π fixpoint (#672).  So the arm reduces EXACTLY
  to: the variable's substituted member at ALL positive levels — read at `predLevel + 1` via `.atLevel`.

* `formationFundamentalGenFormationArm` — the `genFormation` arm: the generic former (Π/Σ via the
  `universeFormerOutput` rule) over a fundamentally-reducible child telescope is a reducible member of its output
  universe at every positive conclusion level.  Like `conv` it is LEVEL-PRESERVING — the universe-former output
  is level-flexible, so it needs NO #672 extension.  It is a thin `∀ envLevels predLevel` wrapper over the
  shipped, gated level-indexed former lemma `fundamentalGenFormationFormerLevelIndexed`: the
  `IsFundamentalConclusionAtVector` shape is exactly that lemma's `FundamentalConclusionLevelIndexed` universally
  quantified over the env-level vector and the positive conclusion level.

The complete formation-engine FT assembly (`formationFundamentalVectorOfAllVariablesPositive`,
`FormationEngineFundamentalAssembly.lean`) already discharges ALL four `HasTypeDesc` arms modulo the single
`variablesAllPositive` (#672) hypothesis — inlining the former logic over the formation telescope `DescTelescope`.
This standalone arm is the independently-reviewable NAMED companion at the grown-telescope (`DescTelescopePi`)
vector shape: the lift of `fundamentalGenFormationFormerLevelIndexed` from `FundamentalConclusionLevelIndexed` to
`IsFundamentalConclusionAtVector`, completing this file's arm-by-arm decomposition (universeFormation / conv /
var were standalone, genFormation was not).  It is NOT new metatheory — the assembly already proves the engine FT
— but it exposes the grown former membership at the vector conclusion as a reusable lemma.

## Remaining (#674 → #672)

* discharge `allPositiveMember` for every variable — the universe-domain-Π type-level all-positive extension
  (#672, the ACTUAL SN-027/SN-043 gate); the sole unconditional gap, shared with the ValidTyping route.

## Zero-axiom verification

`subst_universeCodeCell` (a `rfl`-grade rewrite), `IsReducibleMemberAt.universeFormation` (the shipped
universe-candidate non-degeneracy, SN-037), and `IsReducibleMemberAt.castAlongConvUnderSubst` (Conv-invariance of
reducible membership, SN-034).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The `universeFormation` arm of the formation-engine FT.**  `universeCodeCell levelExpr flag`
(i.e. `Type@levelExpr[flag]`) is a reducible member of `universeCodeCell levelExpr.lsucc flag` at every requested
positive conclusion level `predLevel + 1`.  The universe code is closed, so the closing substitution acts as the
identity on both subject and classifier (`subst_universeCodeCell`), and the membership is exactly
`IsReducibleMemberAt.universeFormation` — independent of the environment-level vector, so it holds at the
arbitrary-vector conclusion shape. -/
theorem formationFundamentalUniverseFormationArm {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsFundamentalConclusionAtVector context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) := by
  intro _targetScope substitution _envLevels predLevel _env
  rw [subst_universeCodeCell, subst_universeCodeCell]
  exact IsReducibleMemberAt.universeFormation predLevel levelExpr flag

/-- **The `conv` arm of the formation-engine FT.**  Given the two sub-derivation fundamentals (the subject as a
member of `classifier`, and the reclassifier as a member of `universeCodeCell levelExpr flag`) plus a conversion
`classifier ~ reclassifier`, the subject is a member of `reclassifier`.  The conv arm is LEVEL-PRESERVING — no
level mismatch (contrast the `var` arm): instantiate the reclassifier fundamental one level up
(`predLevel + 1`), `tarskiDecode` its universe membership to a reducible TYPE at `predLevel + 1`, then
`castAlongConvUnderSubst` transports the subject's `predLevel + 1` membership across the substituted conversion
onto the reclassifier — exactly the level-indexed conv arm (`fundamentalConvLevelIndexed`) at the AtVector shape.
Stated as a binary helper over the two inductive premises; the four-arm assembly threads it. -/
theorem formationFundamentalConvArm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectIH : IsFundamentalConclusionAtVector context subject classifier)
    (reclassifierIH : IsFundamentalConclusionAtVector context reclassifier
      (universeCodeCell levelExpr flag))
    (converts : Conv classifier reclassifier) :
    IsFundamentalConclusionAtVector context subject reclassifier := by
  intro _targetScope substitution envLevels predLevel env
  have reclassifierMember := reclassifierIH substitution (predLevel + 1) env
  rw [subst_universeCodeCell] at reclassifierMember
  obtain ⟨_candidate, reclassifierReducible⟩ := reclassifierMember.tarskiDecode
  exact IsReducibleMemberAt.castAlongConvUnderSubst substitution
    (subjectIH substitution predLevel env) reclassifierReducible converts

/-- **The `var` arm of the formation-engine FT, with its residual ISOLATED to the all-positive member extension
(= the #672 fixpoint gate).**  `IsFundamentalConclusionAtVector` concludes at an ARBITRARY `predLevel + 1`, but
`ReducibleEnvVec` supplies each variable at its single STORED level `envLevels index` only — and since
`IsReducibleMemberAt level T t = ∃ candidate, ReducibleTypeAt level T candidate ∧ candidate t`, the
level-dependence lives ENTIRELY in `ReducibleTypeAt level T`, whose extension across positive levels is the
universe-domain-Π fixpoint (the documented SN-027 obstruction, tracked as #672).  So the var arm reduces EXACTLY
to: the variable's substituted member is reducible at ALL positive levels.  Given that hypothesis, the arm reads
it at `predLevel + 1` via `.atLevel`.  The hypothesis is precisely what `ReducibleEnvVec`'s single-level member
does NOT provide; discharging it for every variable is the #672 fixpoint.  This isolates the formation FT's sole
genuine residual — both the ValidTyping route (`ValidTypingVariableLevelPinned.lean`) and this Kripke route bottom
out at the SAME variable obstruction. -/
theorem formationFundamentalVarArmOfAllPositiveMember {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope)
    (allPositiveMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      {envLevels : Fin scope → Nat} (_env : ReducibleEnvVec envLevels context substitution),
      IsReducibleMemberAtAllPositiveLevels
        (RawTerm.subst substitution (context.lookup index))
        (RawTerm.subst substitution (variableCell index))) :
    IsFundamentalConclusionAtVector context (variableCell index) (context.lookup index) := by
  intro _targetScope substitution envLevels predLevel env
  exact (allPositiveMember substitution env).atLevel predLevel

/-- **The `genFormation` arm of the formation-engine FT — #672-INDEPENDENT, level-preserving.**  The generic
former `mkGen generator payload children` (Π/Σ via the `universeFormerOutput` rule, the only `typingRuleDescOf`
rows) over a fundamentally-reducible child telescope is a reducible member of its output universe
`rule.outputType scope levels flag` at every positive conclusion level `predLevel + 1`.  Unlike the `var` arm,
this needs NO all-positive member extension (#672): the universe-former output is level-flexible — `toPiMember`/
`toSigmaMember` build the former membership at the requested `predLevel + 1` directly, and `TelescopeReducible`'s
`headMember` is already all-level-quantified, so no per-child level coordination is required.  The arm is a thin
`∀ envLevels predLevel` wrapper over the shipped, gated `fundamentalGenFormationFormerLevelIndexed`:
`IsFundamentalConclusionAtVector context subject classifier` unfolds to
`∀ {envLevels} predLevel, FundamentalConclusionLevelIndexed envLevels (predLevel + 1) context subject classifier`,
so instantiating that lemma at the universally-quantified `(envLevels, predLevel)` and applying it to the
substitution and environment closes the goal.  The `telescopeFundamental` premise — the children's all-level
telescope reducibility under every closing reducible env — is the genFormation analogue of the `conv` arm's two
inductive premises; the shipped complete assembly `formationFundamentalVectorOfAllVariablesPositive` produces
the equivalent telescope reducibility from the mutual `DescTelescope` motive. -/
theorem formationFundamentalGenFormationArm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {generator : Generator} (payload : generator.payload scope)
    {children : RawTermChildren generator.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (premises : DescTelescopePi profile (currentDepth := 0) context levels flag children)
    (telescopeFundamental :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        {envLevels : Fin scope → Nat}
        (_env : ReducibleEnvVec envLevels context substitution)
        (shapeEq : generator.binderShifts = consecutiveShifts 0 levels.length),
        TelescopeReducible flag 0 levels.length substitution levels (shapeEq ▸ children)) :
    IsFundamentalConclusionAtVector context (.mkGen generator payload children)
      (rule.outputType scope levels flag) := by
  intro _targetScope substitution envLevels predLevel env
  exact fundamentalGenFormationFormerLevelIndexed envLevels predLevel payload isFormation premises
    (fun substitution env shapeEq => telescopeFundamental substitution env shapeEq) substitution env

end FX1Poly.Typed
