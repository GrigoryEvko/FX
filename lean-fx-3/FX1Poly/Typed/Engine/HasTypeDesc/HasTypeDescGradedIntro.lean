import FX1Poly.Typed.Engine.RuleTables.IntroRuleDescGradedBinder
import FX1Poly.Typed.Engine.RuleTables.GradedIntroRule
import FX1Poly.Typed.Metatheory.HostAdmissibility.OfGrownArmReflection

/-! # FX1Poly/Typed/HasTypeDescGradedIntro — NATIVE-23: pathLam as a native graded intro row (the KEYSTONE)

NATIVE-20 threaded `binderUsage` into the v1 `IntroRuleDesc`, but the v1 schema CANNOT express the
bridge abstraction: `outputType : (scope) → domain → codomain → output` parameterizes by a user-chosen
domain and a codomain, while the path abstraction's output is
`bridgeTypeCell typeCode (subst0 body interval0) (subst0 body interval1)` — BODY-DEPENDENT (the
endpoints are substitution instances of the introduced body), with the domain PINNED to
`intervalTypeCell` and the member cell `pathLamCell body` (one child, no domain annotation) instead of
`lamCell domain body`.  Three independent schema mismatches.  (This was the output of the bespoke
`HasTypeDescBridge.pathIntro` arm, retired NATIVE-45; the affine `pathLamGradedIntroRule` row below is now
the realization.)

This file is the campaign's intro-schema KEYSTONE — the introduction analogue of the NATIVE-12
TermIndexedFormer generalization, on the same proven template (table → single generic arm → metadata →
adequacy → smokes → coverage gate):

  * `GradedIntroRule` — the v2 introduction-rule description.  Per-row data: `domainCell` (the binder's
    domain — the type-parameter itself for λ, the PINNED `intervalTypeCell` for pathLam),
    `bodyClassifier` (what the body must inhabit under the extended context), `memberCell` (the
    introduced member's SHAPE — rule data, not hardwired), the BODY-DEPENDENT `outputType`, the
    `binderUsage` grade, and two `Bool` gates selecting which formation premises the row demands
    (λ demands domain + codomain formation exactly as `piIntro` does; pathLam demands neither, exactly
    as `pathIntro` does — premise PARITY with the bespoke arms, the delete-safety requirement).
  * `gradedIntroRuleOf` — the two-row table: `gen_lam` at `.omega` (unrestricted) and `gen_pathLam` at
    `.one` (affine).  The FIRST non-`.omega` introduction row — the graded check stops being inert.
  * `HasTypeDescGradedIntro` — ONE generic arm interpreting the table: implication-gated formation
    premises, the body premise at the rule's classifier, and the GRADED side-condition
    `gradedBinderChecks rule.binderUsage body` ENFORCED by the arm (not a dead-weight hypothesis: the
    `.one` row makes it a genuine occurrence bound, see the rejection below).
  * `gradedIntroEngine_typesLam` / `gradedIntroEngine_typesPathLam` — reconstruction: the grown `piIntro`
    premises (and the affine path-intro premises) drive the generic arm to the SAME subject and classifier.
  * `HasTypeDescGradedIntro.soundness` — ★ the reverse: EVERY generic typing is a λ introduction with a
    `HasTypeDescPi.piIntro`-built derivation, OR an affine pathLam introduction at the bridge classifier
    with the affine occurrence bound surfaced.  Together with the reconstructions: per-row adequacy.
  * `gradedIntroEngine_rejectsDoubleDimensionUse` — ★ THE GRADE IS LOAD-BEARING: the body
    `pair(var 0, var 0)` uses the dimension binder TWICE, so `pathLam` over it is UNTYPABLE through the
    engine at EVERY classifier.  First theorem where a kernel typing is refused purely by a usage grade
    read from a table row.
  * `GradedIntroEngineCoverage` + witness — the un-shrinkable property set.

The v1 `IntroRuleDesc`/dispatchers stay untouched (refactor by addition); the wave's intro rows
(NATIVE-34) extend THIS table, and the deletes phase (NATIVE-42/45) migrates the v1 consumers.

## Zero-axiom

The table is pure syntax; metadata is the established `by_cases` + `Option.some.inj` + `if_neg` pattern;
reconstructions are direct arm applications with gates discharged by `fun gate => Bool.noConfusion gate`
on the `false` rows; soundness is `cases` on the single arm (free indices — no equation-motive needed) +
table enumeration; the rejection routes through soundness (avoiding `cases` at a concrete index — the
banked propext trap) + head-generator no-confusion + `injections` body extraction + `Nat` arithmetic.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! The v2 introduction-rule table (`GradedIntroRule`, `lamGradedIntroRule`, `pathLamGradedIntroRule`,
`gradedIntroRuleOf`, and its metadata lemmas) is the live rule-data now homed in
`FX1Poly.Typed.Engine.RuleTables.GradedIntroRule`; this module keeps only the (deprecated)
description-driven introduction JUDGMENT that consumes it. -/

/-! ## The single-arm graded introduction engine -/

/-- **The description-driven graded introduction judgment (the NATIVE-23 core).**  ONE generic `genIntro`
arm: given a v2 table row, implication-gated formation premises (each demanded only when the row's gate
is `true` — premise PARITY with the bespoke arms), the body typed at the rule's classifier under the
rule's domain, and the GRADED side-condition `gradedBinderChecks rule.binderUsage body`, the rule's
member cell inhabits the rule's (body-dependent) output type.  The grade is read from the table and
ENFORCED here — at the `.one` row it is a genuine occurrence bound (see the rejection theorem). -/
inductive HasTypeDescGradedIntro (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | genIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : GradedIntroRule)
      (typeParamA : RawTerm scope) (typeParamB : RawTerm (scope + 1))
      (body : RawTerm (scope + 1))
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
      (isIntro : gradedIntroRuleOf generator = some rule)
      (binderGraded : gradedBinderChecks rule.binderUsage body)
      (domainFormed : rule.demandsDomainFormation = true →
        HasTypeUnion profile context (rule.domainCell scope typeParamA)
          (universeCodeCell domainLevel flag))
      (classifierFormed : rule.demandsClassifierFormation = true →
        HasTypeUnion profile (context.cons (rule.domainCell scope typeParamA))
          (rule.bodyClassifier scope typeParamA typeParamB)
          (universeCodeCell codomainLevel flag))
      (bodyTyped : HasTypeUnion profile (context.cons (rule.domainCell scope typeParamA))
        body (rule.bodyClassifier scope typeParamA typeParamB)) :
      HasTypeDescGradedIntro profile context
        (rule.memberCell scope typeParamA body)
        (rule.outputType scope typeParamA typeParamB body)

/-! ## Reconstruction: the bespoke premises drive the generic arm -/

/-- **The `piIntro` premises drive the generic arm at the λ row.**  Same subject (`lamCell`), same
classifier (`piTyCodeCell`) as `HasTypeDescPi.piIntro` — the graded check discharges by `.omega`. -/
theorem gradedIntroEngine_typesLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (contextLockFree : context.isLockFreeContext = true)
    (domainTyped :
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyTyped :
      HasTypeDescPi profile (context.cons domainCode) body codomainCode) :
    HasTypeDescGradedIntro profile context (lamCell domainCode body)
      (piTyCodeCell domainCode codomainCode) :=
  HasTypeDescGradedIntro.genIntro context .gen_lam lamGradedIntroRule
    domainCode codomainCode body domainLevel codomainLevel flag rfl trivial
    (fun _ => domainTyped.ofGrownReflected contextLockFree)
    (fun _ => codomainTyped.ofGrownReflected
      ((isLockFreeContext_cons context domainCode).trans contextLockFree))
    (bodyTyped.ofGrownReflected
      ((isLockFreeContext_cons context domainCode).trans contextLockFree))

/-- **The affine path-intro premises drive the generic arm at the affine pathLam row.**  Subject
`pathLamCell`, body-dependent classifier (the bridge code at the endpoint substitutions) — the affine path
abstraction the retired `HasTypeDescBridge.pathIntro` arm used to build; the affine premise IS the graded
check at `.one` (definitional); the absent formation premises are the row's `false` gates. -/
theorem gradedIntroEngine_typesPathLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {carrierCode : RawTerm scope} {body : RawTerm (scope + 1)}
    (bodyTyped : HasTypeDescPi profile (context.cons intervalTypeCell) body
      (RawTerm.weaken carrierCode))
    (dimensionAffine :
      RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1)
    (contextLockFree : context.isLockFreeContext = true) :
    HasTypeDescGradedIntro profile context (pathLamCell body)
      (bridgeTypeCell carrierCode
        (RawTerm.subst0 body intervalZeroCell)
        (RawTerm.subst0 body intervalOneCell)) :=
  HasTypeDescGradedIntro.genIntro context .gen_pathLam pathLamGradedIntroRule
    carrierCode (RawTerm.weaken carrierCode) body
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl dimensionAffine
    (fun gateHolds => Bool.noConfusion gateHolds)
    (fun gateHolds => Bool.noConfusion gateHolds)
    (bodyTyped.ofGrownReflected
      ((isLockFreeContext_cons context intervalTypeCell).trans contextLockFree))

/-! ## ★ Soundness: every generic typing is a bespoke derivation -/

/-- **★ Per-row soundness.**  Every `HasTypeDescGradedIntro` typing is EITHER a λ introduction with a
`HasTypeDescPi.piIntro`-built derivation at the SAME subject and classifier, OR an affine pathLam
introduction at the bridge classifier with the affine occurrence bound surfaced.  With the reconstructions
above this is per-row adequacy.  (The pathLam disjunct previously also carried a `HasTypeDescBridge.pathIntro`
derivation; that bespoke engine was retired (NATIVE-45) and the affine path abstraction is now realized only
by the uniform `HasTypeUnion.intro` builder at `pathLamIntroRule` — which is
defined downstream of this file, so the union witness cannot be carried here.  The surviving affine bound is
exactly the uniform `intro` arm's `sideHolds` side condition.)  `cases` at FREE indices (no equation-motive trap) + table
enumeration. -/
theorem HasTypeDescGradedIntro.soundness {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescGradedIntro profile context subject classifier) :
    (∃ (domainCode : RawTerm scope) (body codomainCode : RawTerm (scope + 1)),
      subject = lamCell domainCode body ∧
      classifier = piTyCodeCell domainCode codomainCode ∧
      HasTypeUnion profile (context.cons domainCode) body codomainCode)
    ∨ (∃ (carrierCode : RawTerm scope) (body : RawTerm (scope + 1)),
      subject = pathLamCell body ∧
      classifier = bridgeTypeCell carrierCode
        (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell) ∧
      RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1) := by
  cases derivation with
  | genIntro generator rule typeParamA typeParamB body
      domainLevel codomainLevel flag isIntro binderGraded
      domainFormed classifierFormed bodyTyped =>
    by_cases hLam : generator = .gen_lam
    · subst hLam
      have hRule : rule = lamGradedIntroRule :=
        Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
      subst hRule
      exact Or.inl ⟨typeParamA, body, typeParamB, rfl, rfl, bodyTyped⟩
    · by_cases hPath : generator = .gen_pathLam
      · subst hPath
        have hRule : rule = pathLamGradedIntroRule :=
          Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
        subst hRule
        exact Or.inr ⟨typeParamA, body, rfl, rfl, binderGraded⟩
      · exfalso
        dsimp only [gradedIntroRuleOf] at isIntro
        rw [if_neg hLam, if_neg hPath] at isIntro
        contradiction

/-! ## Smokes: both rows non-vacuously inhabited through the engine -/

/-- **★ A closed λ through the engine's λ row.**  `λ(x:Type@0).Type@0 : Π(x:Type@0).Type@1` — the
`.omega` graded check read from the table and discharged on a real derivation. -/
theorem closedConstantLambdaGradedEngineTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescGradedIntro profile (TypingContext.empty : TypingContext profile 0)
      (lamCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)) :=
  gradedIntroEngine_typesLam
    (LevelExpr.lsucc LevelExpr.lzero) (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag
    isLockFreeContext_empty
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation
        (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
        (LevelExpr.lsucc LevelExpr.lzero) flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation
        (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
        LevelExpr.lzero flag))

/-- **★ The constant bridge through the engine's AFFINE row.**  `pathLam(Type@0) :
Bridge(Type@1, Type@0, Type@0)` — the `.one` graded check read from the table and discharged
(`0 ≤ 1`, the closed body) on a real derivation.  The graded-engine realization of the constant path
abstraction the retired `HasTypeDescBridge` engine carried as `constantBridgeTyped`. -/
theorem constantBridgeGradedEngineTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescGradedIntro profile (TypingContext.empty : TypingContext profile 0)
      (pathLamCell (universeCodeCell LevelExpr.lzero flag))
      (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag)) :=
  gradedIntroEngine_typesPathLam
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation
        (TypingContext.cons TypingContext.empty intervalTypeCell)
        LevelExpr.lzero flag))
    (Nat.zero_le 1)
    isLockFreeContext_empty

/-! ## ★ The grade is load-bearing: double dimension use is REJECTED

(The witness vector `doubleDimensionUseBody` + its occurrence lemma live with the rule table in
`FX1Poly.Typed.Engine.RuleTables.GradedIntroRule` — the live union inversion tests against the same
vector.) -/

/-- **★ THE AFFINE GRADE REJECTS: `pathLam(pair(var 0, var 0))` is untypable through the engine at
EVERY classifier.**  The first kernel theorem where a typing is refused purely by a usage grade read
from a table row: the pathLam row demands `.one` (occurrence ≤ 1), the body occurs twice, soundness
forces every pathLam-headed typing through that row, `2 ≤ 1` is absurd.  Routes through `soundness`
(free-index inversion) — never `cases` at the concrete subject (the banked propext trap). -/
theorem gradedIntroEngine_rejectsDoubleDimensionUse {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (classifier : RawTerm scope) :
    ¬ HasTypeDescGradedIntro profile context
        (pathLamCell (doubleDimensionUseBody scope)) classifier := by
  intro derivation
  rcases derivation.soundness with
    ⟨domainCode, body, codomainCode, subjectEq, _, _⟩ |
    ⟨carrierCode, body, subjectEq, _, bodyAffine⟩
  · -- λ-row case: head generator mismatch (gen_pathLam vs gen_lam).
    exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  · -- pathLam-row case: extract the body, then `2 ≤ 1` is absurd.
    have bodiesEqual : doubleDimensionUseBody scope = body := by injections
    rw [← bodiesEqual, doubleDimensionUseBody_occurrenceIsTwo] at bodyAffine
    exact absurd bodyAffine (Nat.not_succ_le_self 1)

/-! ## The coverage gate -/

/-- **The NATIVE-23 keystone coverage record.**  Each field is a distinct live property of the v2 graded
introduction substrate; an inhabitant certifies the keystone is exercised (both rows present with their
grades, both rows non-vacuously typed through the engine, and the affine grade genuinely REJECTS). -/
structure GradedIntroEngineCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- The λ row carries the unrestricted grade. -/
  lamRowCarriesOmega :
    (gradedIntroRuleOf Generator.gen_lam).map (·.binderUsage) = some UsageGrade.omega
  /-- The pathLam row carries the AFFINE grade (the first non-`.omega` row). -/
  pathLamRowCarriesAffine :
    (gradedIntroRuleOf Generator.gen_pathLam).map (·.binderUsage) = some UsageGrade.one
  /-- A closed λ types through the engine's λ row. -/
  closedLambdaTyped : HasTypeDescGradedIntro profile (TypingContext.empty : TypingContext profile 0)
    (lamCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
    (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag))
  /-- The constant bridge types through the engine's affine row. -/
  constantBridgeTyped : HasTypeDescGradedIntro profile (TypingContext.empty : TypingContext profile 0)
    (pathLamCell (universeCodeCell LevelExpr.lzero flag))
    (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
      (universeCodeCell LevelExpr.lzero flag)
      (universeCodeCell LevelExpr.lzero flag))
  /-- The affine grade REJECTS the dimension-duplicating body at every classifier. -/
  doubleUseRejected : ∀ classifier : RawTerm 0,
    ¬ HasTypeDescGradedIntro profile (TypingContext.empty : TypingContext profile 0)
        (pathLamCell (doubleDimensionUseBody 0)) classifier

/-- **★ The keystone coverage gate** — inhabited by the shipped witnesses, so the exercised property
set can NOT silently shrink. -/
theorem gradedIntroEngineCoverageWitness {profile : PolyProfile} (flag : UniverseFlag) :
    GradedIntroEngineCoverage profile flag where
  lamRowCarriesOmega := rfl
  pathLamRowCarriesAffine := rfl
  closedLambdaTyped := closedConstantLambdaGradedEngineTyped flag
  constantBridgeTyped := constantBridgeGradedEngineTyped flag
  doubleUseRejected := fun classifier => gradedIntroEngine_rejectsDoubleDimensionUse classifier

end FX1Poly.Typed
