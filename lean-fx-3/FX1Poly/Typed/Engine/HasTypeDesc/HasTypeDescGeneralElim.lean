import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescGradedIntro
import FX1Poly.Typed.Engine.RuleTables.ElimRuleDesc
import FX1Poly.Typed.Engine.RuleTables.GeneralElimRule
import FX1Poly.Typed.Metatheory.SubjectReduction.BridgeEndpointGeneralArgumentSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionUnionSubstituent

/-! # FX1Poly/Typed/HasTypeDescGeneralElim — NATIVE-24: pathApp as a native elim row + endpoint-ι typed

The elimination twin of the NATIVE-23 intro keystone.  The v1 `ElimRuleDesc` has the SAME schema gaps
for `pathApp` that the v1 `IntroRuleDesc` had for `pathLam`: the member shape is hardwired
(`appCell` vs `pathAppCell`), and the eliminated FORMER is hardwired in the dispatcher's premise
(`piTyCodeCell domain codomain` vs `bridgeTypeCell carrier left right` — a 2-child former vs a
3-child former).  Only the output half generalizes for free (pathApp is NON-dependent: the output is
the carrier, a constant family — the degenerate case of the dependent `subst0` output).

  * `GeneralElimRule` — the v2 schema: `eliminatedType` (the eliminated former, rule data over four
    type-parameters), `argumentType`, `memberCell` (rule-data member shape), argument-dependent
    `outputType`.
  * `generalElimRuleOf` — the two-row table: `gen_app` (dependent output `subst0 codomain argument`)
    and `gen_pathApp` (constant output = the carrier).
  * `HasTypeDescGeneralElim` — ONE generic arm: eliminated child typed at the rule's former, argument
    typed at the rule's argument type, member typed at the rule's output.  Premises in `HasTypeDescPi`
    (the host judgment of variables and neutral terms): the app row has EXACT premise parity with
    `HasTypeDescPi.piElim`; the pathApp row covers the NEUTRAL-path regime (a path VARIABLE is
    Pi-typed at its bridge-code type) — the canonical-path (pathLam-headed) regime is where endpoint-ι
    FIRES instead (below).  Full path-elimination adequacy with the path/argument premises in the SAME
    judgment is the native union `HasTypeUnion`'s `generalElim` smart constructor (over the uniform
    `elim` arm, recursive premises in the union itself) — the judgment boundary the bespoke
    (now-retired, NATIVE-45) engine could not cross dissolves there.
  * `HasTypeDescGeneralElim.soundness` — every generic typing is a `piElim`-built Pi derivation (app
    row) or a neutral path elimination with surfaced Pi premises (pathApp row), same subject and
    classifier.
  * `HasTypeDescGradedIntro.invertGeneric` — the keystone engine's free-index premise-surfacing
    inversion (the brick the ι theorem consumes).
  * ★ `gradedIntroEndpointIotaComputesTyped` — ENDPOINT-ι AT THE TYPED LEVEL, v2-keyed: a
    `HasTypeDescGradedIntro`-typed `pathLam body` applied to a grown-typed interval argument FIRES
    endpoint-β and the reduct `body[argument]` is GROWN-typed at the carrier extracted from the
    keystone classifier.  The composition (keystone inversion) ∘ (NATIVE-09's
    `endpointBetaGeneralArgumentGrownReduct`) — the GTL-18 ι-computation analogue for the v2 tables.

## Zero-axiom

The table is pure syntax; the engine arm mirrors the keystone; soundness is `cases` at free indices +
table enumeration; the ι theorem routes through `invertGeneric` (free-index inversion — never `cases`
at the concrete subject, the banked propext trap) + head-generator no-confusion + `injections` +
NATIVE-09.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## The single-arm general elimination engine

The v2 elimination-rule table (`GeneralElimRule`, `appGeneralElimRule`, `pathAppGeneralElimRule`,
`generalElimRuleOf`, and its metadata lemmas) is the live rule-data now homed in
`FX1Poly.Typed.Engine.RuleTables.GeneralElimRule`; this module keeps only the (deprecated)
description-driven elimination JUDGMENT that consumes it. -/

/-- **The description-driven elimination judgment (the NATIVE-24 core).**  ONE generic `genElim` arm:
given a v2 table row, an eliminated child typed at the rule's FORMER and an argument typed at the
rule's argument type (both in `HasTypeDescPi`, the host judgment of variables and neutral terms), the
rule's member cell inhabits the rule's argument-dependent output. -/
inductive HasTypeDescGeneralElim (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | genElim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : GeneralElimRule)
      (typeParamA : RawTerm scope) (typeParamB : RawTerm (scope + 1))
      (typeParamC typeParamD : RawTerm scope)
      (eliminated argument : RawTerm scope)
      (isElim : generalElimRuleOf generator = some rule)
      (eliminatedTyped : HasTypeUnion profile context eliminated
        (rule.eliminatedType scope typeParamA typeParamB typeParamC typeParamD))
      (argumentTyped : HasTypeUnion profile context argument
        (rule.argumentType scope typeParamA)) :
      HasTypeDescGeneralElim profile context
        (rule.memberCell scope eliminated argument)
        (rule.outputType scope typeParamA typeParamB argument)

/-! ## Reconstruction: the bespoke premises drive the generic arm -/

/-- **The `piElim` premises drive the generic arm at the app row.**  Same subject (`appCell`), same
dependent classifier (`subst0 codomain argument`) as `HasTypeDescPi.piElim` — exact premise parity. -/
theorem generalElimEngine_typesApp {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionTyped :
      HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode)
    (contextLockFree : context.isLockFreeContext = true) :
    HasTypeDescGeneralElim profile context (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument) :=
  HasTypeDescGeneralElim.genElim context .gen_app appGeneralElimRule
    domainCode codomainCode domainCode domainCode functionTerm argument rfl
    (functionTyped.ofGrownReflected contextLockFree)
    (argumentTyped.ofGrownReflected contextLockFree)

/-- **A Pi-typed (neutral) path drives the generic arm at the pathApp row.**  A path typed at a bridge
code in the HOST judgment (the variable / neutral regime — e.g. a context-bound path variable) applied
to a grown-typed interval argument types at the CARRIER (the constant output).  The canonical
(pathLam-headed) regime is where endpoint-ι fires instead (`gradedIntroEndpointIotaComputesTyped`). -/
theorem generalElimEngine_typesPathApp {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {path argument carrierCode leftEndpoint rightEndpoint : RawTerm scope}
    (pathTyped : HasTypeDescPi profile context path
      (bridgeTypeCell carrierCode leftEndpoint rightEndpoint))
    (argumentTyped : HasTypeDescPi profile context argument intervalTypeCell)
    (contextLockFree : context.isLockFreeContext = true) :
    HasTypeDescGeneralElim profile context (pathAppCell path argument) carrierCode :=
  HasTypeDescGeneralElim.genElim context .gen_pathApp pathAppGeneralElimRule
    carrierCode (RawTerm.weaken carrierCode) leftEndpoint rightEndpoint path argument rfl
    (pathTyped.ofGrownReflected contextLockFree)
    (argumentTyped.ofGrownReflected contextLockFree)

/-! ## ★ Soundness: every generic typing surfaces its bespoke content -/

/-- **★ Per-row soundness.**  Every `HasTypeDescGeneralElim` typing is EITHER an application with a
`HasTypeDescPi.piElim`-built derivation at the SAME subject and classifier (exact app-row adequacy),
OR a path elimination with the Pi-typed path and interval-argument premises SURFACED (the
neutral-path regime; full path-elimination adequacy with the path premise in the SAME judgment is the
native union's `generalElim` arm, where the recursive premises live in the union itself).  `cases` at
FREE indices + table enumeration. -/
theorem HasTypeDescGeneralElim.soundness {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescGeneralElim profile context subject classifier) :
    (∃ (functionTerm argument domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
      subject = appCell functionTerm argument ∧
      classifier = RawTerm.subst0 codomainCode argument ∧
      HasTypeUnion profile context functionTerm (piTyCodeCell domainCode codomainCode) ∧
      HasTypeUnion profile context argument domainCode)
    ∨ (∃ (path argument carrierCode leftEndpoint rightEndpoint : RawTerm scope),
      subject = pathAppCell path argument ∧
      classifier = carrierCode ∧
      HasTypeUnion profile context path
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) ∧
      HasTypeUnion profile context argument intervalTypeCell) := by
  cases derivation with
  | genElim generator rule typeParamA typeParamB typeParamC typeParamD
      eliminated argument isElim eliminatedTyped argumentTyped =>
    by_cases hApp : generator = .gen_app
    · subst hApp
      have hRule : rule = appGeneralElimRule :=
        Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
      subst hRule
      exact Or.inl ⟨eliminated, argument, typeParamA, typeParamB, rfl, rfl,
        eliminatedTyped, argumentTyped⟩
    · by_cases hPath : generator = .gen_pathApp
      · subst hPath
        have hRule : rule = pathAppGeneralElimRule :=
          Option.some.inj (isElim.symm.trans generalElimRuleOf_pathApp)
        subst hRule
        exact Or.inr ⟨eliminated, argument, typeParamA, typeParamC, typeParamD, rfl, rfl,
          eliminatedTyped, argumentTyped⟩
      · exfalso
        dsimp only [generalElimRuleOf] at isElim
        rw [if_neg hApp, if_neg hPath] at isElim
        contradiction

/-! ## The keystone engine's premise-surfacing inversion -/

/-- **The free-index premise-surfacing inversion for the graded intro engine.**  Surfaces the single
arm's raw fields (the table row, the parameters, the graded check, the body premise) without
repackaging into bespoke derivations — the brick the typed endpoint-ι consumes (and the safe route:
`cases` at FREE indices only; a consumer at a concrete subject applies THIS then discriminates by
head, avoiding the equation-motive propext trap). -/
theorem HasTypeDescGradedIntro.invertGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescGradedIntro profile context subject classifier) :
    ∃ (generator : Generator) (rule : GradedIntroRule) (typeParamA : RawTerm scope)
      (typeParamB body : RawTerm (scope + 1)),
      gradedIntroRuleOf generator = some rule ∧
      subject = rule.memberCell scope typeParamA body ∧
      classifier = rule.outputType scope typeParamA typeParamB body ∧
      gradedBinderChecks rule.binderUsage body ∧
      HasTypeUnion profile (context.cons (rule.domainCell scope typeParamA)) body
        (rule.bodyClassifier scope typeParamA typeParamB) := by
  cases derivation with
  | genIntro generator rule typeParamA typeParamB body
      domainLevel codomainLevel flag isIntro binderGraded
      domainFormed classifierFormed bodyTyped =>
    exact ⟨generator, rule, typeParamA, typeParamB, body, isIntro, rfl, rfl,
      binderGraded, bodyTyped⟩

/-! ## ★ Endpoint-ι at the typed level (the GTL-18 analogue for the v2 tables) -/

/-- **★ The typed endpoint-ι computation, v2-keyed.**  A `HasTypeDescGradedIntro`-typed path
abstraction applied to a GROWN-typed interval argument: the keystone classifier is forced to the
bridge code at the body's endpoint substitutions, the endpoint-β step FIRES, and the reduct
`body[argument]` is GROWN-typed at the extracted CARRIER — exactly the pathApp row's output for that
carrier.  The composition (keystone `invertGeneric` + table enumeration) ∘ (NATIVE-09's
`endpointBetaGeneralArgumentGrownReduct`): the v2 intro engine's typing premise drives the v2 elim
row's computation rule. -/
theorem gradedIntroEndpointIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {classifier argument : RawTerm scope}
    (pathTyped : HasTypeDescGradedIntro profile context (pathLamCell body) classifier)
    (argumentTyped : HasTypeDescPi profile context argument intervalTypeCell)
    (contextLockFree : context.isLockFreeContext = true) :
    ∃ carrierCode : RawTerm scope,
      classifier = bridgeTypeCell carrierCode
        (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell) ∧
      StepTable (pathAppCell (pathLamCell body) argument)
        (RawTerm.subst0 body argument) ∧
      HasTypeUnion profile context (RawTerm.subst0 body argument) carrierCode := by
  obtain ⟨generator, rule, typeParamA, typeParamB, armBody, isIntro, subjectEq,
    classifierEq, _, bodyTyped⟩ := pathTyped.invertGeneric
  rcases gradedIntroRuleOf_isLamOrPathLam isIntro with hLam | hPath
  · subst hLam
    have hRule : rule = lamGradedIntroRule :=
      Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_lam)
    subst hRule
    -- `pathLamCell body = lamCell typeParamA armBody` — head-generator clash.
    exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  · subst hPath
    have hRule : rule = pathLamGradedIntroRule :=
      Option.some.inj (isIntro.symm.trans gradedIntroRuleOf_pathLam)
    subst hRule
    have bodiesEqual : body = armBody := by injections
    subst bodiesEqual
    -- The surfaced body premise is NATIVE (`context.cons intervalTypeCell ⊢ body : weaken carrier`); the
    -- grown argument reflects to the native kernel judgment, then the plain-`cons` native single
    -- substitution (`subst0WithUnionImage`, fibrant-usable over the lock-free context) types the reduct at
    -- `subst0 (weaken carrier) argument`, which `subst0_weaken` collapses to the carrier.
    have argumentNative : HasTypeUnion profile context argument intervalTypeCell :=
      argumentTyped.ofGrownReflected contextLockFree
    have argumentUsable : context.isSubjectUsableAtModality argument .fibrant = true :=
      context.lockFreeImpliesSubjectFibrantlyUsable contextLockFree argument
    have reductTyped :=
      HasTypeUnion.subst0WithUnionImage argument bodyTyped argumentNative argumentUsable
    dsimp only [pathLamGradedIntroRule] at reductTyped
    rw [RawTerm.subst0_weaken] at reductTyped
    exact ⟨typeParamA, classifierEq, StepTable.pathBetaFires body argument, reductTyped⟩

/-! ## Smokes: both rows + the ι non-vacuously exercised -/

/-- **★ A closed application through the engine's app row.**  `(λ(x:Type@1).Type@0)(Type@0) :
Type@1` — the dependent output `subst0` collapses on the constant codomain. -/
theorem closedApplicationGeneralElimTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescGeneralElim profile (TypingContext.empty : TypingContext profile 0)
      (appCell
        (lamCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  generalElimEngine_typesApp
    (HasTypeDescPi.piIntro (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero))
      (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation TypingContext.empty
          (LevelExpr.lsucc LevelExpr.lzero) flag))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation
          (TypingContext.empty.cons
            (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag))
          (LevelExpr.lsucc LevelExpr.lzero) flag))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation
          (TypingContext.empty.cons
            (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag))
          LevelExpr.lzero flag)))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    isLockFreeContext_empty

/-- **★ A NEUTRAL path elimination through the engine's pathApp row.**  In a context binding a bridge
variable and a dimension variable, `pathApp(var 1, var 0) : Type@1` — the path is the context-bound
variable (Pi-typed via lookup), the argument is the dimension variable, the output is the carrier.
The neutral regime the pathApp row exists for. -/
theorem neutralPathApplicationGeneralElimTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescGeneralElim profile
      ((TypingContext.empty.cons
        (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
          (universeCodeCell LevelExpr.lzero flag)
          (universeCodeCell LevelExpr.lzero flag))).cons intervalTypeCell
        : TypingContext profile 2)
      (pathAppCell (variableCell ⟨1, Nat.lt_succ_self 1⟩)
        (variableCell ⟨0, Nat.succ_pos 1⟩))
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  generalElimEngine_typesPathApp
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var
        ((TypingContext.empty.cons
          (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
            (universeCodeCell LevelExpr.lzero flag)
            (universeCodeCell LevelExpr.lzero flag))).cons intervalTypeCell)
        ⟨1, Nat.lt_succ_self 1⟩))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var
        ((TypingContext.empty.cons
          (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
            (universeCodeCell LevelExpr.lzero flag)
            (universeCodeCell LevelExpr.lzero flag))).cons intervalTypeCell)
        ⟨0, Nat.succ_pos 1⟩))
    rfl

/-- **★ The typed endpoint-ι exercised on the constant bridge.**  The keystone-typed
`pathLam(Type@0)` (at the dimension-variable context) applied to the dimension variable: the ι
theorem extracts the carrier `Type@1`, fires the step, and grows the reduct — non-vacuous end-to-end
through BOTH v2 engines. -/
theorem constantBridgeEndpointIotaSmoke {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ carrierCode : RawTerm 1,
      StepTable
        (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag))
          (variableCell ⟨0, Nat.succ_pos 0⟩))
        (RawTerm.subst0 (universeCodeCell LevelExpr.lzero flag)
          (variableCell ⟨0, Nat.succ_pos 0⟩)) ∧
      HasTypeUnion profile
        (TypingContext.empty.cons intervalTypeCell : TypingContext profile 1)
        (RawTerm.subst0 (universeCodeCell LevelExpr.lzero flag)
          (variableCell ⟨0, Nat.succ_pos 0⟩)) carrierCode := by
  obtain ⟨carrierCode, _, stepFires, reductTyped⟩ :=
    gradedIntroEndpointIotaComputesTyped
      (gradedIntroEngine_typesPathLam
        (carrierCode := universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation
            ((TypingContext.empty.cons intervalTypeCell).cons intervalTypeCell)
            LevelExpr.lzero flag))
        (Nat.zero_le 1)
        rfl)
      (show HasTypeDescPi profile
          (TypingContext.empty.cons intervalTypeCell : TypingContext profile 1)
          (variableCell ⟨0, Nat.succ_pos 0⟩) intervalTypeCell from
        HasTypeDescPi.ofFormation
          (HasTypeDesc.var (TypingContext.empty.cons intervalTypeCell)
            ⟨0, Nat.succ_pos 0⟩))
      rfl
  exact ⟨carrierCode, stepFires, reductTyped⟩

/-! ## The coverage gate -/

/-- **The NATIVE-24 coverage record.**  Each field is a distinct live property of the v2 elimination
substrate; an inhabitant certifies the elim keystone is exercised (both rows present, both rows
non-vacuously typed through the engine, the ι fires typed end-to-end through both v2 engines). -/
structure GeneralElimEngineCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- The table carries both rows. -/
  tableCarriesBothRows :
    (generalElimRuleOf Generator.gen_app).isSome = true ∧
    (generalElimRuleOf Generator.gen_pathApp).isSome = true
  /-- A closed application types through the app row. -/
  closedApplicationTyped : HasTypeDescGeneralElim profile
    (TypingContext.empty : TypingContext profile 0)
    (appCell
      (lamCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell LevelExpr.lzero flag))
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
  /-- A neutral path elimination types through the pathApp row. -/
  neutralPathApplicationTyped : HasTypeDescGeneralElim profile
    ((TypingContext.empty.cons
      (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag))).cons intervalTypeCell
      : TypingContext profile 2)
    (pathAppCell (variableCell ⟨1, Nat.lt_succ_self 1⟩)
      (variableCell ⟨0, Nat.succ_pos 1⟩))
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
  /-- The typed endpoint-ι fires end-to-end through both v2 engines. -/
  endpointIotaFiresTyped : ∃ carrierCode : RawTerm 1,
    StepTable
      (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag))
        (variableCell ⟨0, Nat.succ_pos 0⟩))
      (RawTerm.subst0 (universeCodeCell LevelExpr.lzero flag)
        (variableCell ⟨0, Nat.succ_pos 0⟩)) ∧
    HasTypeUnion profile
      (TypingContext.empty.cons intervalTypeCell : TypingContext profile 1)
      (RawTerm.subst0 (universeCodeCell LevelExpr.lzero flag)
        (variableCell ⟨0, Nat.succ_pos 0⟩)) carrierCode

/-- **★ The NATIVE-24 coverage gate** — inhabited by the shipped witnesses, so the exercised property
set can NOT silently shrink. -/
theorem generalElimEngineCoverageWitness {profile : PolyProfile} (flag : UniverseFlag) :
    GeneralElimEngineCoverage profile flag where
  tableCarriesBothRows := ⟨rfl, rfl⟩
  closedApplicationTyped := closedApplicationGeneralElimTyped flag
  neutralPathApplicationTyped := neutralPathApplicationGeneralElimTyped flag
  endpointIotaFiresTyped := constantBridgeEndpointIotaSmoke flag

end FX1Poly.Typed
