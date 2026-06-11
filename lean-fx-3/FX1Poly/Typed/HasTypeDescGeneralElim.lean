import FX1Poly.Typed.HasTypeDescGradedIntro
import FX1Poly.Typed.ElimRuleDesc
import FX1Poly.Typed.BridgeEndpointGeneralArgumentSubjectReduction

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
    Pi-typed at its bridge type) — the canonical-path (pathLam-headed) regime is where endpoint-ι
    FIRES instead (below).  Full bespoke-`pathElim` adequacy is NATIVE-25 (the Bridge premises live in
    the Bridge judgment — the same judgment-boundary the NATIVE-04 residual pinned; it dissolves at the
    unified engine).
  * `HasTypeDescGeneralElim.soundness` — every generic typing is a `piElim`-built Pi derivation (app
    row) or a neutral bridge elimination with surfaced Pi premises (pathApp row), same subject and
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

/-- **The v2 elimination-rule description.**  Everything the generic elimination arm needs, as rule
DATA: the eliminated child's FORMER (`eliminatedType` — Π code for app, bridge code for pathApp), the
argument's type, the member shape, and the argument-dependent output.  Four type-parameters cover the
current former arities: `typeParamA : RawTerm scope` (app: the domain; pathApp: the carrier),
`typeParamB : RawTerm (scope+1)` (app: the codomain; pathApp: unused), `typeParamC typeParamD :
RawTerm scope` (pathApp: the bridge endpoints; app: unused).  Pure syntax — strictly positive. -/
structure GeneralElimRule where
  /-- The eliminated child's type (the FORMER being eliminated).  app: `piTyCodeCell paramA paramB`.
  pathApp: `bridgeTypeCell paramA paramC paramD`. -/
  eliminatedType : (scope : Nat) → RawTerm scope → RawTerm (scope + 1) →
    RawTerm scope → RawTerm scope → RawTerm scope
  /-- The argument's type.  app: the domain parameter.  pathApp: PINNED `intervalTypeCell`. -/
  argumentType : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The elimination member's shape — rule data.  app: `appCell`.  pathApp: `pathAppCell`. -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope
  /-- The output — ARGUMENT-dependent (the §11.8.5 children-dependent seam).  app: `subst0 paramB
  argument` (the dependent application type).  pathApp: `paramA` (the carrier — the constant family,
  the non-dependent degenerate case). -/
  outputType : (scope : Nat) → RawTerm scope → RawTerm (scope + 1) → RawTerm scope → RawTerm scope

/-- The app row: eliminated at the Π code, argument at the domain, member `appCell`, dependent
`subst0` output — exactly `HasTypeDescPi.piElim`. -/
def appGeneralElimRule : GeneralElimRule where
  eliminatedType := fun _ domainCode codomainCode _ _ => piTyCodeCell domainCode codomainCode
  argumentType := fun _ domainCode => domainCode
  memberCell := fun _ functionTerm argument => appCell functionTerm argument
  outputType := fun _ _ codomainCode argument => RawTerm.subst0 codomainCode argument

/-- The pathApp row: eliminated at the bridge code, argument PINNED to the interval, member
`pathAppCell`, CONSTANT output (the carrier) — exactly `HasTypeDescBridge.pathElim`'s conclusion
shape. -/
def pathAppGeneralElimRule : GeneralElimRule where
  eliminatedType := fun _ carrierCode _ leftEndpoint rightEndpoint =>
    bridgeTypeCell carrierCode leftEndpoint rightEndpoint
  argumentType := fun _ _ => intervalTypeCell
  memberCell := fun _ path argument => pathAppCell path argument
  outputType := fun _ carrierCode _ _ => carrierCode

/-- **The v2 elimination table.**  Two rows: the dependent app and the non-dependent pathApp.  A new
eliminator (the data-eliminator family, NATIVE-28/32) is one more row here — never a new arm. -/
def generalElimRuleOf (generator : Generator) : Option GeneralElimRule :=
  if generator = .gen_app then some appGeneralElimRule
  else if generator = .gen_pathApp then some pathAppGeneralElimRule
  else none

/-! ## Table metadata (cascade-death lemmas) -/

/-- `gen_app`'s v2 row is the dependent application rule. -/
theorem generalElimRuleOf_app :
    generalElimRuleOf .gen_app = some appGeneralElimRule := rfl

/-- `gen_pathApp`'s v2 row is the non-dependent bridge elimination rule. -/
theorem generalElimRuleOf_pathApp :
    generalElimRuleOf .gen_pathApp = some pathAppGeneralElimRule := rfl

/-- **The current v2 elimination table is exactly `{gen_app, gen_pathApp}`.**  The enumeration lemma
every dispatch consumer routes through. -/
theorem generalElimRuleOf_isAppOrPathApp {generator : Generator} {rule : GeneralElimRule}
    (isElim : generalElimRuleOf generator = some rule) :
    generator = Generator.gen_app ∨ generator = Generator.gen_pathApp := by
  by_cases hApp : generator = .gen_app
  · exact Or.inl hApp
  · by_cases hPath : generator = .gen_pathApp
    · exact Or.inr hPath
    · exfalso
      dsimp only [generalElimRuleOf] at isElim
      rw [if_neg hApp, if_neg hPath] at isElim
      contradiction

/-! ## The single-arm general elimination engine -/

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
      (eliminatedTyped : HasTypeDescPi profile context eliminated
        (rule.eliminatedType scope typeParamA typeParamB typeParamC typeParamD))
      (argumentTyped : HasTypeDescPi profile context argument
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
    (argumentTyped : HasTypeDescPi profile context argument domainCode) :
    HasTypeDescGeneralElim profile context (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument) :=
  HasTypeDescGeneralElim.genElim context .gen_app appGeneralElimRule
    domainCode codomainCode domainCode domainCode functionTerm argument rfl
    functionTyped argumentTyped

/-- **A Pi-typed (neutral) path drives the generic arm at the pathApp row.**  A path typed at a bridge
code in the HOST judgment (the variable / neutral regime — e.g. a context-bound path variable) applied
to a grown-typed interval argument types at the CARRIER (the constant output).  The canonical
(pathLam-headed) regime is where endpoint-ι fires instead (`gradedIntroEndpointIotaComputesTyped`). -/
theorem generalElimEngine_typesPathApp {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {path argument carrierCode leftEndpoint rightEndpoint : RawTerm scope}
    (pathTyped : HasTypeDescPi profile context path
      (bridgeTypeCell carrierCode leftEndpoint rightEndpoint))
    (argumentTyped : HasTypeDescPi profile context argument intervalTypeCell) :
    HasTypeDescGeneralElim profile context (pathAppCell path argument) carrierCode :=
  HasTypeDescGeneralElim.genElim context .gen_pathApp pathAppGeneralElimRule
    carrierCode (RawTerm.weaken carrierCode) leftEndpoint rightEndpoint path argument rfl
    pathTyped argumentTyped

/-! ## ★ Soundness: every generic typing surfaces its bespoke content -/

/-- **★ Per-row soundness.**  Every `HasTypeDescGeneralElim` typing is EITHER an application with a
`HasTypeDescPi.piElim`-built derivation at the SAME subject and classifier (exact app-row adequacy),
OR a bridge elimination with the Pi-typed path and interval-argument premises SURFACED (the
neutral-path regime; bespoke `pathElim` adequacy is NATIVE-25's union-judgment work — its premises
live in the Bridge judgment, the pinned judgment-boundary).  `cases` at FREE indices + table
enumeration. -/
theorem HasTypeDescGeneralElim.soundness {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescGeneralElim profile context subject classifier) :
    (∃ (functionTerm argument : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
      subject = appCell functionTerm argument ∧
      classifier = RawTerm.subst0 codomainCode argument ∧
      HasTypeDescPi profile context (appCell functionTerm argument)
        (RawTerm.subst0 codomainCode argument))
    ∨ (∃ (path argument carrierCode leftEndpoint rightEndpoint : RawTerm scope),
      subject = pathAppCell path argument ∧
      classifier = carrierCode ∧
      HasTypeDescPi profile context path
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) ∧
      HasTypeDescPi profile context argument intervalTypeCell) := by
  cases derivation with
  | genElim generator rule typeParamA typeParamB typeParamC typeParamD
      eliminated argument isElim eliminatedTyped argumentTyped =>
    by_cases hApp : generator = .gen_app
    · subst hApp
      have hRule : rule = appGeneralElimRule :=
        Option.some.inj (isElim.symm.trans generalElimRuleOf_app)
      subst hRule
      exact Or.inl ⟨eliminated, argument, typeParamB, rfl, rfl,
        HasTypeDescPi.piElim eliminatedTyped argumentTyped⟩
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
      HasTypeDescPi profile (context.cons (rule.domainCell scope typeParamA)) body
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
    (argumentTyped : HasTypeDescPi profile context argument intervalTypeCell) :
    ∃ carrierCode : RawTerm scope,
      classifier = bridgeTypeCell carrierCode
        (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell) ∧
      StepBridgeEndpoint (pathAppCell (pathLamCell body) argument)
        (RawTerm.subst0 body argument) ∧
      HasTypeDescPi profile context (RawTerm.subst0 body argument) carrierCode := by
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
    obtain ⟨stepFires, reductTyped⟩ :=
      endpointBetaGeneralArgumentGrownReduct bodyTyped argumentTyped
    exact ⟨typeParamA, classifierEq, stepFires, reductTyped⟩

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

/-- **★ The typed endpoint-ι exercised on the constant bridge.**  The keystone-typed
`pathLam(Type@0)` (at the dimension-variable context) applied to the dimension variable: the ι
theorem extracts the carrier `Type@1`, fires the step, and grows the reduct — non-vacuous end-to-end
through BOTH v2 engines. -/
theorem constantBridgeEndpointIotaSmoke {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ carrierCode : RawTerm 1,
      StepBridgeEndpoint
        (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag))
          (variableCell ⟨0, Nat.succ_pos 0⟩))
        (RawTerm.subst0 (universeCodeCell LevelExpr.lzero flag)
          (variableCell ⟨0, Nat.succ_pos 0⟩)) ∧
      HasTypeDescPi profile
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
        (Nat.zero_le 1))
      (show HasTypeDescPi profile
          (TypingContext.empty.cons intervalTypeCell : TypingContext profile 1)
          (variableCell ⟨0, Nat.succ_pos 0⟩) intervalTypeCell from
        HasTypeDescPi.ofFormation
          (HasTypeDesc.var (TypingContext.empty.cons intervalTypeCell)
            ⟨0, Nat.succ_pos 0⟩))
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
    StepBridgeEndpoint
      (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag))
        (variableCell ⟨0, Nat.succ_pos 0⟩))
      (RawTerm.subst0 (universeCodeCell LevelExpr.lzero flag)
        (variableCell ⟨0, Nat.succ_pos 0⟩)) ∧
    HasTypeDescPi profile
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
