import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.RawTermFreeVars
import FX1Poly.Core.ReducibilityCandidateArrow

/-! # FX1Poly/Typed/HasTypeDescBridge — the GRADED bridge-type rows (OP1-INT brick 2)

The standalone internal-parametricity typing engine over the landed `gen_intervalCode` /
`gen_bridgeCode` substrate, realizing the typing-row design recorded in
`KernelParamSubstrateSurvey`.  Same cascade-free pattern as the DI family
(`HasTypeDescIdIntro` etc.): a brand-new standalone judgment, NOT mutual with / NOT an arm
of any existing engine.

## THE GRADED ROW — type and usage dimensions jointly load-bearing

The `pathIntro` arm is the first kernel rule where TWO FX dimensions are simultaneously
REQUIRED for one premise set:

  * the TYPE premise: the body is typed under the interval-extended context
    (`context.cons intervalTypeCell ⊢ body : weaken typeCode`), and
  * the USAGE premise: the dimension binder is AFFINE — the body uses variable `0` at most
    once (`RawTerm.occurrenceCountAt body 0 ≤ 1`, the BCM bridge-dimension discipline;
    duplicating the dimension variable collapses internal parametricity).

The affinity is the kernel realization of the usage semiring's affine grade (the survey's
design decision): `TypingContext` is structural, so the grade lives as a CHECKED syntactic
occurrence bound, the quantitative refinement of `RawTerm.UsesPosition`.

## The rules (per the survey schemas)

      intervalFormation   ⊢ dim : Type@0
      intervalZero/One    ⊢ 0, 1 : dim
      bridgeFormation     A : Type@e → a : A → b : A → Bridge A a b : Type@e
      pathIntro           Γ, i:⟨affine⟩dim ⊢ body : A  →  count_i body ≤ 1
                          → pathLam body : Bridge A body[i:=0] body[i:=1]
      pathElim            p : Bridge A a b → ε : dim → pathApp p ε : A

## HONEST SCOPE

Rows + the endpoint-β computation: the rule `pathApp (pathLam body) ε ↝ body[i:=ε]` ships as
the GATED SIBLING `StepBridgeEndpoint` (`BridgeEndpointStep.lean`, the η-discipline — NOT a
core `Step` arm; promotion is the recorded future event), with the deterministic inversion
stack and two non-vacuous SR fragments there.  GENERAL SR for this engine awaits engine
integration (see `intervalZeroGrownUntypable` — the cross-engine wall); the definitional
endpoint boundary (`pathApp p 0 ≡ a`) remains open.  The rows passed the ONORM-M2 sconing
admission gate (the live flip) — the remaining OP1-INT verdict half is the affine-dimension
glued-model statement over `pathIntro`.

## Zero-axiom

A positive recursive inductive; smokes are direct arm applications (the affine premise on a
closed constant body computes to `0 ≤ 1` by `rfl` + `Nat.zero_le`); inversions are free-index
`cases` with `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

-- `intervalTypeCell` (the interval/dimension type code `Interval`, `gen_intervalCode` nullary)
-- now lives in `CellConstructors` beside `boolTypeCell` / `unitTypeCell` (NATIVE-07 consolidation —
-- the cell is shared by this bridge engine and the union's `dataIntroNullary` endpoint rows); reached here
-- transitively via the `HasTypeDescPi → … → CellConstructors` import.

/-- The left interval endpoint `0 : dim` (`gen_interval0`, nullary). -/
def intervalZeroCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_interval0 () .childNil

/-- The right interval endpoint `1 : dim` (`gen_interval1`, nullary). -/
def intervalOneCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_interval1 () .childNil

/-- The bridge type code `Bridge(typeCode, left, right)` — `gen_bridgeCode` (arity 3,
`binderShifts = [0, 0, 0]`, the `gen_idCode` template): a carrier type and two endpoint
terms. -/
def bridgeTypeCell {scope : Nat} (typeCode left right : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_bridgeCode ()
    (.childCons typeCode (.childCons left (.childCons right .childNil)))

/-- The bridge abstraction `pathLam(body)` — `gen_pathLam` (arity 1,
`binderShifts = [1]`): the body lives under ONE fresh dimension binder. -/
def pathLamCell {scope : Nat} (body : RawTerm (scope + 1)) : RawTerm scope :=
  .mkGen .gen_pathLam () (.childCons body .childNil)

/-- The bridge application `pathApp(path, argument)` — `gen_pathApp` (arity 2,
`binderShifts = [0, 0]`). -/
def pathAppCell {scope : Nat} (path argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_pathApp () (.childCons path (.childCons argument .childNil))

/-- **The graded bridge-type judgment.**  Interval formation + endpoints, bridge formation,
the GRADED `pathIntro` (type premise × affine usage premise), and `pathElim`.  Recursive (the
elim's path and argument premises are this judgment), standalone (cascade-free). -/
inductive HasTypeDescBridge (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | intervalFormation {scope : Nat} (context : TypingContext profile scope)
      (flag : UniverseFlag) :
      HasTypeDescBridge profile context intervalTypeCell
        (universeCodeCell LevelExpr.lzero flag)
  | intervalZero {scope : Nat} (context : TypingContext profile scope) :
      HasTypeDescBridge profile context intervalZeroCell intervalTypeCell
  | intervalOne {scope : Nat} (context : TypingContext profile scope) :
      HasTypeDescBridge profile context intervalOneCell intervalTypeCell
  | bridgeFormation {scope : Nat} (context : TypingContext profile scope)
      (typeCode leftEndpoint rightEndpoint : RawTerm scope)
      (level : LevelExpr) (flag : UniverseFlag)
      (typeCodeTyped : HasTypeDescPi profile context typeCode
        (universeCodeCell level flag))
      (leftTyped : HasTypeDescPi profile context leftEndpoint typeCode)
      (rightTyped : HasTypeDescPi profile context rightEndpoint typeCode) :
      HasTypeDescBridge profile context
        (bridgeTypeCell typeCode leftEndpoint rightEndpoint)
        (universeCodeCell level flag)
  | pathIntro {scope : Nat} (context : TypingContext profile scope)
      (body : RawTerm (scope + 1)) (typeCode : RawTerm scope)
      (bodyTyped : HasTypeDescPi profile (context.cons intervalTypeCell) body
        (RawTerm.weaken typeCode))
      (dimensionAffine :
        RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1) :
      HasTypeDescBridge profile context (pathLamCell body)
        (bridgeTypeCell typeCode
          (RawTerm.subst0 body intervalZeroCell)
          (RawTerm.subst0 body intervalOneCell))
  | pathElim {scope : Nat} (context : TypingContext profile scope)
      (path argument typeCode leftEndpoint rightEndpoint : RawTerm scope)
      (pathTyped : HasTypeDescBridge profile context path
        (bridgeTypeCell typeCode leftEndpoint rightEndpoint))
      (argumentTyped : HasTypeDescBridge profile context argument intervalTypeCell) :
      HasTypeDescBridge profile context (pathAppCell path argument) typeCode

/-- **★ The first typed bridge type.**  `Bridge(Type@1, Type@0, Type@0) : Type@2` — bridge
formation at concrete universe codes (carrier `Type@1 : Type@2`, both endpoints
`Type@0 : Type@1`... at the carrier `Type@1`). -/
theorem HasTypeDescBridge.bridgeOfUniverseCodesTyped {profile : PolyProfile}
    (flag : UniverseFlag) :
    HasTypeDescBridge profile (TypingContext.empty : TypingContext profile 0)
      (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag) :=
  HasTypeDescBridge.bridgeFormation TypingContext.empty
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty
        (LevelExpr.lsucc LevelExpr.lzero) flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ The constant bridge — the FIRST GRADED-ROW INHABITANT.**  `pathLam(Type@0)` (the
dimension-constant body) is typed at `Bridge(Type@1, Type@0, Type@0)`: the body is closed, so
the affine usage premise computes to `0 ≤ 1` and both endpoint substitutions collapse to the
body itself.  The kernel's first internal-parametricity VALUE, with the type premise and the
usage premise discharged together. -/
theorem HasTypeDescBridge.constantBridgeTyped {profile : PolyProfile}
    (flag : UniverseFlag) :
    HasTypeDescBridge profile (TypingContext.empty : TypingContext profile 0)
      (pathLamCell (universeCodeCell LevelExpr.lzero flag))
      (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag)) :=
  HasTypeDescBridge.pathIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation
        (TypingContext.cons TypingContext.empty intervalTypeCell)
        LevelExpr.lzero flag))
    (Nat.zero_le 1)

/-- **★ Endpoint elimination is typed.**  Applying the constant bridge to the left endpoint:
`pathApp(pathLam(Type@0), 0) : Type@1` — the intro smoke eliminated at `intervalZero`. -/
theorem HasTypeDescBridge.constantBridgeAppliedTyped {profile : PolyProfile}
    (flag : UniverseFlag) :
    HasTypeDescBridge profile (TypingContext.empty : TypingContext profile 0)
      (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag))
        intervalZeroCell)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  HasTypeDescBridge.pathElim TypingContext.empty
    (pathLamCell (universeCodeCell LevelExpr.lzero flag)) intervalZeroCell
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (HasTypeDescBridge.constantBridgeTyped flag)
    (HasTypeDescBridge.intervalZero TypingContext.empty)

/-- **★ The graded-row honesty inversion: every typed bridge abstraction is AFFINE.**  If a
`pathLam`-headed subject is bridge-typed, its body uses the dimension binder at most once —
the usage discipline is FORCED by the engine, not merely permitted.  Equation-motive
inversion (free subject + threaded equality; cross-arm refutations by head-generator
no-confusion). -/
theorem HasTypeDescBridge.pathLamSubjectIsAffine {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBridge profile context subject classifier) :
    ∀ {body : RawTerm (scope + 1)}, subject = pathLamCell body →
      RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1 := by
  cases derivation with
  | intervalFormation _flag =>
      intro body subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | intervalZero =>
      intro body subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | intervalOne =>
      intro body subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | bridgeFormation _typeCode _leftEndpoint _rightEndpoint _level _flag
      _typeCodeTyped _leftTyped _rightTyped =>
      intro body subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | pathIntro armBody _typeCode _bodyTyped dimensionAffine =>
      intro body subjectEq
      have bodiesEqual : armBody = body := by injections
      exact bodiesEqual ▸ dimensionAffine
  | pathElim _path _argument _typeCode _leftEndpoint _rightEndpoint
      _pathTyped _argumentTyped =>
      intro body subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)

end FX1Poly.Typed
