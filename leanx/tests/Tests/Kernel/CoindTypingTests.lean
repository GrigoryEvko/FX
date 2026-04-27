import FX.Kernel.Typing
import FX.Derived.Session

/-!
# Coind typing tests (task S6)

Pin the three Coind typing rules landed in S6:

  * **Coind-form** — `Term.coind name args` infers `.type .zero`
    when the spec is registered and the arg count matches.
  * **Coind-intro** — `Term.coindUnfold name typeArgs arms` infers
    `.coind name typeArgs` when each arm has the corresponding
    destructor's `resultType`.
  * **Coind-elim** — `Term.coindDestruct name index target`
    infers the destructor's `resultType` (with target's params
    substituted) when the target has `.coind name _` type.

Specs are registered via `GlobalEnv.addUserCoindSpecs` using the
output of `FX.Derived.Session.translate` — real translator
output, not hand-rolled specs.  This pins the integration
between S11 (elaborator registration) and S6 (kernel typing).

All checks are compile-time `example` assertions via
`native_decide`.  Partial defs in reduction and typing require
native compilation; ordinary `decide` won't reduce through them.
-/

namespace Tests.Kernel.CoindTypingTests

open FX.Kernel
open FX.Kernel.Term
open FX.Derived.Session

/-! ## Test helpers — thread a GlobalEnv into `infer` -/

/-- True iff `infer context term globalEnv = .ok inferred` and
    `inferred == expected`.  Parallel to `TypingTests.inferOk` but
    accepts the GlobalEnv argument. -/
private def inferOkE (context : TypingContext) (globalEnv : GlobalEnv)
    (term expected : Term) : Bool :=
  match infer context term globalEnv with
  | .ok inferred => inferred == expected
  | .error _     => false

/-- True iff `infer context term globalEnv = .error e` AND
    `e.code == expectedCode`.  Parallel to
    `TypingTests.inferFailsCode`. -/
private def inferFailsCodeE (context : TypingContext) (globalEnv : GlobalEnv)
    (term : Term) (expectedCode : String) : Bool :=
  match infer context term globalEnv with
  | .error typeError => typeError.code == expectedCode
  | .ok _            => false

/-- Register a session-translated spec in a fresh GlobalEnv and
    return (rootName, env). -/
private def envWith (namePrefix : String) (session : SessionType)
    : String × GlobalEnv :=
  let result := translate namePrefix session
  let envWithSpecs := ({} : GlobalEnv).addUserCoindSpecs result.specs
  (result.rootName, envWithSpecs)

private def typeZero : Term := .type Level.zero

/-! ## Coind-form — `Term.coind` inhabits `.type .zero`

A registered coinductive spec name resolves via
`GlobalEnv.coindSpecByName?`.  With zero parameters (the shape
every session translation produces), the form is simply
`.coind name []`.
-/

-- endS translates to a single terminal spec.  coind on its
-- root name infers `.type .zero` (no params needed).
example :
  let (rootName, env) := envWith "TrialEnd" SessionType.endS
  inferOkE [] env (.coind rootName []) typeZero = true := by native_decide

-- send(Nat, end): root spec has one "send" destructor; coind
-- on its name with zero params still infers `.type .zero`.
example :
  let natPayload := Term.ind "Nat" []
  let (rootName, env) := envWith "SendCh" (SessionType.send natPayload .endS)
  inferOkE [] env (.coind rootName []) typeZero = true := by native_decide

-- Unknown spec name → T110 (unknown coinductive type).
example :
  inferFailsCodeE [] {} (.coind "NoSuchSpec" []) "T110" = true := by native_decide

-- Wrong param count on a zero-param spec → T111.
example :
  let (rootName, env) := envWith "TrialEnd" SessionType.endS
  inferFailsCodeE [] env (.coind rootName [typeZero]) "T111" = true := by
  native_decide

/-! ## Coind-intro — `coindUnfold` inhabits `.coind name typeArgs`

An unfold introduces a codata value.  It must supply one arm
per destructor; each arm's type must match the destructor's
`resultType`.  For an empty spec (endS/stop), there are zero
destructors, so the unfold takes zero arms.
-/

-- Terminal spec (endS translation): zero destructors → zero-arm
-- unfold infers `.coind rootName []`.  The minimal Coind-intro.
example :
  let (rootName, env) := envWith "EndUnfold" SessionType.endS
  let unfold := Term.coindUnfold rootName [] []
  inferOkE [] env unfold (.coind rootName []) = true := by native_decide

-- Mismatched arm count on a zero-destructor spec → T113.
-- Providing one arm where the spec expects zero is rejected.
example :
  let (rootName, env) := envWith "EndUnfold" SessionType.endS
  let unfold := Term.coindUnfold rootName [] [typeZero]
  inferFailsCodeE [] env unfold "T113" = true := by native_decide

-- Mismatched param count: zero-param spec given one type arg → T111.
example :
  let (rootName, env) := envWith "EndUnfold" SessionType.endS
  let unfold := Term.coindUnfold rootName [typeZero] []
  inferFailsCodeE [] env unfold "T111" = true := by native_decide

-- Unknown name → T110.
example :
  let unfold := Term.coindUnfold "NoSuchSpec" [] []
  inferFailsCodeE [] {} unfold "T110" = true := by native_decide

/-! ## Coind-elim — `coindDestruct` infers the destructor type

Observing destructor #i on a target of `.coind name typeArgs`
type yields a value of the destructor's `resultType` with the
params substituted.  For the zero-param case, substitution is
a no-op.

The test setup uses an *axiomatised* target via a context-bound
variable.  The kernel doesn't reduce `.var 0` at whnf (it's a
neutral), so `infer` reaches `.coind` directly — which is the
well-formedness check we care about.
-/

-- send(Nat, end): destruct #0 on a target of `coind root []`
-- should yield the send destructor's resultType, which is
-- `Π(x: Nat, coind cont []) Tot` (params = [], substitution
-- is a no-op).  Factored into a Bool helper so `native_decide`
-- sees a pure Bool equation.
private def destructSendInfersResultType : Bool :=
  let natPayload      := Term.ind "Nat" []
  let (rootName, env) := envWith "SendCh" (SessionType.send natPayload .endS)
  let expectedType    := (env.coindSpecByName? rootName).bind
    (fun spec => spec.destructors.head?)
    |>.map (fun dest => dest.resultType)
  match expectedType with
  | none              => false
  | some expected     =>
    let context  := [{ grade := Grade.default, typeTerm := .coind rootName [] }]
    let destruct := Term.coindDestruct rootName 0 (Term.var 0)
    inferOkE context env destruct expected

example : destructSendInfersResultType = true := by native_decide

-- Out-of-bounds destructor index on a single-destructor spec → T112.
example :
  let natPayload := Term.ind "Nat" []
  let (rootName, env) := envWith "SendCh" (SessionType.send natPayload .endS)
  let context  := [{ grade := Grade.default, typeTerm := .coind rootName [] }]
  let destruct := Term.coindDestruct rootName 5 (Term.var 0)
  inferFailsCodeE context env destruct "T112" = true := by native_decide

-- Unknown spec name on destructor → T110.
example :
  let context  := [{ grade := Grade.default, typeTerm := typeZero }]
  let destruct := Term.coindDestruct "NoSuchSpec" 0 (Term.var 0)
  inferFailsCodeE context {} destruct "T110" = true := by native_decide

-- Target with non-coind type (here `type Level.zero` — type of
-- types) → T115: "destructor target must have coinductive type".
example :
  let (rootName, env) := envWith "SendCh"
    (SessionType.send (Term.ind "Nat" []) .endS)
  -- Context binds a var at type `.type .zero` (inhabitant: any type).
  let context  := [{ grade := Grade.default, typeTerm := typeZero }]
  let destruct := Term.coindDestruct rootName 0 (Term.var 0)
  inferFailsCodeE context env destruct "T115" = true := by native_decide

-- Target with mismatched coind name → T115.  Both specs are
-- registered, but destructor names one while target is typed
-- as the other.
example :
  let natPayload := Term.ind "Nat" []
  let resA       := translate "ChanA" (SessionType.send natPayload .endS)
  let resB       := translate "ChanB" (SessionType.recv natPayload .endS)
  let env        := GlobalEnv.addUserCoindSpecs
                     (GlobalEnv.addUserCoindSpecs {} resA.specs) resB.specs
  -- Target is typed at ChanA's root; destructor names ChanB's root.
  let context    := [{ grade := Grade.default, typeTerm := .coind resA.rootName [] }]
  let destruct   := Term.coindDestruct resB.rootName 0 (Term.var 0)
  inferFailsCodeE context env destruct "T115" = true := by native_decide

/-! ## Two-destructor spec — index discrimination

selectS with two branches produces a spec with two destructors.
Verify that indices 0 and 1 pick distinct destructors' result
types, and index 2 is out of bounds.
-/

private def selectDiscriminatesDestructorIndices : Bool :=
  let sessions        := SessionType.selectS [("a", .endS), ("b", .endS)]
  let (rootName, env) := envWith "SelCh" sessions
  match env.coindSpecByName? rootName with
  | none      => false
  | some spec =>
    match spec.destructors with
    | dest0 :: dest1 :: _ =>
      let context := [{ grade := Grade.default, typeTerm := .coind rootName [] }]
      let d0      := Term.coindDestruct rootName 0 (Term.var 0)
      let d1      := Term.coindDestruct rootName 1 (Term.var 0)
      -- Each destructor index picks the matching resultType.  The
      -- two resultTypes are structurally distinct (different
      -- continuation spec names), witnessing discrimination.
      inferOkE context env d0 dest0.resultType
        && inferOkE context env d1 dest1.resultType
    | _ => false

example : selectDiscriminatesDestructorIndices = true := by native_decide

-- Two-destructor spec, index 2 → T112.
example :
  let sessions := SessionType.selectS [("a", .endS), ("b", .endS)]
  let (rootName, env) := envWith "SelCh" sessions
  let context  := [{ grade := Grade.default, typeTerm := .coind rootName [] }]
  let destruct := Term.coindDestruct rootName 2 (Term.var 0)
  inferFailsCodeE context env destruct "T112" = true := by native_decide

end Tests.Kernel.CoindTypingTests
