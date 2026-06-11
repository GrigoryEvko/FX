import FX1Poly.Typed.HasTypeDescBridge
import FX1Poly.Typed.TermIndexedFormerSpike

/-! # FX1Poly/Typed/HasTypeDescTermIndexedFormer — NATIVE-12 [MEGA]: the TermIndexedFormer table + arm + Id/Bridge rows

NATIVE-02 (`TermIndexedFormerSpike`) settled the GO verdict: the term-indexed former premise — a carrier
typed at a universe plus endpoint terms typed at that carrier — is expressible over the grown engine, and
`HasTypeDescBridge.bridgeFormation`'s premise IS an instance.  What NATIVE-02 deferred to NATIVE-12 is the
INTERPRETER: a generator-table-driven typing arm that turns a table row + the term-indexed premise into a
typing, so that EVERY term-indexed former (the identity former `Id A a b`, the bridge former
`Bridge A a b`) is typed by ONE generic arm — never a bespoke per-former rule.

This is the term-indexed analogue of the formation table (`typingRuleDescOf` + `HasTypeDesc.genFormation`):

  * **the formation table** types formers whose children are a CUMULATIVE telescope of TYPES (`DescTelescope`,
    each child a universe member, the context extending under each — the Π/Σ shape);
  * **the term-indexed table** (here) types formers whose FIRST child is the carrier type and whose REMAINING
    children are MEMBERS of that carrier (no context extension — the Id/Bridge shape `[A, a, b]`).

The two premise spines differ exactly in what classifies the later children: a universe code (formation) vs an
earlier child viewed as a type (term-indexed).  Both arms are table-driven and cascade-free — adding a future
term-indexed former is one more row in `termIndexedFormerDescOf`, never a new arm.

## What ships

  * `TermIndexedFormerDesc` + `termIndexedCarrierOutput` + `termIndexedFormerDescOf` — the rule table, with the
    `gen_bridgeCode` and `gen_idCode` rows (both at the carrier-level output `Type@e`).
  * `TermIndexedEndpoints` — the endpoint sub-telescope (every later child typed at the fixed carrier, over
    the grown engine, indexed by the `RawTermChildren` spine — the children-data form of NATIVE-02's
    `TermIndexedFormerPremise`).
  * `TermIndexedFormerTelescope` — the full premise indexed by the children: head = carrier typed at a
    universe, tail = endpoints typed at the carrier.
  * `HasTypeDescTermIndexedFormer` — the standalone engine with ONE generic `genFormation` arm, consuming the
    table membership + the children-indexed telescope (the exact shape of `HasTypeDesc.genFormation`).
  * **★ `termIndexedFormerGenFormation_reconstructsBridge`** — ADEQUACY: the generic arm at `gen_bridgeCode`
    produces EXACTLY `bridgeFormation`'s conclusion from `bridgeFormation`'s premises (the bespoke bridge
    former IS the generic arm at one table row).
  * **★ `termIndexedFormerGenFormation_idCode`** — the Id former typed by the SAME generic arm at the OTHER
    table row, with NO bespoke `idFormation` rule anywhere — the table-genericity payoff (the NATIVE-17 Id
    retrofit rides this).
  * `termIndexedFormerGenFormation_bridgeUniverseSmoke` — non-vacuous closed witness.

## Honest scope

The ARM is shipped (term-indexed formers are now table-typed); its METATHEORY (weakening/subst/inversion/
uniqueness/context-conversion/SR/reducibility-FT-SN) is NATIVE-13..16.  The generic arm fixes the carrier as
the head child and types every later child at it — the Id/Bridge shape `[carrier, e₁, …, eₙ]`.  This engine is
standalone (cascade-free), to be merged into the unified judgment at NATIVE-45.

## Zero-axiom

A positive recursive inductive over the grown engine; the table is `if`-chained `Option`; the adequacy and
row witnesses are direct constructor applications (the output `termIndexedCarrierOutput … = universeCodeCell …`
collapses by `rfl`, the bridge cell `mkGen gen_bridgeCode () (childCons …)` IS `bridgeTypeCell` definitionally).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The term-indexed former rule description.**  The output classifier as a function of the scope, the
CARRIER's universe level, and the flag.  (A term-indexed former's output is the carrier's universe — `Bridge A
a b : Type@e` when `A : Type@e` — so unlike the formation table's `lmaxAll`, the level is the single carrier
level, not an iterated max.) -/
structure TermIndexedFormerDesc where
  /-- The rule's output classifier: a universe code at the carrier's level. -/
  outputType : (scope : Nat) → LevelExpr → UniverseFlag → RawTerm scope

/-- The output classifier shared by the term-indexed formers (Id, Bridge): a universe code at the CARRIER's
level — `Id A a b : Type@e` / `Bridge A a b : Type@e` when the carrier `A : Type@e`.  Factored out so the two
rows are visibly the same rule and the metadata lemmas reduce through one definition. -/
def termIndexedCarrierOutput (scope : Nat) (level : LevelExpr)
    (flag : UniverseFlag) : RawTerm scope :=
  universeCodeCell level flag

/-- **The per-generator term-indexed former table.**  `gen_bridgeCode` (the bridge/internal-parametricity
former) and `gen_idCode` (the identity-type former) are the two term-indexed formers, both arity-3
`[carrier, left, right]` and both at the carrier-level output.  Adding a future term-indexed former is one more
row here — never a new `HasTypeDescTermIndexedFormer` arm. -/
def termIndexedFormerDescOf (generator : Generator) : Option TermIndexedFormerDesc :=
  if generator = .gen_bridgeCode then some { outputType := termIndexedCarrierOutput }
  else if generator = .gen_idCode then some { outputType := termIndexedCarrierOutput }
  else none

/-- **The endpoint sub-telescope.**  Every later child (all at binder-shift `0`) is typed at the fixed
`carrier` via the grown engine — the children-data form of NATIVE-02's `TermIndexedFormerPremise`.  Indexed by
the `RawTermChildren` spine so the generic arm can consume the children abstractly. -/
inductive TermIndexedEndpoints (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (carrier : RawTerm scope) :
    {shifts : List Nat} → RawTermChildren shifts scope → Prop where
  | nil : TermIndexedEndpoints profile context carrier .childNil
  | cons {restShifts : List Nat} (endpoint : RawTerm scope)
      (rest : RawTermChildren restShifts scope)
      (endpointTyped : HasTypeDescPi profile context endpoint carrier)
      (restTyped : TermIndexedEndpoints profile context carrier rest) :
      TermIndexedEndpoints profile context carrier
        (RawTermChildren.childCons (shift := 0) endpoint rest)

/-- **The full term-indexed former premise, indexed by the children.**  The head child is the carrier (typed at
a universe code), and the tail children are the endpoints (each typed at the carrier).  The generic arm
consumes exactly this — the term-indexed analogue of `DescTelescope`. -/
inductive TermIndexedFormerTelescope (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) :
    {shifts : List Nat} → RawTermChildren shifts scope →
      RawTerm scope → LevelExpr → UniverseFlag → Prop where
  | mk {restShifts : List Nat} (carrier : RawTerm scope)
      (rest : RawTermChildren restShifts scope)
      (level : LevelExpr) (flag : UniverseFlag)
      (carrierTyped : HasTypeDescPi profile context carrier (universeCodeCell level flag))
      (endpointsTyped : TermIndexedEndpoints profile context carrier rest) :
      TermIndexedFormerTelescope profile context
        (RawTermChildren.childCons (shift := 0) carrier rest) carrier level flag

/-- **The description-driven term-indexed former judgment (NATIVE-12 core).**  ONE generic `genFormation` arm:
given a table row for `generator` and a children-indexed term-indexed telescope (carrier typed at a universe,
endpoints typed at the carrier), the cell `mkGen generator payload children` inhabits the rule's output (the
carrier's universe).  No per-former arm — the shape of `HasTypeDesc.genFormation`, with the term-indexed
premise spine in place of the cumulative `DescTelescope`. -/
inductive HasTypeDescTermIndexedFormer (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop where
  | genFormation {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
      (rule : TermIndexedFormerDesc)
      (isTermIndexed : termIndexedFormerDescOf generator = some rule)
      (premises : TermIndexedFormerTelescope profile context children carrier level flag) :
      HasTypeDescTermIndexedFormer profile context (.mkGen generator payload children)
        (rule.outputType scope level flag)

/-! ## Table metadata (`rfl`) -/

/-- `gen_bridgeCode`'s term-indexed row is the carrier-level output. -/
theorem termIndexedFormerDescOf_bridgeCode :
    termIndexedFormerDescOf .gen_bridgeCode = some { outputType := termIndexedCarrierOutput } := rfl

/-- `gen_idCode`'s term-indexed row is the carrier-level output (the SAME rule — table-genericity). -/
theorem termIndexedFormerDescOf_idCode :
    termIndexedFormerDescOf .gen_idCode = some { outputType := termIndexedCarrierOutput } := rfl

/-- A non-term-indexed former (here `gen_piTyCode`) has no term-indexed row. -/
theorem termIndexedFormerDescOf_piTyCode :
    termIndexedFormerDescOf .gen_piTyCode = none := rfl

/-! ## ★ Adequacy + the Id/Bridge rows -/

/-- **★ The generic arm reconstructs the bridge former.**  From `bridgeFormation`'s premises (carrier typed at
a universe, two endpoints typed at the carrier), the generic table-driven arm at the `gen_bridgeCode` row
produces EXACTLY `bridgeFormation`'s conclusion `bridgeTypeCell carrier left right : Type@level`.  The bespoke
`HasTypeDescBridge.bridgeFormation` is therefore the generic `genFormation` arm at one table row — its premise
IS an instance of the term-indexed premise spine (NATIVE-02's adequacy, now realized through the engine). -/
theorem termIndexedFormerGenFormation_reconstructsBridge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (carrier leftEndpoint rightEndpoint : RawTerm scope)
    (level : LevelExpr) (flag : UniverseFlag)
    (carrierTyped : HasTypeDescPi profile context carrier (universeCodeCell level flag))
    (leftTyped : HasTypeDescPi profile context leftEndpoint carrier)
    (rightTyped : HasTypeDescPi profile context rightEndpoint carrier) :
    HasTypeDescTermIndexedFormer profile context
      (bridgeTypeCell carrier leftEndpoint rightEndpoint)
      (universeCodeCell level flag) :=
  HasTypeDescTermIndexedFormer.genFormation context .gen_bridgeCode ()
    (.childCons carrier (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
    carrier level flag { outputType := termIndexedCarrierOutput } rfl
    (TermIndexedFormerTelescope.mk carrier
      (show RawTermChildren [0, 0] scope from
        .childCons leftEndpoint (.childCons rightEndpoint .childNil)) level flag
      carrierTyped
      (TermIndexedEndpoints.cons leftEndpoint
        (show RawTermChildren [0] scope from .childCons rightEndpoint .childNil) leftTyped
        (TermIndexedEndpoints.cons rightEndpoint
          (show RawTermChildren [] scope from .childNil) rightTyped
          TermIndexedEndpoints.nil)))

/-- **★ The Id former is typed by the SAME generic arm — at the OTHER table row.**  `Id(carrier, left, right) :
Type@level` from the identical premises, with NO bespoke `idFormation` rule anywhere: the generic
`genFormation` arm at the `gen_idCode` row covers it.  THE table-genericity payoff of NATIVE-12 — adding the
Id former cost ONE table row (`termIndexedFormerDescOf_idCode`), not a new engine.  (The NATIVE-17 Id retrofit
— `idCode` formable, `refl` classifier grown-formable — rides exactly this arm.) -/
theorem termIndexedFormerGenFormation_idCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (carrier leftEndpoint rightEndpoint : RawTerm scope)
    (level : LevelExpr) (flag : UniverseFlag)
    (carrierTyped : HasTypeDescPi profile context carrier (universeCodeCell level flag))
    (leftTyped : HasTypeDescPi profile context leftEndpoint carrier)
    (rightTyped : HasTypeDescPi profile context rightEndpoint carrier) :
    HasTypeDescTermIndexedFormer profile context
      (.mkGen .gen_idCode ()
        (.childCons carrier (.childCons leftEndpoint (.childCons rightEndpoint .childNil))))
      (universeCodeCell level flag) :=
  HasTypeDescTermIndexedFormer.genFormation context .gen_idCode ()
    (.childCons carrier (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
    carrier level flag { outputType := termIndexedCarrierOutput } rfl
    (TermIndexedFormerTelescope.mk carrier
      (show RawTermChildren [0, 0] scope from
        .childCons leftEndpoint (.childCons rightEndpoint .childNil)) level flag
      carrierTyped
      (TermIndexedEndpoints.cons leftEndpoint
        (show RawTermChildren [0] scope from .childCons rightEndpoint .childNil) leftTyped
        (TermIndexedEndpoints.cons rightEndpoint
          (show RawTermChildren [] scope from .childNil) rightTyped
          TermIndexedEndpoints.nil)))

/-- **★ Non-vacuous closed witness.**  `Bridge(Type@1, Type@0, Type@0) : Type@2` typed through the generic
term-indexed arm — the same subject/classifier as `HasTypeDescBridge.bridgeOfUniverseCodesTyped`, now via the
table-driven engine (carrier `Type@1 : Type@2`, endpoints `Type@0 : Type@1` members of the carrier). -/
theorem termIndexedFormerGenFormation_bridgeUniverseSmoke {profile : PolyProfile}
    (flag : UniverseFlag) :
    HasTypeDescTermIndexedFormer profile (TypingContext.empty : TypingContext profile 0)
      (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag) :=
  termIndexedFormerGenFormation_reconstructsBridge
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

end FX1Poly.Typed
