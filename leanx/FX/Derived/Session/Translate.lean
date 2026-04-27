import FX.Derived.Session.Binary
import FX.Kernel.Coinductive

/-!
# Session → Coind translation (task S9)

`FX/Derived/Session/Binary.lean` defines `SessionType` as a
standalone inductive tree of protocol states.  The kernel
uses `FX.Kernel.CoindSpec` (from `A2`) for coinductive types
and `Term.coind` / `Term.indRec`-analogue destructors for
their elimination.  S9 bridges the two: given a `SessionType`
tree, generate a list of `CoindSpec`s — one per distinct
sub-state — plus the root spec's name.

Downstream tasks consume this translation:

  * **S11** registers the generated `CoindSpec`s in the global
    env at `session_decl` elaboration time.
  * **S6** supplies the typing rules for channel destructor
    calls by looking up the appropriate spec.
  * **S13** desugars surface `send` / `receive` / `select` /
    `offer` to destructor-call `Term`s against these specs.

## Encoding

For each `SessionType` constructor:

  * `endS` / `stop`: a terminal `CoindSpec` with zero
    destructors.  Observing a terminated channel yields
    nothing — the value has completed its protocol.
  * `send(T, cont)`: one destructor named `send` whose
    result type is `Pi(_ :_ghost T) → coind <contName>`
    (conceptually: "consume a T, return the next channel").
  * `recv(T, cont)`: symmetric — destructor named `recv` with
    the same shape.  The direction distinction lives in the
    destructor's NAME, not the type (the payload-flow
    direction is an operational concern captured by S13's
    send/recv desugaring).
  * `selectS(branches)` / `offerS(branches)`: one destructor
    per branch, named after the branch label, whose result
    type is `coind <branchContName>`.  The structural layout
    is identical for both — direction again lives in
    surface-level distinction, not in the spec data.
  * `loopS(body)`: the loop's spec is `body`'s spec emitted
    under a reserved up-front name.  `continueS` inside
    `body` resolves to that reserved name, creating the
    self-loop edge (via `coind <loopName>`).
  * `continueS`: outside any `loopS` it's malformed and
    recorded in `errors`; inside a `loopS` it references the
    innermost enclosing loop's reserved spec name without
    emitting a new spec.

Nested `loopS` (a `loopS` whose immediate body is another
`loopS`) is allowed by `Binary.wellFormed` but creates an
unused reserved name for the outer loop — the inner loop's
`loopS` generates its own fresh name via `freshName` and uses
THAT as its spec name (because `loopS` translates its body
with the assigned name slot).  This is a well-known edge
case; downstream `wellFormed` callers may choose to reject
it.  S9 itself doesn't reject; it leaks a counter slot.

## Name generation

The translator takes a `namePrefix` string and appends
`_<counter>`.  A session declared as `session AuthClient =
...` would typically call `translate "AuthClient" session`
and get specs named `AuthClient_0`, `AuthClient_1`, etc.
S11 is responsible for deduplicating against existing global
env names.

## Malformed-input handling

`continueS` outside any `loopS` is structurally malformed; it
could only arise from a manually-constructed `SessionType`
that bypasses `wellFormed`.  The translator emits a terminal
spec as a sentinel value and records the error in
`TranslationResult.errors`.  Consumers MUST check for empty
errors before registering the result in the kernel global
env (S11 will do this).

## Trust layer

`FX/Derived/Session/` is L3 untrusted per SPEC.md §5.  This
translator's correctness (that it produces `CoindSpec`s
satisfying `CoindSpec.isSatisfied`) is a property we can
pin by `decide` over concrete examples but haven't
mechanized as a universal theorem.  S25's conformance suite
and S20's association-invariant proofs will strengthen that
relationship.
-/

namespace FX.Derived.Session

open FX.Kernel (Term Effect Grade CoindSpec CoindDestructor)

/-- Result of translating one `SessionType` tree.  `rootName`
    is the name of the spec at the ROOT of the session (the
    channel's initial state), `specs` is the full
    declaration-order list, and `errors` records any
    malformed-input issues encountered. -/
structure TranslationResult where
  rootName : String
  specs    : List CoindSpec
  errors   : List String
  deriving Repr, Inhabited

namespace Translate

/-- Internal translator state threaded through the recursion.
    Kept `private` so callers use the public `translate`
    entry point rather than constructing state directly. -/
private structure State where
  namePrefix    : String
  counter   : Nat
  specsRev  : List CoindSpec
  loopStack : List String
  errors    : List String
  deriving Repr, Inhabited

/-- Fresh state with the given namePrefix. -/
private def initState (namePrefix : String) : State :=
  { namePrefix    := namePrefix
  , counter   := 0
  , specsRev  := []
  , loopStack := []
  , errors    := [] }

/-- Generate a fresh spec name and bump the counter. -/
private def freshName (state : State) : String × State :=
  let name := s!"{state.namePrefix}_{state.counter}"
  (name, { state with counter := state.counter + 1 })

/-- If the caller assigned a name, use it; otherwise mint one. -/
private def resolveName (assigned : Option String) (state : State)
    : String × State :=
  match assigned with
  | some alreadyAssigned => (alreadyAssigned, state)
  | none                 => freshName state

/-- Append a spec to the reverse list (specs are reversed to
    O(1) prepend; `TranslationResult` reverses at the end). -/
private def emitSpec (spec : CoindSpec) (state : State) : State :=
  { state with specsRev := spec :: state.specsRev }

/-- Helper: emit a terminal (zero-destructor) spec. -/
private def emitTerminal (assigned : Option String) (state : State)
    : String × State :=
  let (name, nextState) := resolveName assigned state
  let terminalSpec : CoindSpec :=
    { name := name, params := [], destructors := [] }
  (name, emitSpec terminalSpec nextState)

/-! Main mutual recursion: translate one session + its branches.

The `assignedName` argument is `some N` when the caller
(typically `loopS`) has reserved a specific name for this
spec; `none` mints a fresh one. -/

mutual

/-- Translate one `SessionType` node.  Recurses into
    continuations and branches via the mutual `ofBranches`. -/
partial def ofSession
    (assignedName : Option String)
    (session : SessionType)
    (state : State) : String × State :=
  match session with
  | .endS => emitTerminal assignedName state
  | .stop => emitTerminal assignedName state
  | .send payloadType continuation =>
    let (contName, afterCont)  := ofSession none continuation state
    let (specName, afterName)  := resolveName assignedName afterCont
    let sendDestructor : CoindDestructor :=
      { name       := "send"
      , resultType :=
          Term.pi Grade.default payloadType
            (Term.coind contName []) Effect.tot }
    let builtSpec : CoindSpec :=
      { name := specName, params := [], destructors := [sendDestructor] }
    (specName, emitSpec builtSpec afterName)
  | .recv payloadType continuation =>
    let (contName, afterCont)  := ofSession none continuation state
    let (specName, afterName)  := resolveName assignedName afterCont
    let recvDestructor : CoindDestructor :=
      { name       := "recv"
      , resultType :=
          Term.pi Grade.default payloadType
            (Term.coind contName []) Effect.tot }
    let builtSpec : CoindSpec :=
      { name := specName, params := [], destructors := [recvDestructor] }
    (specName, emitSpec builtSpec afterName)
  | .selectS branches =>
    let (destructorsList, afterBranches) := ofBranches branches state
    let (specName, afterName) := resolveName assignedName afterBranches
    let builtSpec : CoindSpec :=
      { name := specName, params := [], destructors := destructorsList }
    (specName, emitSpec builtSpec afterName)
  | .offerS branches =>
    let (destructorsList, afterBranches) := ofBranches branches state
    let (specName, afterName) := resolveName assignedName afterBranches
    let builtSpec : CoindSpec :=
      { name := specName, params := [], destructors := destructorsList }
    (specName, emitSpec builtSpec afterName)
  | .loopS body =>
    let (reservedLoopName, afterReserve) := freshName state
    let pushedStack := { afterReserve with
      loopStack := reservedLoopName :: afterReserve.loopStack }
    let (_, afterBody) := ofSession (some reservedLoopName) body pushedStack
    let poppedStack := { afterBody with
      loopStack := afterBody.loopStack.tail }
    (reservedLoopName, poppedStack)
  | .continueS =>
    match state.loopStack with
    | enclosingLoop :: _ => (enclosingLoop, state)
    | []                 =>
      let (fallbackName, afterFallback) :=
        emitTerminal assignedName state
      let withError := { afterFallback with
        errors :=
          s!"continueS outside any loopS (orphan binding); emitted terminal spec '{fallbackName}' as sentinel"
            :: afterFallback.errors }
      (fallbackName, withError)

partial def ofBranches
    (branches : List (Label × SessionType))
    (state : State) : List CoindDestructor × State :=
  match branches with
  | []                               => ([], state)
  | (branchLabel, branchCont) :: rest =>
    let (contName, afterCont) := ofSession none branchCont state
    let branchDestructor : CoindDestructor :=
      { name := branchLabel, resultType := Term.coind contName [] }
    let (restDestructors, afterRest) := ofBranches rest afterCont
    (branchDestructor :: restDestructors, afterRest)

end  -- mutual

end Translate

/-- Translate a `SessionType` tree into a list of
    `CoindSpec`s with the root spec's name.  The `namePrefix`
    parameter is prepended to every generated spec's name
    (e.g., `"AuthClient"` yields `AuthClient_0`,
    `AuthClient_1`, ...).  Downstream S11 is responsible for
    checking no name collides with an existing global-env
    entry.

    A non-empty `errors` list indicates malformed input
    (currently only: `continueS` outside any `loopS`); the
    returned specs list is still well-formed Lean data but
    semantically incomplete. -/
def translate (namePrefix : String) (session : SessionType)
    : TranslationResult :=
  let initial := Translate.initState namePrefix
  let (rootName, final) := Translate.ofSession none session initial
  { rootName := rootName
  , specs    := final.specsRev.reverse
  , errors   := final.errors.reverse }

/-- `true` iff the translation succeeded without recording any
    structural errors. -/
def TranslationResult.wasSuccessful (result : TranslationResult) : Bool :=
  result.errors.isEmpty

/-- Total spec count in the result.  Matches the number of
    distinct sub-session states generated. -/
def TranslationResult.specCount (result : TranslationResult) : Nat :=
  result.specs.length

/-- Lookup a spec by its generated name.  Returns `none` when
    the name is absent from `specs`. -/
def TranslationResult.specByName? (result : TranslationResult)
    (name : String) : Option CoindSpec :=
  result.specs.find? fun candidate => candidate.name == name

/-! ## Dual-pair translation (task S12)

The `new_channel<S>()` primitive (§11.2) produces a pair whose
endpoints carry dual session types: one endpoint at session `S`,
the other at `dual(S)`.  For both endpoints to be type-checked
by the Coind-form typing rule (S6), both `S`'s and `dual(S)`'s
translated `CoindSpec`s must be registered in `GlobalEnv`.

`translateDualPair` emits both halves.  The dual is translated
under a `"<prefix>__dual"` name prefix — a double underscore to
avoid collision with any user-written session name (normal
session decls use a single-underscore suffix pattern like
`Chan_1`; the doubled-underscore marker is reserved for
compiler-emitted duals).

Duality is structural: `dual` (Binary.lean) is a total function
from SessionType to SessionType that swaps send/recv and
select/offer while preserving loop/continue structure.  S3
proves `dual (dual s) = s` — translating the dual pair is
idempotent at the session-tree level, though the spec names
(`"Chan"`, `"Chan__dual"`, `"Chan__dual__dual"` if triple-
translated) diverge.

Callers (notably S11's `elabSessionDeclSpec`) concatenate the
two `specs` lists before calling `GlobalEnv.addUserCoindSpecs`. -/

/-- The dual name-prefix marker.  Appended to the primary
    session's prefix when translating its dual.  Double-
    underscore by convention so compiler-emitted dual names
    never collide with user-declared session names. -/
private def dualMarker : String := "__dual"

/-- Translate a session and its dual in one pass.  Returns both
    translation results.  The primary's errors are independent of
    the dual's; a malformed session may or may not produce a
    malformed dual (structural walking is identical, but the
    `continueS`-orphan test applies to each tree separately —
    in practice dual of a well-formed session is always
    well-formed). -/
def translateDualPair (namePrefix : String) (session : SessionType)
    : TranslationResult × TranslationResult :=
  let primary   := translate namePrefix session
  let dualSess  := SessionType.dual session
  let dualResult := translate (namePrefix ++ dualMarker) dualSess
  (primary, dualResult)

/-- The dual-pair's combined specs, primary first, dual second.
    Suitable for a single `GlobalEnv.addUserCoindSpecs` call. -/
def translateDualPairSpecs (namePrefix : String) (session : SessionType)
    : List CoindSpec :=
  let (primaryResult, dualResult) := translateDualPair namePrefix session
  primaryResult.specs ++ dualResult.specs

/-- Collected errors from both halves of the dual pair.  Empty
    iff both translations succeeded. -/
def translateDualPairErrors (namePrefix : String) (session : SessionType)
    : List String :=
  let (primaryResult, dualResult) := translateDualPair namePrefix session
  primaryResult.errors ++ dualResult.errors

end FX.Derived.Session
