import FX.Kernel.Term

/-!
# Derived spec — Session types, Layer 1 binary combinators (§11.2, S1)

First landing of FX's session-type machinery per §11 of the
design document, implementing stage S1 of the 25-stage
plan.  This file establishes the L1 surface combinator
vocabulary — eight per-endpoint session-type constructors
from Honda 1998's binary core, extended with the `Stop`
marker from the crash-stop extensions of §11.21.

## Scope

This file defines only the session-type data type and a
handful of canonical examples.  Every operation on session
types — duality, well-formedness, subtyping, kernel
translation — lands in subsequent stages and references
the vocabulary established here.

The eight constructors follow §11.2:

  * `endS` — the protocol has terminated.
  * `stop` — a crashed endpoint.  Vacuously a subtype of
    every session type (§11.21); the post-crash position
    satisfies any remaining protocol because the crashed
    participant will not observe further events.
  * `send P K` — send a payload of type `P`, continue as
    `K`.
  * `recv P K` — receive a payload of type `P`, continue
    as `K`.
  * `selectS bs` — the endpoint chooses one of the
    labelled branches in `bs`; each branch carries its own
    continuation.
  * `offerS bs` — the peer chooses; this endpoint offers
    all the listed branches and continues according to the
    peer's pick.
  * `loopS body` — protocol recursion.  Every `continueS`
    in `body` is bound to this loop.
  * `continueS` — re-enter the innermost enclosing
    `loopS`.

The loop/continue discipline uses De-Bruijn-style single-
scope binding in v1: every `continueS` refers to the
nearest enclosing `loopS`.  Named-recursion-variable
bindings (`μt.T` / `t`) with multi-level nesting are a
later-stage extension.

## Payload types

A session's payload types are kernel `Term` values.  This
is deliberate: the existing subtyping, refinement, and
effect-inference machinery operates on `Term` directly, so
session types inherit it without a separate payload
abstraction.  The dependency on `Term` means `SessionType`
does not derive `DecidableEq`; structural comparison is
handled by an analogue of `Term.structEq` added at stage
S5.

## Status in the implementation layer

Untrusted (L3 per SPEC.md §5).  The kernel-level soundness
sits on the `CoindSpec` discipline of Appendix H.5 once
the translation of stage S9 lands.  Until then the data
type is standalone — any obligations it bears at
elaboration go through future Session modules, not through
the kernel.
-/

namespace FX.Derived.Session

open FX.Kernel

/-- Branch labels on `selectS` and `offerS` are strings in
    v1.  Well-formedness (stage S4, §11.14) enforces
    pairwise distinctness within each choice point. -/
abbrev Label := String

/-- Per-endpoint session type.  See the module docstring
    for the semantics of each constructor and §11.2 of the
    design document for the surface syntax.

    Equality on `SessionType` is not decidable because
    payload `Term`s do not derive `DecidableEq`.  Later
    stages add a `sessionTypeBeq` function that mirrors
    `Term.structEq` for structural comparison in
    specification contexts. -/
inductive SessionType : Type where
  | endS      : SessionType
  | stop      : SessionType
  | send      (payloadType : Term) (continuation : SessionType) : SessionType
  | recv      (payloadType : Term) (continuation : SessionType) : SessionType
  | selectS   (branches : List (Label × SessionType)) : SessionType
  | offerS    (branches : List (Label × SessionType)) : SessionType
  | loopS     (body : SessionType) : SessionType
  | continueS : SessionType
  deriving Inhabited, Repr

namespace SessionType

/-! ## Canonical examples

A small catalog of canonical session patterns.  Each
example is a `def` so later stages can pin properties
against concrete values — for instance, that `dual
requestResponseLoopClient` equals `requestResponseLoopServer`,
or that `wellFormed authClient` discharges.

The examples exercise each combinator class: plain
send/recv sequences, branch choice, and guarded recursion.
Payload types use `Term.ind` with placeholder names; a
future prelude integration will use real kernel payload
types. -/

/-- One-shot request-response, client view: send a request
    and receive a response, then end. -/
def requestResponseOnce : SessionType :=
  .send (Term.ind "Request" [])
    (.recv (Term.ind "Response" []) .endS)

/-- Request-response loop, client view: indefinitely send a
    request and receive a response.  The loop body ends
    with `continueS` to iterate. -/
def requestResponseLoopClient : SessionType :=
  .loopS
    (.send (Term.ind "Request" [])
      (.recv (Term.ind "Response" []) .continueS))

/-- Request-response loop, server view.  Dual of
    `requestResponseLoopClient`; stage S2's `dual` function
    will derive one from the other. -/
def requestResponseLoopServer : SessionType :=
  .loopS
    (.recv (Term.ind "Request" [])
      (.send (Term.ind "Response" []) .continueS))

/-- Authentication protocol, client view: send credentials,
    then branch on success or failure.  The canonical
    example for `offerS`. -/
def authClient : SessionType :=
  .send (Term.ind "Credentials" [])
    (.offerS [
      ("success", .recv (Term.ind "Token" [])  .endS),
      ("failure", .recv (Term.ind "Reason" []) .endS)
    ])

/-- Authentication protocol, server view.  Dual of
    `authClient`: receive credentials, then select the
    outcome. -/
def authServer : SessionType :=
  .recv (Term.ind "Credentials" [])
    (.selectS [
      ("success", .send (Term.ind "Token" [])  .endS),
      ("failure", .send (Term.ind "Reason" []) .endS)
    ])

/-- Stream reader endpoint.  Loop offering either `next`
    with a payload or `done` for termination.  Models
    unbounded producer-consumer with explicit termination. -/
def streamReader : SessionType :=
  .loopS (.offerS [
    ("next", .recv (Term.ind "Item" []) .continueS),
    ("done", .endS)
  ])

/-- Stream writer endpoint.  Dual of `streamReader`: loop
    selecting either `next` with a payload or `done`. -/
def streamWriter : SessionType :=
  .loopS (.selectS [
    ("next", .send (Term.ind "Item" []) .continueS),
    ("done", .endS)
  ])

/-! ## Structural properties pinned at construction

These examples verify the inductive's basic shape without
needing any operations yet.  Later stages attach
`dual_dual`, `wellFormed_dual`, and subtype examples to
the same values. -/

-- `endS` is always the bottom of a finite protocol and
-- carries no payload.
example : SessionType.endS = .endS := rfl

-- `stop` is a distinct constructor from `endS`; pin the
-- difference so a refactor collapsing the two surfaces
-- here.
example : (SessionType.stop = .endS) = False := by
  simp

-- `continueS` and `endS` are distinct even though both are
-- nullary leaves of the grammar.
example : (SessionType.continueS = .endS) = False := by
  simp

/-! ## Duality (§11.2, S2)

`dual` swaps the role of each communication action: a send
becomes a receive and a select becomes an offer, with the
swap applied structurally through continuations and branch
bodies.  Two endpoints of a channel whose session types are
dual produce matched communication by construction — every
send on one side has a receive on the other, every select
on one side has an offer on the other, and label sets
align.  This is the central property of Honda 1998's
binary-session discipline.

`dual` is mutually recursive with `dualBranches` over the
List-of-branches payload carried by `selectS` and `offerS`.
The mutual form lets Lean's termination checker see the
structural decrease: every `dual` call inside
`dualBranches` is on a body strictly smaller than the list
element containing it, and every `dualBranches` call inside
`dual` is on a list strictly smaller than the enclosing
`selectS` or `offerS` argument.  The pattern mirrors
`FX/Kernel/Coinductive.lean`'s `Guarded.absent` /
`Guarded.absentList` pair.

The involutivity theorem `dual (dual T) = T` lands in stage
S3; this file exports the function and the pinning
examples only. -/

mutual

/-- Swap sends with receives and selects with offers
    structurally.  Keeps `endS`, `stop`, `continueS`, and
    loop bodies in place; recurses into every non-leaf
    continuation.  Preserves well-formedness (§11.14):
    guarded recursion and label distinctness are structural
    and survive the swap. -/
def dual : SessionType → SessionType
  | .endS             => .endS
  | .stop             => .stop
  | .send P K         => .recv P (dual K)
  | .recv P K         => .send P (dual K)
  | .selectS branches => .offerS (dualBranches branches)
  | .offerS branches  => .selectS (dualBranches branches)
  | .loopS body       => .loopS (dual body)
  | .continueS        => .continueS

/-- Dualize every branch body in a `selectS` or `offerS`
    branch list.  Threads `dual` through each body; labels
    are preserved verbatim so duality commutes with label
    lookup. -/
def dualBranches : List (Label × SessionType) → List (Label × SessionType)
  | []                    => []
  | (label, body) :: rest => (label, dual body) :: dualBranches rest

end

/-! ### Nullary-case pinnings

The three nullary constructors are fixed points of `dual`.
`rfl` discharges directly via unfolding of the pattern
equations. -/

example : dual .endS      = .endS      := rfl
example : dual .stop      = .stop      := rfl
example : dual .continueS = .continueS := rfl

/-! ### Head-constructor swap pinnings

A short name for the top-level constructor of a session
type.  Equality on strings is decidable, so `native_decide`
discharges head-constructor-swap checks against concrete
dual outputs without needing `DecidableEq` on payloads or
full structural equality on `SessionType`.  Structural
equality comes with stage S5's `sessionTypeBeq`. -/

def headName : SessionType → String
  | .endS       => "endS"
  | .stop       => "stop"
  | .send _ _   => "send"
  | .recv _ _   => "recv"
  | .selectS _  => "selectS"
  | .offerS _   => "offerS"
  | .loopS _    => "loopS"
  | .continueS  => "continueS"

-- `dual` swaps send and recv at the head.
example :
    headName (dual (.send (Term.ind "X" []) .endS)) = "recv" := by
  native_decide

example :
    headName (dual (.recv (Term.ind "X" []) .endS)) = "send" := by
  native_decide

-- `dual` swaps selectS and offerS at the head.
example : headName (dual (.selectS [])) = "offerS" := by native_decide
example : headName (dual (.offerS  [])) = "selectS" := by native_decide

-- `dual` preserves loopS and the nullary leaves at the head.
example : headName (dual (.loopS .continueS)) = "loopS"    := by native_decide
example : headName (dual .endS)               = "endS"     := by native_decide
example : headName (dual .stop)               = "stop"     := by native_decide
example : headName (dual .continueS)          = "continueS" := by native_decide

/-! ### Canonical-example pinnings

Each paired (client, server) example from the canonical
catalog is pinned by head-swap: dualizing the client's head
produces the server's head constructor, and dualizing its
outermost continuation's head flips in the expected way.
Full structural pinning of `dual client = server` lives
with stage S3's `dual_dual` proof, which generalizes the
individual-example pins into the involutivity theorem. -/

-- requestResponseOnce begins with a send; its dual begins
-- with recv.
example : headName (dual requestResponseOnce) = "recv" := by native_decide

-- requestResponseLoopClient begins with loopS (preserved),
-- and unwrapping one level shows the send/recv swap.
example : headName (dual requestResponseLoopClient) = "loopS" := by native_decide

-- authClient begins with send; authServer begins with recv.
-- dual authClient should have a recv head.
example : headName (dual authClient) = "recv" := by native_decide

-- streamReader is a loop offering branches; dualizing
-- preserves the loop head and flips offerS to selectS at
-- the next level, matching streamWriter's shape.
example : headName (dual streamReader) = "loopS" := by native_decide

/-! ### Branch-list pinnings

`dualBranches` preserves labels and dualizes each body.
Empty in, empty out.  Non-empty cases are pinned via
length preservation since full structural equality
requires stage S5's decidable-equality analogue. -/

example : dualBranches ([] : List (Label × SessionType)) = [] := rfl

-- Length is preserved.
example :
    (dualBranches [("ok", .endS), ("bye", .endS)]).length
      = 2 := by native_decide

-- Labels are preserved verbatim.
example :
    (dualBranches [("ok", .endS), ("bye", .endS)]).map Prod.fst
      = ["ok", "bye"] := by native_decide

/-! ## Duality is involutive (§11.2, S3)

Honda 1998's central result mechanized for FX:
`dual (dual T) = T` for every session type `T`.  Proved by
structural induction on `T`, mutual with a branch-list
involutivity lemma.  The theorem is the equational
upgrade of the head-swap pinnings established in stage S2:
where S2's examples confirmed duality inverts the head
constructor on concrete inputs, `dual_dual` establishes
full structural equality of the round-trip for every
session type.

The mutual form of the proof mirrors `dual`'s definitional
structure.  The `SessionType` half closes by reflexivity on
nullary constructors and by `change` + `rw` on compound
ones; the `List (Label × SessionType)` half closes
symmetrically on the list recursor, reusing the
`SessionType` theorem at the head and recursing on the
tail.

## Downstream consequences

  * Round-trip for every endpoint declaration: a channel's
    two endpoints satisfy `dual ∘ dual = id`, so stage S11's
    elaborator can treat `new_channel<P>()` as producing a
    canonically determined pair without an ambiguity check.
  * Injectivity: duality has no collisions, so any two
    session types agreeing on their duals are themselves
    equal.  Used later in subtyping and migration checks
    to propagate session-type identity through sessions
    carried as payloads (higher-order sessions, §11.23). -/

mutual

theorem dual_dual : ∀ (T : SessionType), dual (dual T) = T
  | .endS        => rfl
  | .stop        => rfl
  | .send P K    => by
    change SessionType.send P (dual (dual K)) = SessionType.send P K
    rw [dual_dual K]
  | .recv P K    => by
    change SessionType.recv P (dual (dual K)) = SessionType.recv P K
    rw [dual_dual K]
  | .selectS bs  => by
    change SessionType.selectS (dualBranches (dualBranches bs))
        = SessionType.selectS bs
    rw [dualBranches_involutive bs]
  | .offerS bs   => by
    change SessionType.offerS (dualBranches (dualBranches bs))
        = SessionType.offerS bs
    rw [dualBranches_involutive bs]
  | .loopS body  => by
    change SessionType.loopS (dual (dual body)) = SessionType.loopS body
    rw [dual_dual body]
  | .continueS   => rfl

theorem dualBranches_involutive :
    ∀ (bs : List (Label × SessionType)),
      dualBranches (dualBranches bs) = bs
  | []                    => rfl
  | (label, body) :: rest => by
    change (label, dual (dual body)) :: dualBranches (dualBranches rest)
        = (label, body) :: rest
    rw [dual_dual body, dualBranches_involutive rest]

end

/-! ### Canonical-example round-trips

Every canonical example from §S1 round-trips via its dual.
These are immediate applications of `dual_dual` and confirm
that the theorem discharges as expected on concrete
session types with payload references, loop/continue
bindings, and multi-branch choice. -/

example : dual (dual requestResponseOnce)       = requestResponseOnce       := dual_dual _
example : dual (dual requestResponseLoopClient) = requestResponseLoopClient := dual_dual _
example : dual (dual requestResponseLoopServer) = requestResponseLoopServer := dual_dual _
example : dual (dual authClient)                = authClient                := dual_dual _
example : dual (dual authServer)                = authServer                := dual_dual _
example : dual (dual streamReader)              = streamReader              := dual_dual _
example : dual (dual streamWriter)              = streamWriter              := dual_dual _

/-- Duality is injective on session types: if two session
    types have the same dual, they are equal.  Proof
    applies `dual` to both sides of `h`, then rewrites via
    `dual_dual` on each to strip the outer duals. -/
theorem dual_injective {T₁ T₂ : SessionType}
    (h : dual T₁ = dual T₂) : T₁ = T₂ := by
  have step : dual (dual T₁) = dual (dual T₂) := congrArg dual h
  rw [dual_dual T₁, dual_dual T₂] at step
  exact step

/-! ## Well-formedness (§11.14, S4)

A session type is well-formed when two syntactic
conditions hold: every `continueS` appears inside an
enclosing `loopS`, and every `selectS` / `offerS` has
pairwise-distinct branch labels.  The balanced+ condition
from WF-3 of §11.14 is a composition-site check and lands
with stage S18; WF-1 (guardedness) and WF-2 (label
distinctness) are the local checks covered here.

Guardedness is tracked by a `depth` counter that starts at
zero for top-level session types and increments on every
traversal through `loopS`.  A bare `continueS` is
well-formed precisely when `depth > 0` — at least one
enclosing loop is in scope to bind it.

Label distinctness is independent of branch bodies, so it
factors through the label-only projection.  This gives a
one-line proof that duality preserves distinctness:
`dualBranches` leaves the labels verbatim, so
`(dualBranches bs).map Prod.fst = bs.map Prod.fst`.

`wellFormed_dual : wellFormed (dual T) = wellFormed T` is
the load-bearing soundness theorem for stage S12's
`new_channel<P>()` primitive.  The primitive mints both
endpoints of a channel from a single well-formed session
declaration; with `wellFormed_dual` in hand the compiler
can treat both minted endpoints as satisfying the same
surface contract. -/

/-- Check that every label in a list of labels is distinct
    from every later occurrence.  Operates on labels alone
    so downstream theorems can reduce branch-list
    preservation to label-list preservation. -/
def labelsDistinct : List Label → Bool
  | []        => true
  | l :: rest => !rest.contains l && labelsDistinct rest

/-- A branch list has pairwise-distinct labels.  Factored
    as `labelsDistinct` on the label projection so
    `distinctLabels_dualBranches` closes by rewriting with
    `labelsOf_dualBranches`. -/
def distinctLabels (bs : List (Label × SessionType)) : Bool :=
  labelsDistinct (bs.map Prod.fst)

mutual

/-- Walk a session type checking guarded recursion and
    per-choice label distinctness.  `depth` counts
    enclosing `loopS` binders in scope. -/
def wellFormedAt (depth : Nat) : SessionType → Bool
  | .endS       => true
  | .stop       => true
  | .send _ K   => wellFormedAt depth K
  | .recv _ K   => wellFormedAt depth K
  | .selectS bs =>
    distinctLabels bs && wellFormedAtBranches depth bs
  | .offerS bs  =>
    distinctLabels bs && wellFormedAtBranches depth bs
  | .loopS body => wellFormedAt (depth + 1) body
  | .continueS  => depth != 0

/-- Walk a branch list checking each body's well-formedness
    at the enclosing depth.  Distinct-label checking is
    handled by `distinctLabels` at the call site, not here. -/
def wellFormedAtBranches (depth : Nat)
    : List (Label × SessionType) → Bool
  | []               => true
  | (_, body) :: rest =>
    wellFormedAt depth body && wellFormedAtBranches depth rest

end

/-- Top-level well-formedness: the session type is checked
    with no enclosing loop in scope, so a top-level
    `continueS` is rejected. -/
def wellFormed (T : SessionType) : Bool := wellFormedAt 0 T

/-! ### Well-formedness failure reason (S24)

The boolean `wellFormed` check collapses two distinct
failure modes — unguarded `continueS` (§11.27 S001) and
duplicate branch/select labels (§11.27 S002) — into one
result.  Downstream error emission needs the specific code
so consumers can emit the right diagnostic per the §11.27
taxonomy.

`WellFormedFailure` is the minimal discriminant; concrete
labels are intentionally elided (the elaborator surfaces the
failing spec name in its diagnostic message, which together
with the code points the reader at the right spot). -/

/-- The specific reason a session type failed well-formedness.
    Used by `elabSessionDeclSpec` to pick the right S-code
    per §11.27. -/
inductive WellFormedFailure where
  /-- `continueS` appears outside any enclosing `loopS` —
      §11.27 S001. -/
  | unguardedContinue : WellFormedFailure
  /-- `selectS` or `offerS` has two branches with the same
      label — §11.27 S002. -/
  | duplicateLabel    : WellFormedFailure
  deriving Repr, Inhabited, DecidableEq

mutual

/-- Walk a session type returning the first well-formedness
    failure encountered, or `none` if the session is
    well-formed.  Mirrors `wellFormedAt` but carries the
    specific failure reason instead of a boolean. -/
def wellFormedReasonAt (depth : Nat)
    : SessionType → Option WellFormedFailure
  | .endS       => none
  | .stop       => none
  | .send _ K   => wellFormedReasonAt depth K
  | .recv _ K   => wellFormedReasonAt depth K
  | .selectS bs =>
    if !distinctLabels bs then some .duplicateLabel
    else wellFormedReasonAtBranches depth bs
  | .offerS bs  =>
    if !distinctLabels bs then some .duplicateLabel
    else wellFormedReasonAtBranches depth bs
  | .loopS body => wellFormedReasonAt (depth + 1) body
  | .continueS  =>
    if depth == 0 then some .unguardedContinue else none

def wellFormedReasonAtBranches (depth : Nat)
    : List (Label × SessionType) → Option WellFormedFailure
  | []                => none
  | (_, body) :: rest =>
    match wellFormedReasonAt depth body with
    | some reason => some reason
    | none        => wellFormedReasonAtBranches depth rest

end

/-- Top-level reason-returning well-formedness check.  `none`
    iff the session is well-formed. -/
def wellFormedReason (T : SessionType)
    : Option WellFormedFailure :=
  wellFormedReasonAt 0 T

/-! ### Reason-check matches boolean-check on canonical examples -/

example : wellFormedReason requestResponseOnce       = none := by native_decide
example : wellFormedReason streamReader              = none := by native_decide
example : wellFormedReason .continueS =
    some WellFormedFailure.unguardedContinue := by native_decide
example : wellFormedReason
    (.selectS [("dup", .endS), ("dup", .endS)]) =
    some WellFormedFailure.duplicateLabel := by native_decide

/-! ### Canonical examples are well-formed -/

example : wellFormed requestResponseOnce       = true := by native_decide
example : wellFormed requestResponseLoopClient = true := by native_decide
example : wellFormed requestResponseLoopServer = true := by native_decide
example : wellFormed authClient                = true := by native_decide
example : wellFormed authServer                = true := by native_decide
example : wellFormed streamReader              = true := by native_decide
example : wellFormed streamWriter              = true := by native_decide

/-! ### Ill-formed examples are rejected

Regression witnesses: a bare `continueS` at the top level
and a `selectS` with duplicate labels are both rejected. -/

example : wellFormed .continueS = false := by native_decide

example :
    wellFormed (.selectS [("dup", .endS), ("dup", .endS)])
      = false := by
  native_decide

example :
    wellFormed (.loopS (.send (Term.ind "X" []) .continueS))
      = true := by
  native_decide

/-! ### Duality preserves well-formedness -/

/-- Dualizing a branch list preserves the list of labels.
    The proof is structural induction on the branch list:
    `dualBranches` rewrites the body while leaving the label
    in place. -/
theorem labelsOf_dualBranches :
    ∀ (bs : List (Label × SessionType)),
      (dualBranches bs).map Prod.fst = bs.map Prod.fst
  | []                    => rfl
  | (label, _body) :: rest => by
    change label :: (dualBranches rest).map Prod.fst
         = label :: rest.map Prod.fst
    rw [labelsOf_dualBranches rest]

/-- Dualizing a branch list preserves label distinctness.
    Immediate consequence of `labelsOf_dualBranches`:
    `distinctLabels` only inspects the label projection. -/
theorem distinctLabels_dualBranches
    (bs : List (Label × SessionType)) :
    distinctLabels (dualBranches bs) = distinctLabels bs := by
  unfold distinctLabels
  rw [labelsOf_dualBranches]

mutual

/-- Duality preserves well-formedness: `dual` and
    `wellFormedAt` commute on every session type.  Proved
    by structural induction on `T`, mutual with
    `wellFormedAtBranches_dual`.  Nullary leaves are rfl;
    send/recv reduce to a single IH application;
    select/offer rewrite using `distinctLabels_dualBranches`
    plus the mutual branch-list companion; loopS recurses
    at a bumped depth. -/
theorem wellFormedAt_dual : ∀ (d : Nat) (T : SessionType),
    wellFormedAt d (dual T) = wellFormedAt d T
  | _, .endS       => rfl
  | _, .stop       => rfl
  | d, .send _ K   => by
    change wellFormedAt d (dual K) = wellFormedAt d K
    exact wellFormedAt_dual d K
  | d, .recv _ K   => by
    change wellFormedAt d (dual K) = wellFormedAt d K
    exact wellFormedAt_dual d K
  | d, .selectS bs => by
    change (distinctLabels (dualBranches bs)
              && wellFormedAtBranches d (dualBranches bs))
         = (distinctLabels bs && wellFormedAtBranches d bs)
    rw [distinctLabels_dualBranches bs,
        wellFormedAtBranches_dual d bs]
  | d, .offerS bs  => by
    change (distinctLabels (dualBranches bs)
              && wellFormedAtBranches d (dualBranches bs))
         = (distinctLabels bs && wellFormedAtBranches d bs)
    rw [distinctLabels_dualBranches bs,
        wellFormedAtBranches_dual d bs]
  | d, .loopS body => by
    change wellFormedAt (d + 1) (dual body) = wellFormedAt (d + 1) body
    exact wellFormedAt_dual (d + 1) body
  | _, .continueS  => rfl

/-- Mutual companion: branch-list duality preserves
    well-formedness of every body.  Body cases go through
    `wellFormedAt_dual`; the list tail closes by recursion. -/
theorem wellFormedAtBranches_dual :
    ∀ (d : Nat) (bs : List (Label × SessionType)),
      wellFormedAtBranches d (dualBranches bs)
        = wellFormedAtBranches d bs
  | _, []                   => rfl
  | d, (_, body) :: rest => by
    change (wellFormedAt d (dual body)
              && wellFormedAtBranches d (dualBranches rest))
         = (wellFormedAt d body && wellFormedAtBranches d rest)
    rw [wellFormedAt_dual d body,
        wellFormedAtBranches_dual d rest]

end

/-- Top-level corollary: a session type is well-formed
    exactly when its dual is well-formed.  Zero depth
    version of `wellFormedAt_dual`. -/
theorem wellFormed_dual (T : SessionType) :
    wellFormed (dual T) = wellFormed T :=
  wellFormedAt_dual 0 T

-- Canonical-example pins: each well-formed client's dual
-- (the corresponding server) is also well-formed, and the
-- equality goes through `wellFormed_dual` directly.
example : wellFormed (dual requestResponseLoopClient) = true := by
  rw [wellFormed_dual]; native_decide

example : wellFormed (dual authClient) = true := by
  rw [wellFormed_dual]; native_decide

example : wellFormed (dual streamReader) = true := by
  rw [wellFormed_dual]; native_decide

/-! ## Synchronous subtyping — Gay-Hole 2005 (§11.19, S5)

Subtyping captures safe substitution: if `T₁ ⩽ T₂`, then a
`T₂`-typed participant can be replaced by a `T₁`-typed one
without violating protocol correctness.  The relation is the
heart of protocol evolution (`refines` in §15.4) and of the
refinement of abstract session specifications into concrete
implementations.

The six Gay-Hole 2005 structural rules under rendezvous
semantics:

```
 end  ⩽  end                                   (nullary reflexive)

 stop ⩽  T                (for every T)        (bottom — crashed endpoint
                                                 vacuously inhabits anything;
                                                 BSYZ22 crash-stop rule)

 continue ⩽ continue                           (guarded recursion reference)

 send P₁ K₁ ⩽ send P₂ K₂    when P₁ ≈ P₂ and K₁ ⩽ K₂
                                                (covariant payload + continuation;
                                                 see note on payload comparison
                                                 below)

 recv P₁ K₁ ⩽ recv P₂ K₂    when P₁ ≈ P₂ and K₁ ⩽ K₂
                                                (contravariant payload per §11.19,
                                                 but equality is the sound
                                                 under-approximation used here)

 select B₁  ⩽ select B₂     when every branch in B₁ has a matching
                                                 branch in B₂ with subtype body
                                                (sub has ⊆ labels — narrower choice)

 offer B₁   ⩽ offer B₂      when every branch in B₂ has a matching
                                                 branch in B₁ with subtype body
                                                (sub has ⊇ labels — broader offer)

 loop K₁    ⩽ loop K₂       when K₁ ⩽ K₂
```

### Payload comparison

The Gay-Hole rule makes `send` payloads covariant and
`recv` payloads contravariant on the payload's base type.
A full-fidelity implementation would invoke the kernel's
`Term` subtyping relation (`FX/Kernel/Subtyping.lean`) at
each payload check.  The first landing uses `Term.structEq`
— structural equality — which is a sound
under-approximation: syntactically equal payloads are
always subtypes in both directions, so both covariant and
contravariant sites are satisfied.  Sessions with
distinct-but-compatible payload types (e.g. `send<u8>` vs
`send<nat { x < 256 }>`) do not currently discharge through
`subtypeSync`; stage S22's contract bridge will route
payloads through `Term` subtyping when the full relation is
required.

### Fuel-bounded recursion

The relation is decidable for guarded recursion but its
natural definition is coinductive.  Rather than memoize
visited pairs, `subtypeSync` carries an explicit fuel
counter that decrements at every structural step.  The
default fuel is 64, matching stage S21's SISO async
bound.  Depth-exhausted checks return `false` and trigger
error S017 diagnostic at the elaborator level.  Callers
demanding a deeper check pass a larger fuel explicitly or
switch to the precise async relation of §11.20.

This file uses `partial def` for `subtypeSync` because the
natural termination measure — lexicographic fuel-plus-list
— is not structural over a single argument, and the
proof-level termination obligation is not load-bearing for
soundness (the function returns a bounded-cost `Bool` that
elaboration layer validates).  The precedent is
`Term.structEq`, which is also a `partial def` over the
kernel's inductive term type.  Stage S21 will mechanize
termination when the precise-async relation is introduced
alongside its unique-soundness theorem. -/

/-- Look up a branch body by label in a list of labelled
    continuations.  Returns `none` when the label is
    absent.  Used by `subtypeSync` at `selectS` and
    `offerS` cases to check that every required label has
    a matching continuation. -/
def findBranch (needle : Label)
    : List (Label × SessionType) → Option SessionType
  | [] => none
  | (label, body) :: rest =>
    if label == needle then some body else findBranch needle rest

mutual

/-- Decide synchronous subtyping `T₁ ⩽ T₂` per Gay-Hole 2005
    §11.19, bounded by `fuel` structural steps.  Exhausted
    fuel rejects (conservative).  `.stop` matches first and
    wins against any right-hand side — the crash-stop
    bottom rule.  The payload check uses `Term.structEq`
    as a sound under-approximation (see module docstring).
    See `defaultSubtypeFuel` / `subtypeSyncDefault` for the
    64-fuel convenience wrapper.  Mutual with
    `branchesCovered` over the branch-list payloads of
    `selectS` and `offerS`. -/
partial def subtypeSync : Nat → SessionType → SessionType → Bool
  | _, .stop, _                          => true
  | 0, _, _                               => false
  | _ + 1, .endS, .endS                  => true
  | _ + 1, .continueS, .continueS        => true
  | fuel + 1, .send payload₁ cont₁, .send payload₂ cont₂ =>
      Term.structEq payload₁ payload₂ && subtypeSync fuel cont₁ cont₂
  | fuel + 1, .recv payload₁ cont₁, .recv payload₂ cont₂ =>
      Term.structEq payload₁ payload₂ && subtypeSync fuel cont₁ cont₂
  | fuel + 1, .selectS subBranches, .selectS superBranches =>
      branchesCovered fuel subBranches superBranches
  | fuel + 1, .offerS subBranches, .offerS superBranches =>
      branchesCovered fuel superBranches subBranches
  | fuel + 1, .loopS body₁, .loopS body₂ =>
      subtypeSync fuel body₁ body₂
  | _, _, _                               => false

/-- Auxiliary: every branch in `narrower` has a matching
    branch in `wider` with a subtype body (checked via
    `subtypeSync`).  Used by both the `selectS` arm (sub
    narrower, super wider) and the `offerS` arm (super
    narrower, sub wider — arguments flipped at the call
    site).  Rejects when a label is missing from `wider`
    or when matched continuations are not in the subtype
    relation.  Mutual with `subtypeSync`. -/
partial def branchesCovered (fuel : Nat)
    : List (Label × SessionType) → List (Label × SessionType) → Bool
  | [], _ => true
  | (label, body) :: rest, wider =>
    match findBranch label wider with
    | some widerBody => subtypeSync fuel body widerBody
                     && branchesCovered fuel rest wider
    | none => false

end

/-- Default fuel for `subtypeSync`: 64 structural steps.
    Matches the default SISO expansion depth used by
    stage S21's precise async subtyping (§11.20), so
    switching between the synchronous and asynchronous
    relations does not surprise users with disparate
    depth bounds. -/
def defaultSubtypeFuel : Nat := 64

/-- Convenience wrapper calling `subtypeSync` at
    `defaultSubtypeFuel`.  Most call sites want this. -/
def subtypeSyncDefault (sub super : SessionType) : Bool :=
  subtypeSync defaultSubtypeFuel sub super

/-! ### Pinning examples — `stop` is the bottom

Every canonical session type is a super of `stop` at
every fuel.  This is the Gay-Hole crash-stop rule: a
crashed endpoint satisfies any remaining protocol
obligation because it will not observe further events. -/

example : subtypeSync 0 .stop .endS = true := by native_decide
example : subtypeSync 0 .stop requestResponseOnce = true := by native_decide
example : subtypeSync 0 .stop authClient = true := by native_decide
example : subtypeSync 0 .stop streamReader = true := by native_decide

example : subtypeSyncDefault .stop .endS = true := by native_decide
example : subtypeSyncDefault .stop requestResponseOnce = true := by native_decide
example : subtypeSyncDefault .stop streamWriter = true := by native_decide

/-! ### Reflexivity on the canonical examples

Every canonical example is a subtype of itself at
`defaultSubtypeFuel`.  Reflexivity holds in general up to
the fuel bound — these pins exercise that on concrete
structures with send/recv, loop, select, and offer. -/

example : subtypeSyncDefault requestResponseOnce requestResponseOnce = true := by
  native_decide
example :
    subtypeSyncDefault requestResponseLoopClient requestResponseLoopClient
      = true := by
  native_decide
example : subtypeSyncDefault authClient authClient = true := by
  native_decide
example : subtypeSyncDefault authServer authServer = true := by
  native_decide
example : subtypeSyncDefault streamReader streamReader = true := by
  native_decide
example : subtypeSyncDefault streamWriter streamWriter = true := by
  native_decide

/-! ### Select narrowing — fewer labels on the sub side

`select { a => ... }` is a subtype of `select { a => ...,
b => ... }`: the sub chooses from a narrower menu than
the super offers.  The subtype has ⊆ labels of the super. -/

example :
    subtypeSyncDefault
      (.selectS [("go", .endS)])
      (.selectS [("go", .endS), ("wait", .endS)])
      = true := by
  native_decide

-- Adding a label to the subtype's menu is NOT a subtype:
-- the subtype cannot choose a label the super does not
-- know how to receive.
example :
    subtypeSyncDefault
      (.selectS [("go", .endS), ("unknown", .endS)])
      (.selectS [("go", .endS)])
      = false := by
  native_decide

/-! ### Offer widening — more labels on the sub side

`offer { a => ..., b => ... }` is a subtype of
`offer { a => ... }`: the sub handles every label the super
does plus extras.  The subtype has ⊇ labels of the super. -/

example :
    subtypeSyncDefault
      (.offerS [("a", .endS), ("b", .endS)])
      (.offerS [("a", .endS)])
      = true := by
  native_decide

-- Removing a label the super expects handled is NOT a
-- subtype: a super-typed peer could send the missing
-- label and the sub has no branch for it.
example :
    subtypeSyncDefault
      (.offerS [("a", .endS)])
      (.offerS [("a", .endS), ("b", .endS)])
      = false := by
  native_decide

/-! ### Payload-equality rejection

The current implementation requires payload types to be
syntactically equal (see module docstring).  A `send u8`
is not a subtype of `send nat` under `subtypeSync` — a
full-fidelity check against kernel `Term` subtyping lands
with stage S22. -/

example :
    subtypeSyncDefault
      (.send (Term.ind "u8" []) .endS)
      (.send (Term.ind "nat" []) .endS)
      = false := by
  native_decide

example :
    subtypeSyncDefault
      (.recv (Term.ind "u8" []) .endS)
      (.recv (Term.ind "nat" []) .endS)
      = false := by
  native_decide

/-! ### Loop body subtyping

`loop K₁ ⩽ loop K₂` iff `K₁ ⩽ K₂`.  Narrowing under a
`loop` carries through unchanged. -/

example :
    subtypeSyncDefault
      (.loopS (.selectS [("a", .continueS)]))
      (.loopS (.selectS [("a", .continueS), ("b", .endS)]))
      = true := by
  native_decide

-- The dual relationship does not hold at loop body level
-- — widening a select inside a loop is NOT a subtype.
example :
    subtypeSyncDefault
      (.loopS (.selectS [("a", .continueS), ("b", .endS)]))
      (.loopS (.selectS [("a", .continueS)]))
      = false := by
  native_decide

/-! ### Exhausted fuel rejects conservatively

At fuel=0 and sub≠.stop, the check conservatively rejects
regardless of whether the pair is actually in the
relation.  Soundness is preserved (no unsafe program is
accepted); completeness is sacrificed (some safe programs
need more fuel).  Users raising `@[subtype_depth(N)]` on
the session declaration supply a larger value. -/

example : subtypeSync 0 .endS .endS = false := by native_decide
example : subtypeSync 1 .endS .endS = true := by native_decide

-- Deeply-nested subtyping requires fuel proportional to
-- the structural depth.  Nine-level continue chain needs
-- at least 9 fuel; 8 fuel rejects.
example :
    subtypeSync 2
      (.send (Term.ind "T" []) (.send (Term.ind "T" []) .endS))
      (.send (Term.ind "T" []) (.send (Term.ind "T" []) .endS))
      = false := by
  -- fuel=2 rejects because two `send` cost 2 fuel plus one step for
  -- the .endS match — so total structural depth 3 exceeds 2.
  native_decide

example :
    subtypeSync 3
      (.send (Term.ind "T" []) (.send (Term.ind "T" []) .endS))
      (.send (Term.ind "T" []) (.send (Term.ind "T" []) .endS))
      = true := by
  native_decide

end SessionType

end FX.Derived.Session
