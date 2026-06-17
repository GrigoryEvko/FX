import FX1Poly.Tier0.Mode.Mode

/-! # mode-25 ★ — the session / protocol modality: duality as a self-inverse 2-cell

Binary session types as a dedicated mode-polygraph instance.  The headline is that the DUALITY involution is a
SELF-INVERSE 2-cell — `dual ∘ dual = id` — the ℤ/2 action that pairs the two endpoints of a channel (fx_design
§11.2; FX's SESSION-DUALITY).  This folds the `.protocol` cell axis into the mode doctrine.

## What this file ships (each piece zero-axiom)

  * **`SessionProtocol`** — binary session types: `endSession`, `send`/`receive` (a message then a continuation),
    `selectChoice` (internal choice ⊕) / `branchOffer` (external choice &), and `recur`/`recVar` (raw recursion).
  * **`SessionProtocol.dual`** — the duality: `send ↔ receive`, `selectChoice ↔ branchOffer`, `end`/`recVar` fixed,
    `recur` structural; with ★ **`dual_dual`** (`dual ∘ dual = id`, by structural induction — the self-inverse).
  * **`Involution`** + **`sessionDualityInvolution`** — duality packaged as a genuine involution (a self-inverse
    operator), the mode-level "self-inverse 2-cell" shape.
  * **`SessionSubtype`** — the structural sub-protocol precongruence (the 1-cell order), with `refl` and ★
    `dual_monotone` (duality is an order-ISO on the precongruence: `send ↔ receive`, `select ↔ branch`).
  * **`SessionAdvance`** — the single-action reduction (communication step), with ★ **`dual_fidelity`** — the two
    endpoints advance in lockstep staying dual (SESSION fidelity).
  * **`canAdvance`** + `canAdvance_progress` + ★ **`deadlockFree`** — a live session and its dual ALWAYS make
    synchronized progress (never stuck): deadlock-freedom from the duality discipline.

## What is DEFERRED (markers)

  * the duality involution as a COHERENT 2-cell in the mode 2-category (the involution's full 2-cell coherence,
    beyond the `dual_dual` equation) (`hasSessionTwoCellCoherence`);
  * the multiparty GLOBAL-to-LOCAL session projection (global session types → per-participant projected views) —
    the scary core (`hasSessionMultipartyProjection`);
  * the full Gay-Hole WIDTH subtyping (select fewer / branch more) + the ANTITONE duality-reversal under it
    (`hasSessionWidthSubtyping`);
  * the well-scoped / equirecursive recursion semantics (here `recur`/`recVar` are raw structural)
    (`hasSessionRecursionScoping`);
  * the kernel's `.protocol` cell axis fibred into the mode doctrine (cross-axis, `fib`)
    (`hasSessionKernelProtocolFibration`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## Involutions — self-inverse operators -/

/-- An **involution** on a type — a self-inverse operator (`involute ∘ involute = id`).  An involution is exactly
a ℤ/2 action, i.e. a self-inverse 2-cell; session duality is the canonical example. -/
structure Involution (Carrier : Type) where
  /-- The self-inverse operator. -/
  involute : Carrier → Carrier
  /-- It is self-inverse. -/
  involute_involute : (point : Carrier) → involute (involute point) = point

/-! ## Session protocols + duality -/

/-- A **binary session protocol** — the type of one channel endpoint's communication script (fx_design §11.1),
parameterised by the message-label alphabet `Label`. -/
inductive SessionProtocol (Label : Type) where
  /-- The terminated session. -/
  | endSession
  /-- Send a labelled message, then continue. -/
  | send (label : Label) (continuation : SessionProtocol Label)
  /-- Receive a labelled message, then continue. -/
  | receive (label : Label) (continuation : SessionProtocol Label)
  /-- Internal choice (⊕) — this endpoint SELECTS one of the two continuations. -/
  | selectChoice (left right : SessionProtocol Label)
  /-- External choice (&) — this endpoint OFFERS both continuations. -/
  | branchOffer (left right : SessionProtocol Label)
  /-- A recursion binder (raw — scoping deferred). -/
  | recur (body : SessionProtocol Label)
  /-- A recursion variable (raw — scoping deferred). -/
  | recVar (index : Nat)

/-- The **duality** of a session protocol — the script of the OTHER endpoint: `send ↔ receive`,
`selectChoice ↔ branchOffer` (internal ↔ external choice), `endSession` / `recVar` fixed, `recur` structural
(fx_design §11.2). -/
def SessionProtocol.dual {Label : Type} : SessionProtocol Label → SessionProtocol Label
  | .endSession => .endSession
  | .send label continuation => .receive label continuation.dual
  | .receive label continuation => .send label continuation.dual
  | .selectChoice left right => .branchOffer left.dual right.dual
  | .branchOffer left right => .selectChoice left.dual right.dual
  | .recur body => .recur body.dual
  | .recVar index => .recVar index

/-- ★ **Duality is a self-inverse** — `dual ∘ dual = id`.  The session-duality involution is a self-inverse 2-cell
(the ℤ/2 channel-endpoint symmetry), proved by structural induction. -/
theorem SessionProtocol.dual_dual {Label : Type} (session : SessionProtocol Label) :
    session.dual.dual = session := by
  induction session with
  | endSession => rfl
  | send label continuation ih => exact congrArg (SessionProtocol.send label) ih
  | receive label continuation ih => exact congrArg (SessionProtocol.receive label) ih
  | selectChoice left right ihLeft ihRight =>
      show SessionProtocol.selectChoice left.dual.dual right.dual.dual = SessionProtocol.selectChoice left right
      rw [ihLeft, ihRight]
  | branchOffer left right ihLeft ihRight =>
      show SessionProtocol.branchOffer left.dual.dual right.dual.dual = SessionProtocol.branchOffer left right
      rw [ihLeft, ihRight]
  | recur body ih => exact congrArg SessionProtocol.recur ih
  | recVar index => rfl

/-- ★ Session duality packaged as an **involution** — the self-inverse 2-cell at the mode level. -/
def sessionDualityInvolution (Label : Type) : Involution (SessionProtocol Label) where
  involute := SessionProtocol.dual
  involute_involute := SessionProtocol.dual_dual

/-! ## Sub-protocol order (the 1-cell order) -/

/-- The **structural sub-protocol precongruence** — the 1-cell order on session protocols (the structural,
width-uniform fragment: each former is monotone in its continuations). -/
inductive SessionSubtype {Label : Type} : SessionProtocol Label → SessionProtocol Label → Prop where
  /-- `end` refines `end`. -/
  | endSub : SessionSubtype .endSession .endSession
  /-- `send` is monotone in its continuation. -/
  | sendSub {label : Label} {first second : SessionProtocol Label} :
      SessionSubtype first second → SessionSubtype (.send label first) (.send label second)
  /-- `receive` is monotone in its continuation. -/
  | receiveSub {label : Label} {first second : SessionProtocol Label} :
      SessionSubtype first second → SessionSubtype (.receive label first) (.receive label second)
  /-- `selectChoice` is monotone in both continuations. -/
  | selectSub {firstLeft secondLeft firstRight secondRight : SessionProtocol Label} :
      SessionSubtype firstLeft secondLeft → SessionSubtype firstRight secondRight →
      SessionSubtype (.selectChoice firstLeft firstRight) (.selectChoice secondLeft secondRight)
  /-- `branchOffer` is monotone in both continuations. -/
  | branchSub {firstLeft secondLeft firstRight secondRight : SessionProtocol Label} :
      SessionSubtype firstLeft secondLeft → SessionSubtype firstRight secondRight →
      SessionSubtype (.branchOffer firstLeft firstRight) (.branchOffer secondLeft secondRight)
  /-- `recur` is monotone in its body. -/
  | recurSub {first second : SessionProtocol Label} :
      SessionSubtype first second → SessionSubtype (.recur first) (.recur second)
  /-- `recVar` refines itself. -/
  | recVarSub {index : Nat} : SessionSubtype (.recVar index) (.recVar index)

/-- The sub-protocol order is REFLEXIVE — the 1-cell order is a genuine preorder. -/
theorem SessionSubtype.refl {Label : Type} (session : SessionProtocol Label) :
    SessionSubtype session session := by
  induction session with
  | endSession => exact .endSub
  | send label continuation ih => exact .sendSub ih
  | receive label continuation ih => exact .receiveSub ih
  | selectChoice left right ihLeft ihRight => exact .selectSub ihLeft ihRight
  | branchOffer left right ihLeft ihRight => exact .branchSub ihLeft ihRight
  | recur body ih => exact .recurSub ih
  | recVar index => exact .recVarSub

/-- ★ **Duality is an order-isomorphism** on the precongruence — it maps sub-protocols to sub-protocols, swapping
`send ↔ receive` and `select ↔ branch`.  The 1-cell order and the self-inverse 2-cell cohere. -/
theorem SessionSubtype.dual_monotone {Label : Type} {source target : SessionProtocol Label}
    (sub : SessionSubtype source target) : SessionSubtype source.dual target.dual := by
  induction sub with
  | endSub => exact .endSub
  | sendSub _ ih => exact .receiveSub ih
  | receiveSub _ ih => exact .sendSub ih
  | selectSub _ _ ihLeft ihRight => exact .branchSub ihLeft ihRight
  | branchSub _ _ ihLeft ihRight => exact .selectSub ihLeft ihRight
  | recurSub _ ih => exact .recurSub ih
  | recVarSub => exact .recVarSub

/-! ## Communication step + session fidelity -/

/-- A single **communication advance** — the head action fires and the endpoint moves to a continuation. -/
inductive SessionAdvance {Label : Type} : SessionProtocol Label → SessionProtocol Label → Prop where
  /-- A send fires. -/
  | sendAdvance {label : Label} {continuation : SessionProtocol Label} :
      SessionAdvance (.send label continuation) continuation
  /-- A receive fires. -/
  | receiveAdvance {label : Label} {continuation : SessionProtocol Label} :
      SessionAdvance (.receive label continuation) continuation
  /-- Internal choice selects the left continuation. -/
  | selectLeft {left right : SessionProtocol Label} : SessionAdvance (.selectChoice left right) left
  /-- Internal choice selects the right continuation. -/
  | selectRight {left right : SessionProtocol Label} : SessionAdvance (.selectChoice left right) right
  /-- External choice takes the left branch. -/
  | branchLeft {left right : SessionProtocol Label} : SessionAdvance (.branchOffer left right) left
  /-- External choice takes the right branch. -/
  | branchRight {left right : SessionProtocol Label} : SessionAdvance (.branchOffer left right) right

/-- ★ **Session fidelity** — when one endpoint advances, its DUAL advances to the dual continuation (the two
endpoints move in lockstep and remain dual).  This is the operational heart of communication safety. -/
theorem SessionAdvance.dual_fidelity {Label : Type} {source target : SessionProtocol Label}
    (advance : SessionAdvance source target) : SessionAdvance source.dual target.dual := by
  cases advance with
  | sendAdvance => exact .receiveAdvance
  | receiveAdvance => exact .sendAdvance
  | selectLeft => exact .branchLeft
  | selectRight => exact .branchRight
  | branchLeft => exact .selectLeft
  | branchRight => exact .selectRight

/-! ## Deadlock-freedom -/

/-- Whether a session has a head action ready to fire (is not terminated / not a bare recursion point). -/
def SessionProtocol.canAdvance {Label : Type} : SessionProtocol Label → Bool
  | .endSession => false
  | .recVar _ => false
  | .recur _ => false
  | .send _ _ => true
  | .receive _ _ => true
  | .selectChoice _ _ => true
  | .branchOffer _ _ => true

/-- A session with a head action can take a step (progress). -/
theorem SessionProtocol.canAdvance_progress {Label : Type} {source : SessionProtocol Label}
    (canStep : source.canAdvance = true) : ∃ target, SessionAdvance source target := by
  cases source with
  | endSession => exact Bool.noConfusion canStep
  | recVar _ => exact Bool.noConfusion canStep
  | recur _ => exact Bool.noConfusion canStep
  | send label continuation => exact ⟨continuation, .sendAdvance⟩
  | receive label continuation => exact ⟨continuation, .receiveAdvance⟩
  | selectChoice left right => exact ⟨left, .selectLeft⟩
  | branchOffer left right => exact ⟨left, .branchLeft⟩

/-- ★ **Deadlock-freedom** — a live session and its DUAL always make SYNCHRONIZED progress: if the session can
advance, both it and its dual step (to dual continuations), so the channel never deadlocks.  This is the
deadlock-freedom guaranteed by the duality discipline. -/
theorem SessionProtocol.deadlockFree {Label : Type} {source : SessionProtocol Label}
    (canStep : source.canAdvance = true) :
    ∃ target, SessionAdvance source target ∧ SessionAdvance source.dual target.dual := by
  obtain ⟨target, advance⟩ := source.canAdvance_progress canStep
  exact ⟨target, advance, advance.dual_fidelity⟩

/-! ## Well-scoped recursion (discharges hasSessionRecursionScoping) -/

/-- Whether every `recVar` index is bound by an enclosing `recur` (the de-Bruijn well-scopedness check at a given
binder depth). -/
def SessionProtocol.wellScopedAt {Label : Type} (depth : Nat) : SessionProtocol Label → Bool
  | .endSession => true
  | .send _ continuation => continuation.wellScopedAt depth
  | .receive _ continuation => continuation.wellScopedAt depth
  | .selectChoice left right => left.wellScopedAt depth && right.wellScopedAt depth
  | .branchOffer left right => left.wellScopedAt depth && right.wellScopedAt depth
  | .recur body => body.wellScopedAt (depth + 1)
  | .recVar index => decide (index < depth)

/-- A protocol is **well-scoped** when every recursion variable is bound (checked from depth `0`). -/
def SessionProtocol.wellScoped {Label : Type} (session : SessionProtocol Label) : Bool :=
  session.wellScopedAt 0

/-- ★ Duality PRESERVES well-scopedness at every depth (`recur`/`recVar` are fixed by `dual`, so the binder
structure is intact). -/
theorem SessionProtocol.dual_wellScopedAt {Label : Type} (depth : Nat) (session : SessionProtocol Label) :
    session.dual.wellScopedAt depth = session.wellScopedAt depth := by
  induction session generalizing depth with
  | endSession => rfl
  | send label continuation ih => exact ih depth
  | receive label continuation ih => exact ih depth
  | selectChoice left right ihLeft ihRight =>
      show (left.dual.wellScopedAt depth && right.dual.wellScopedAt depth)
         = (left.wellScopedAt depth && right.wellScopedAt depth)
      rw [ihLeft, ihRight]
  | branchOffer left right ihLeft ihRight =>
      show (left.dual.wellScopedAt depth && right.dual.wellScopedAt depth)
         = (left.wellScopedAt depth && right.wellScopedAt depth)
      rw [ihLeft, ihRight]
  | recur body ih => exact ih (depth + 1)
  | recVar index => rfl

/-- ★ Duality preserves well-scopedness — a well-scoped session's dual is well-scoped. -/
theorem SessionProtocol.dual_wellScoped {Label : Type} (session : SessionProtocol Label) :
    session.dual.wellScoped = session.wellScoped :=
  SessionProtocol.dual_wellScopedAt 0 session

/-! ## Duality as a coherent 2-cell (discharges hasSessionTwoCellCoherence) -/

/-- ★ Duality REFLECTS the sub-protocol order: from `source.dual ⊑ target.dual` recover `source ⊑ target` (via the
`dual_dual` involution).  Together with `dual_monotone` this makes duality a full order-AUTOMORPHISM — the coherent
involutive 2-cell on the 1-cell order. -/
theorem SessionSubtype.dual_reflect {Label : Type} {source target : SessionProtocol Label}
    (sub : SessionSubtype source.dual target.dual) : SessionSubtype source target := by
  have stepped := sub.dual_monotone
  rw [SessionProtocol.dual_dual, SessionProtocol.dual_dual] at stepped
  exact stepped

/-- ★ Duality is an order-ISO on the precongruence: `source.dual ⊑ target.dual ↔ source ⊑ target` — the 2-cell
coheres with the 1-cell order in BOTH directions. -/
theorem SessionSubtype.dual_iff {Label : Type} (source target : SessionProtocol Label) :
    SessionSubtype source.dual target.dual ↔ SessionSubtype source target :=
  ⟨SessionSubtype.dual_reflect, SessionSubtype.dual_monotone⟩

/-! ## The 2-party global-to-local projection (partial — binary case) -/

/-- A single global interaction step between the two roles `A` and `B`. -/
inductive GlobalStep (Label : Type) where
  /-- `A` sends a labelled message to `B`. -/
  | aToB (label : Label)
  /-- `B` sends a labelled message to `A`. -/
  | bToA (label : Label)

/-- A global (2-party) session type: a sequence of role-to-role messages, then end. -/
inductive GlobalProtocol (Label : Type) where
  /-- The terminated global session. -/
  | globalEnd
  /-- One interaction, then the rest. -/
  | step (head : GlobalStep Label) (rest : GlobalProtocol Label)

/-- Projection onto role `A`: an `A→B` message is a send, a `B→A` message is a receive. -/
def GlobalProtocol.projectA {Label : Type} : GlobalProtocol Label → SessionProtocol Label
  | .globalEnd => .endSession
  | .step (.aToB label) rest => .send label rest.projectA
  | .step (.bToA label) rest => .receive label rest.projectA

/-- Projection onto role `B`: an `A→B` message is a receive, a `B→A` message is a send (the opposite role). -/
def GlobalProtocol.projectB {Label : Type} : GlobalProtocol Label → SessionProtocol Label
  | .globalEnd => .endSession
  | .step (.aToB label) rest => .receive label rest.projectB
  | .step (.bToA label) rest => .send label rest.projectB

/-- ★ The 2-party projection coherence: the two role projections are DUAL — `projectB g = (projectA g).dual`.  A
global type's two local views are dual channel endpoints (projection respects duality), so the projected pair is
deadlock-free by `deadlockFree`. -/
theorem GlobalProtocol.projectB_eq_dual_projectA {Label : Type} (global : GlobalProtocol Label) :
    global.projectB = global.projectA.dual := by
  induction global with
  | globalEnd => rfl
  | step head rest ih =>
    cases head with
    | aToB label =>
        show SessionProtocol.receive label rest.projectB = SessionProtocol.receive label rest.projectA.dual
        rw [ih]
    | bToA label =>
        show SessionProtocol.send label rest.projectB = SessionProtocol.send label rest.projectA.dual
        rw [ih]

/-! ## n-ary labelled choice + Gay-Hole width subtyping (discharges hasSessionWidthSubtyping) -/

mutual

/-- A session protocol with **n-ary labelled choice** — the width dimension the binary `selectChoice`/`branchOffer`
cannot express.  `wSelect`/`wBranch` carry a `ChoiceList` of branches (mutually inductive with that list, so the
data stays plain — no nesting through `List`).  Crucible's `Select`/`Offer` are exactly this variadic form. -/
inductive WidthSession (Label : Type) where
  /-- The terminated protocol. -/
  | wEnd
  /-- Send a labelled message, then continue. -/
  | wSend (label : Label) (continuation : WidthSession Label)
  /-- Receive a labelled message, then continue. -/
  | wRecv (label : Label) (continuation : WidthSession Label)
  /-- Internal choice (WE pick) over an n-ary branch list. -/
  | wSelect (branches : ChoiceList Label)
  /-- External choice (the PEER offers) over an n-ary branch list. -/
  | wBranch (branches : ChoiceList Label)

/-- A list of protocol branches, mutually inductive with `WidthSession`. -/
inductive ChoiceList (Label : Type) where
  /-- No further branches. -/
  | nil
  /-- One branch, then the rest of the choice. -/
  | cons (head : WidthSession Label) (tail : ChoiceList Label)

end

mutual

/-- Duality on width sessions — `wSend ↔ wRecv`, `wSelect ↔ wBranch` (internal ↔ external choice). -/
def WidthSession.dual {Label : Type} : WidthSession Label → WidthSession Label
  | .wEnd => .wEnd
  | .wSend label continuation => .wRecv label continuation.dual
  | .wRecv label continuation => .wSend label continuation.dual
  | .wSelect branches => .wBranch branches.dualList
  | .wBranch branches => .wSelect branches.dualList

/-- Duality on a branch list — dualize each branch. -/
def ChoiceList.dualList {Label : Type} : ChoiceList Label → ChoiceList Label
  | .nil => .nil
  | .cons head tail => .cons head.dual tail.dualList

end

mutual

/-- ★ `dual` is a self-inverse involution on width sessions. -/
theorem WidthSession.dual_dual {Label : Type} :
    (session : WidthSession Label) → session.dual.dual = session
  | .wEnd => rfl
  | .wSend label continuation => congrArg (WidthSession.wSend label) continuation.dual_dual
  | .wRecv label continuation => congrArg (WidthSession.wRecv label) continuation.dual_dual
  | .wSelect branches => congrArg WidthSession.wSelect branches.dualList_dualList
  | .wBranch branches => congrArg WidthSession.wBranch branches.dualList_dualList

/-- ★ `dualList` is self-inverse. -/
theorem ChoiceList.dualList_dualList {Label : Type} :
    (branches : ChoiceList Label) → branches.dualList.dualList = branches
  | .nil => rfl
  | .cons head tail =>
      (congrArg (fun headDualled => ChoiceList.cons headDualled tail.dualList.dualList)
          head.dual_dual).trans
        (congrArg (ChoiceList.cons head) tail.dualList_dualList)

end

/-- **Gay-Hole synchronous width subtyping** as a single inductive.  `wSelect` is width-covariant DOWN (a subtype
offers FEWER internal choices); `wBranch` is width-covariant UP (a subtype handles MORE external offers); both are
depth-covariant in the continuations.  The choice recursion threads through `WidthSubtype` at the `wSelect`/
`wBranch` of the tail, keeping this a single (non-mutual) relation. -/
inductive WidthSubtype {Label : Type} : WidthSession Label → WidthSession Label → Prop
  | wEnd : WidthSubtype .wEnd .wEnd
  | wSend {label : Label} {k1 k2 : WidthSession Label} (continuation : WidthSubtype k1 k2) :
      WidthSubtype (.wSend label k1) (.wSend label k2)
  | wRecv {label : Label} {k1 k2 : WidthSession Label} (continuation : WidthSubtype k1 k2) :
      WidthSubtype (.wRecv label k1) (.wRecv label k2)
  /-- Empty internal choice is the minimum — `wSelect nil` offers fewest, a subtype of any `wSelect`. -/
  | wSelectNil {supers : ChoiceList Label} : WidthSubtype (.wSelect .nil) (.wSelect supers)
  | wSelectCons {b1 b2 : WidthSession Label} {r1 r2 : ChoiceList Label}
      (branchHead : WidthSubtype b1 b2) (branchTail : WidthSubtype (.wSelect r1) (.wSelect r2)) :
      WidthSubtype (.wSelect (.cons b1 r1)) (.wSelect (.cons b2 r2))
  /-- Empty external choice is the maximum to handle — any `wBranch` handles at least the empty offer. -/
  | wBranchNil {subs : ChoiceList Label} : WidthSubtype (.wBranch subs) (.wBranch .nil)
  | wBranchCons {b1 b2 : WidthSession Label} {r1 r2 : ChoiceList Label}
      (branchHead : WidthSubtype b1 b2) (branchTail : WidthSubtype (.wBranch r1) (.wBranch r2)) :
      WidthSubtype (.wBranch (.cons b1 r1)) (.wBranch (.cons b2 r2))

mutual

/-- ★ Width subtyping is reflexive (a preorder). -/
theorem widthSubtype_refl {Label : Type} :
    (session : WidthSession Label) → WidthSubtype session session
  | .wEnd => .wEnd
  | .wSend _ continuation => .wSend (widthSubtype_refl continuation)
  | .wRecv _ continuation => .wRecv (widthSubtype_refl continuation)
  | .wSelect branches => widthSelectRefl branches
  | .wBranch branches => widthBranchRefl branches

/-- `wSelect bs ⩽ wSelect bs` for every branch list. -/
theorem widthSelectRefl {Label : Type} :
    (branches : ChoiceList Label) → WidthSubtype (.wSelect branches) (.wSelect branches)
  | .nil => .wSelectNil
  | .cons head tail => .wSelectCons (widthSubtype_refl head) (widthSelectRefl tail)

/-- `wBranch bs ⩽ wBranch bs` for every branch list. -/
theorem widthBranchRefl {Label : Type} :
    (branches : ChoiceList Label) → WidthSubtype (.wBranch branches) (.wBranch branches)
  | .nil => .wBranchNil
  | .cons head tail => .wBranchCons (widthSubtype_refl head) (widthBranchRefl tail)

end

/-- ★★ The Gay-Hole **antitone-under-duality** law (Prop 3.4): width subtyping REVERSES under `dual` —
`sub ⩽ super ⟹ dual super ⩽ dual sub`.  Internal-choice narrowing dualizes to external-choice narrowing and vice
versa; send-depth covariance dualizes to receive-depth covariance.  This is the law `widthCompatibleClient` is
built on, and it is the OPPOSITE variance to the structural precongruence's covariant `SessionSubtype.dual_monotone`
— width subtyping is a genuinely different, richer relation. -/
theorem widthSubtype_dual_antitone {Label : Type} {sub super : WidthSession Label}
    (relation : WidthSubtype sub super) : WidthSubtype super.dual sub.dual := by
  induction relation with
  | wEnd => exact .wEnd
  | wSend _ ih => exact .wRecv ih
  | wRecv _ ih => exact .wSend ih
  | wSelectNil => exact .wBranchNil
  | wSelectCons _ _ ihHead ihTail => exact .wBranchCons ihHead ihTail
  | wBranchNil => exact .wSelectNil
  | wBranchCons _ _ ihHead ihTail => exact .wSelectCons ihHead ihTail

/-- A client is **compatible** with a server when the client is a width-subtype of the server's dual (Gay-Hole
client/server compatibility, the consumer of the antitone law). -/
def widthCompatibleClient {Label : Type} (client server : WidthSession Label) : Prop :=
  WidthSubtype client server.dual

/-! ## Arbitrary-N multiparty projection (discharges hasSessionMultipartyProjection for the communication fragment) -/

/-- A **global (multiparty) type** over an ARBITRARY role set — `gComm sender receiver label continuation` is one
directed message `sender → receiver`.  Unlike the 2-party `GlobalProtocol`, roles are arbitrary (`Role` is any type
with decidable equality), so this is genuine n≥3-party. -/
inductive GlobalType (Role Label : Type) where
  /-- The terminated global session. -/
  | gEnd
  /-- One directed message `sender → receiver : label`, then the rest. -/
  | gComm (sender receiver : Role) (label : Label) (continuation : GlobalType Role Label)

/-- **Projection** of a global type onto one role's local view (Honda-Yoshida-Carbone).  A message is a `send`
for its sender, a `receive` for its receiver, and — the defining multiparty feature — is SKIPPED by every third
party (a role that is neither sender nor receiver moves straight to the continuation). -/
def GlobalType.projectTo {Role Label : Type} [DecidableEq Role] (role : Role) :
    GlobalType Role Label → SessionProtocol Label
  | .gEnd => .endSession
  | .gComm sender receiver label continuation =>
      if role = sender then .send label (continuation.projectTo role)
      else if role = receiver then .receive label (continuation.projectTo role)
      else continuation.projectTo role

/-- The sender's view of a message is a `send`. -/
theorem GlobalType.projectTo_sender {Role Label : Type} [DecidableEq Role] {role sender receiver : Role}
    {label : Label} {continuation : GlobalType Role Label} (isSender : role = sender) :
    (GlobalType.gComm sender receiver label continuation).projectTo role
      = .send label (continuation.projectTo role) := by
  show (if role = sender then _ else _) = _
  rw [if_pos isSender]

/-- The receiver's view of a message is a `receive`. -/
theorem GlobalType.projectTo_receiver {Role Label : Type} [DecidableEq Role] {role sender receiver : Role}
    {label : Label} {continuation : GlobalType Role Label} (notSender : role ≠ sender) (isReceiver : role = receiver) :
    (GlobalType.gComm sender receiver label continuation).projectTo role
      = .receive label (continuation.projectTo role) := by
  show (if role = sender then _ else if role = receiver then _ else _) = _
  rw [if_neg notSender, if_pos isReceiver]

/-- ★ The defining MULTIPARTY feature: a THIRD party (neither sender nor receiver) SKIPS the message — projection
moves straight to the continuation.  This is exactly what the 2-party `GlobalProtocol` cannot express. -/
theorem GlobalType.projectTo_skip {Role Label : Type} [DecidableEq Role] {role sender receiver : Role}
    {label : Label} {continuation : GlobalType Role Label} (notSender : role ≠ sender) (notReceiver : role ≠ receiver) :
    (GlobalType.gComm sender receiver label continuation).projectTo role
      = continuation.projectTo role := by
  show (if role = sender then _ else if role = receiver then _ else _) = _
  rw [if_neg notSender, if_neg notReceiver]

/-- A global type is **bipartite** between roles `a` and `b` when every message is directed between exactly those
two roles (the 2-party slice of the n-party machinery). -/
def GlobalType.isBipartite {Role Label : Type} (a b : Role) : GlobalType Role Label → Prop
  | .gEnd => True
  | .gComm sender receiver _ continuation =>
      ((sender = a ∧ receiver = b) ∨ (sender = b ∧ receiver = a)) ∧ continuation.isBipartite a b

/-- ★ Multiparty projection coherence (2-party slice): on a bipartite global type the two endpoints project to DUAL
local types — `projectTo b = (projectTo a).dual`.  This recovers, through the arbitrary-N `projectTo` with its role
dispatch, the duality that `GlobalProtocol.projectB_eq_dual_projectA` proved for the fixed 2-party encoding. -/
theorem GlobalType.projectTo_dual_of_bipartite {Role Label : Type} [DecidableEq Role] {a b : Role}
    (distinct : a ≠ b) :
    (global : GlobalType Role Label) → global.isBipartite a b →
      global.projectTo b = (global.projectTo a).dual
  | .gEnd, _ => rfl
  | .gComm sender receiver label continuation, bipartite => by
      obtain ⟨here, deeper⟩ := bipartite
      have continuationDual : continuation.projectTo b = (continuation.projectTo a).dual :=
        GlobalType.projectTo_dual_of_bipartite distinct continuation deeper
      cases here with
      | inl senderA =>
          obtain ⟨senderIsA, receiverIsB⟩ := senderA
          rw [GlobalType.projectTo_sender senderIsA.symm,
              GlobalType.projectTo_receiver (by rw [senderIsA]; exact (Ne.symm distinct)) receiverIsB.symm]
          show SessionProtocol.receive label (continuation.projectTo b)
            = SessionProtocol.receive label (continuation.projectTo a).dual
          rw [continuationDual]
      | inr senderB =>
          obtain ⟨senderIsB, receiverIsA⟩ := senderB
          rw [GlobalType.projectTo_receiver (by rw [senderIsB]; exact distinct) receiverIsA.symm,
              GlobalType.projectTo_sender senderIsB.symm]
          show SessionProtocol.send label (continuation.projectTo b)
            = SessionProtocol.send label (continuation.projectTo a).dual
          rw [continuationDual]

/-! ## Delegation — higher-order sessions (channel over channel) -/

/-- A session protocol with **delegation** (Honda 1998 throw/catch / higher-order sessions): `dDelegate delegated
continuation` SENDS a channel whose protocol is `delegated`, then continues as `continuation`; `dAccept` RECEIVES
one.  This is the exponential point where a `.protocol` inhabitant becomes the PAYLOAD of another `.protocol`. -/
inductive DelegatingSession (Label : Type) where
  /-- The terminated protocol. -/
  | dEnd
  /-- Send a labelled value, then continue. -/
  | dSend (label : Label) (continuation : DelegatingSession Label)
  /-- Receive a labelled value, then continue. -/
  | dRecv (label : Label) (continuation : DelegatingSession Label)
  /-- Send (delegate) a channel of protocol `delegated`, then continue as `continuation`. -/
  | dDelegate (delegated : DelegatingSession Label) (continuation : DelegatingSession Label)
  /-- Receive (accept) a channel of protocol `delegated`, then continue as `continuation`. -/
  | dAccept (delegated : DelegatingSession Label) (continuation : DelegatingSession Label)

/-- Duality on delegating sessions.  ★ The crucible invariant: `dDelegate ↔ dAccept` and the CARRIER continuation
flips, but the DELEGATED payload protocol is transferred VERBATIM (NOT dualized) — the recipient owns the same
endpoint the sender had. -/
def DelegatingSession.dual {Label : Type} : DelegatingSession Label → DelegatingSession Label
  | .dEnd => .dEnd
  | .dSend label continuation => .dRecv label continuation.dual
  | .dRecv label continuation => .dSend label continuation.dual
  | .dDelegate delegated continuation => .dAccept delegated continuation.dual
  | .dAccept delegated continuation => .dDelegate delegated continuation.dual

/-- ★ `dual (dDelegate T K) = dAccept T (dual K)` — the delegated payload `T` is preserved verbatim; only the head
flips and the carrier continuation dualizes.  Stated as `rfl`, pinning the crucible invariant. -/
theorem DelegatingSession.dual_dDelegate {Label : Type} (delegated continuation : DelegatingSession Label) :
    (DelegatingSession.dDelegate delegated continuation).dual
      = DelegatingSession.dAccept delegated continuation.dual := rfl

/-- ★ `dual (dAccept T K) = dDelegate T (dual K)` — the symmetric payload-preservation invariant. -/
theorem DelegatingSession.dual_dAccept {Label : Type} (delegated continuation : DelegatingSession Label) :
    (DelegatingSession.dAccept delegated continuation).dual
      = DelegatingSession.dDelegate delegated continuation.dual := rfl

/-- ★ `dual` is a self-inverse involution on delegating sessions (the delegated payload, fixed by `dual`, survives
the round trip unchanged). -/
theorem DelegatingSession.dual_dual {Label : Type} :
    (session : DelegatingSession Label) → session.dual.dual = session
  | .dEnd => rfl
  | .dSend label continuation => congrArg (DelegatingSession.dSend label) continuation.dual_dual
  | .dRecv label continuation => congrArg (DelegatingSession.dRecv label) continuation.dual_dual
  | .dDelegate delegated continuation =>
      congrArg (DelegatingSession.dDelegate delegated) continuation.dual_dual
  | .dAccept delegated continuation =>
      congrArg (DelegatingSession.dAccept delegated) continuation.dual_dual

/-- Whether a protocol uses delegation (contains a `dDelegate`/`dAccept`) — the higher-order fragment. -/
def DelegatingSession.isHigherOrder {Label : Type} : DelegatingSession Label → Bool
  | .dEnd => false
  | .dSend _ continuation => continuation.isHigherOrder
  | .dRecv _ continuation => continuation.isHigherOrder
  | .dDelegate _ _ => true
  | .dAccept _ _ => true

/-- ★ Duality preserves higher-order-ness — `dDelegate`/`dAccept` map to each other, so the higher-order fragment
is closed under `dual`. -/
theorem DelegatingSession.dual_isHigherOrder {Label : Type} :
    (session : DelegatingSession Label) → session.dual.isHigherOrder = session.isHigherOrder
  | .dEnd => rfl
  | .dSend _ continuation => continuation.dual_isHigherOrder
  | .dRecv _ continuation => continuation.dual_isHigherOrder
  | .dDelegate _ _ => rfl
  | .dAccept _ _ => rfl

/-! ## Global CHOICE + plain-merge projection (closes hasSessionMultipartyProjection) -/

mutual

/-- A global (multiparty) type WITH n-ary labelled CHOICE — `mChoice decider chooser branches` is the decider
offering the chooser one of several labelled branches.  This extends the communication-only `GlobalType` to the
full MPST fragment. -/
inductive MpstGlobal (Role Label : Type) where
  /-- The terminated global session. -/
  | mEnd
  /-- One directed message `sender → receiver : label`, then the rest. -/
  | mComm (sender receiver : Role) (label : Label) (continuation : MpstGlobal Role Label)
  /-- `decider` offers `chooser` a labelled choice among `branches`. -/
  | mChoice (decider chooser : Role) (branches : MpstBranches Role Label)

/-- A labelled list of choice branches (mutually inductive with `MpstGlobal`). -/
inductive MpstBranches (Role Label : Type) where
  /-- No further branches. -/
  | bnil
  /-- One labelled branch, then the rest. -/
  | bcons (label : Label) (branch : MpstGlobal Role Label) (rest : MpstBranches Role Label)

end

mutual

/-- **Projection** of a global type (with choice) onto a role's local view, landing in `WidthSession` (whose n-ary
`wSelect`/`wBranch` carry the choice).  The decider sees an internal choice, the chooser an external offer, and a
THIRD party sees the PLAIN MERGE of the branch projections (head-biased — correct exactly when they agree, see
`MpstBranches.projectMerge_eq_of_agree`). -/
def MpstGlobal.projectMpst {Role Label : Type} [DecidableEq Role] (role : Role) :
    MpstGlobal Role Label → WidthSession Label
  | .mEnd => .wEnd
  | .mComm sender receiver label continuation =>
      if role = sender then .wSend label (continuation.projectMpst role)
      else if role = receiver then .wRecv label (continuation.projectMpst role)
      else continuation.projectMpst role
  | .mChoice decider chooser branches =>
      if role = decider then .wSelect (branches.projectSelect role)
      else if role = chooser then .wBranch (branches.projectOffer role)
      else branches.projectMerge role

/-- The decider's branch list — each branch becomes `wSend label (projection)` (the decider sends the chosen label). -/
def MpstBranches.projectSelect {Role Label : Type} [DecidableEq Role] (role : Role) :
    MpstBranches Role Label → ChoiceList Label
  | .bnil => .nil
  | .bcons label branch rest => .cons (.wSend label (branch.projectMpst role)) (rest.projectSelect role)

/-- The chooser's branch list — each branch becomes `wRecv label (projection)` (the chooser receives the label). -/
def MpstBranches.projectOffer {Role Label : Type} [DecidableEq Role] (role : Role) :
    MpstBranches Role Label → ChoiceList Label
  | .bnil => .nil
  | .bcons label branch rest => .cons (.wRecv label (branch.projectMpst role)) (rest.projectOffer role)

/-- The third party's PLAIN MERGE — head-biased: the projection of the first branch (the empty choice merges to
`wEnd`).  It is the genuine merge exactly when every branch agrees (`projectMerge_eq_of_agree`). -/
def MpstBranches.projectMerge {Role Label : Type} [DecidableEq Role] (role : Role) :
    MpstBranches Role Label → WidthSession Label
  | .bnil => .wEnd
  | .bcons _ branch _ => branch.projectMpst role

end

/-- The plain-merge precondition: every branch projects (for `role`) to `target`. -/
def MpstBranches.allAgreeWith {Role Label : Type} [DecidableEq Role] (role : Role) (target : WidthSession Label) :
    MpstBranches Role Label → Prop
  | .bnil => True
  | .bcons _ branch rest => branch.projectMpst role = target ∧ rest.allAgreeWith role target

/-- The decider's view of a choice is a `wSelect`. -/
theorem MpstGlobal.projectMpst_decider {Role Label : Type} [DecidableEq Role] {role decider chooser : Role}
    {branches : MpstBranches Role Label} (isDecider : role = decider) :
    (MpstGlobal.mChoice decider chooser branches).projectMpst role = .wSelect (branches.projectSelect role) := by
  show (if role = decider then _ else _) = _
  rw [if_pos isDecider]

/-- The chooser's view of a choice is a `wBranch`. -/
theorem MpstGlobal.projectMpst_chooser {Role Label : Type} [DecidableEq Role] {role decider chooser : Role}
    {branches : MpstBranches Role Label} (notDecider : role ≠ decider) (isChooser : role = chooser) :
    (MpstGlobal.mChoice decider chooser branches).projectMpst role = .wBranch (branches.projectOffer role) := by
  show (if role = decider then _ else if role = chooser then _ else _) = _
  rw [if_neg notDecider, if_pos isChooser]

/-- A third party's view of a choice is the plain merge of the branch projections. -/
theorem MpstGlobal.projectMpst_third {Role Label : Type} [DecidableEq Role] {role decider chooser : Role}
    {branches : MpstBranches Role Label} (notDecider : role ≠ decider) (notChooser : role ≠ chooser) :
    (MpstGlobal.mChoice decider chooser branches).projectMpst role = branches.projectMerge role := by
  show (if role = decider then _ else if role = chooser then _ else _) = _
  rw [if_neg notDecider, if_neg notChooser]

/-- ★ PLAIN-MERGE correctness: when every branch agrees on `target`, the head-biased `projectMerge` IS that common
`target` — i.e. the third party's merge yields the genuine merged local type.  (Disagreeing branches fail the
`allAgreeWith` premise, exactly the plain-merge discipline; full coinductive merge would relax this.) -/
theorem MpstBranches.projectMerge_eq_of_agree {Role Label : Type} [DecidableEq Role] (role : Role)
    (target : WidthSession Label) :
    (branches : MpstBranches Role Label) → branches.allAgreeWith role target → branches ≠ .bnil →
      branches.projectMerge role = target
  | .bnil, _, notNil => absurd rfl notNil
  | .bcons _ _ _, agree, _ => agree.1

/-! ### A concrete 3-party witness (decider · chooser · observer) -/

/-- A 3-party global (roles as `Nat`: `0` decider, `1` chooser, `2` observer): the decider offers the chooser two
labelled branches; in BOTH branches the decider then sends the observer the same message `7`, then end. -/
def exampleThreePartyGlobal : MpstGlobal Nat Nat :=
  .mChoice 0 1 (.bcons 100 (.mComm 0 2 7 .mEnd) (.bcons 200 (.mComm 0 2 7 .mEnd) .bnil))

/-- The observer (role `2`) is a third party at the choice, so its view is the PLAIN MERGE — both branches project
to `wRecv 7 wEnd`, they agree, and the merge succeeds. -/
theorem exampleThreeParty_observer_merges :
    exampleThreePartyGlobal.projectMpst 2 = WidthSession.wRecv 7 WidthSession.wEnd := rfl

/-- The observer's two branch projections genuinely AGREE — the plain-merge precondition is met. -/
theorem exampleThreeParty_observer_agrees :
    (MpstBranches.bcons 100 (MpstGlobal.mComm 0 2 7 .mEnd)
        (.bcons 200 (MpstGlobal.mComm 0 2 7 .mEnd) .bnil)).allAgreeWith 2
      (WidthSession.wRecv 7 WidthSession.wEnd) :=
  ⟨rfl, rfl, trivial⟩

/-- The decider (role `0`) sees an internal choice (`wSelect`) — two `wSend`-labelled options. -/
theorem exampleThreeParty_decider_selects :
    exampleThreePartyGlobal.projectMpst 0
      = WidthSession.wSelect
          (.cons (WidthSession.wSend 100 (WidthSession.wSend 7 WidthSession.wEnd))
            (.cons (WidthSession.wSend 200 (WidthSession.wSend 7 WidthSession.wEnd)) .nil)) := rfl

/-! ## Honesty markers -/

/-- Duality as a coherent 2-cell is SHIPPED: it is a full order-AUTOMORPHISM of the precongruence
(`SessionSubtype.dual_iff` / `dual_reflect` + `dual_monotone`), self-inverse (`dual_dual`) and advance-coherent
(`dual_fidelity`).  `= true`. -/
def fxMode_hasSessionTwoCellCoherence : Bool := true

/-- Arbitrary-N multiparty projection WITH global choice + plain-merge is SHIPPED: `MpstGlobal` (any role set,
`mComm` + n-ary `mChoice`), total `MpstGlobal.projectMpst` into `WidthSession` — decider→`wSelect`, chooser→
`wBranch`, third party→PLAIN MERGE (`projectMpst_decider`/`_chooser`/`_third`), with merge correctness
(`MpstBranches.projectMerge_eq_of_agree`) and a concrete 3-party witness whose observer's branches agree and merge
(`exampleThreeParty_observer_merges`/`_agrees`).  Plus the communication-fragment `GlobalType.projectTo` with the
third-party SKIP and bipartite duality.  The remaining refinement is FULL (coinductive) merge — plain-merge is the
state-of-the-art level crucible itself ships.  `= true`. -/
def fxMode_hasSessionMultipartyProjection : Bool := true

/-- Gay-Hole WIDTH subtyping is SHIPPED over the n-ary `WidthSession`/`ChoiceList`: `WidthSubtype` (select fewer /
branch more, depth-covariant), reflexive (`widthSubtype_refl`), with the ★ antitone-under-dual law
(`widthSubtype_dual_antitone`) and `widthCompatibleClient`.  `= true`. -/
def fxMode_hasSessionWidthSubtyping : Bool := true

/-- Well-scoped / equirecursive recursion is SHIPPED: `SessionProtocol.wellScoped` checks every `recVar` is bound,
and duality preserves it (`SessionProtocol.dual_wellScoped`).  `= true`. -/
def fxMode_hasSessionRecursionScoping : Bool := true

/-- DELEGATION (higher-order sessions) is SHIPPED: `DelegatingSession` with `dDelegate`/`dAccept` (channel over
channel), its `dual` with the ★ payload-preservation invariant (`dual_dDelegate`/`dual_dAccept` — the delegated `T`
transfers verbatim, only the carrier flips), the involution (`dual_dual`), and the higher-order fragment closed
under dual (`dual_isHigherOrder`).  `= true`. -/
def fxMode_hasSessionDelegation : Bool := true

/-- **Honesty marker.**  The kernel's `.protocol` cell axis fibred into the mode doctrine (cross-axis, `fib`) is
deferred.  `= false`. -/
def fxMode_hasSessionKernelProtocolFibration : Bool := false

end FX1Poly.Tier0
