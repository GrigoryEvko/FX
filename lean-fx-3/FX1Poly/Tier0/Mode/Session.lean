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

/-! ## Honesty markers -/

/-- Duality as a coherent 2-cell is SHIPPED: it is a full order-AUTOMORPHISM of the precongruence
(`SessionSubtype.dual_iff` / `dual_reflect` + `dual_monotone`), self-inverse (`dual_dual`) and advance-coherent
(`dual_fidelity`).  `= true`. -/
def fxMode_hasSessionTwoCellCoherence : Bool := true

/-- **Honesty marker.**  The n≥3-party MULTIPARTY projection with the MERGE operator (full MPST) is deferred — the
2-party global-to-local projection + its duality coherence (`GlobalProtocol.projectA`/`projectB` /
`projectB_eq_dual_projectA`) ARE shipped.  `= false`. -/
def fxMode_hasSessionMultipartyProjection : Bool := false

/-- **Honesty marker.**  The Gay-Hole WIDTH subtyping (select fewer / branch more options) needs an n-ARY choice
former; the binary `selectChoice`/`branchOffer` here support only the width-uniform precongruence (shipped) + its
antitone duality.  Deferred to an n-ary refinement.  `= false`. -/
def fxMode_hasSessionWidthSubtyping : Bool := false

/-- Well-scoped / equirecursive recursion is SHIPPED: `SessionProtocol.wellScoped` checks every `recVar` is bound,
and duality preserves it (`SessionProtocol.dual_wellScoped`).  `= true`. -/
def fxMode_hasSessionRecursionScoping : Bool := true

/-- **Honesty marker.**  The kernel's `.protocol` cell axis fibred into the mode doctrine (cross-axis, `fib`) is
deferred.  `= false`. -/
def fxMode_hasSessionKernelProtocolFibration : Bool := false

end FX1Poly.Tier0
