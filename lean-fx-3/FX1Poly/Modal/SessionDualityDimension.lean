/-! # FX1Poly/Modal/SessionDualityDimension
    — the session-type dimension (§6.3 Dim 6 / §11) as the FIRST INVOLUTION-structured dimension

Every dimension built so far is an ORDER or ALGEBRAIC structure: ordered grade semirings (usage / security /
complexity), bounded join-semilattices and full lattices (effect / trust / overflow / clock / mutation), a
partial PCM (fractional permission), a preorder (lifetime).  The PROTOCOL dimension (§6.3 Dim 6, the session
types of §11) is structurally different in kind: its defining operation is DUALITY — the protocol of the
opposite endpoint — and duality is an INVOLUTION (`dual (dual S) = S`), not an order or a binary combine.  This
file builds that structure, the first of its algebraic shape in the kernel.  (The complementary §27.2
linearity-mechanism witness for session-endpoint aliasing is `L1-SESSION` in the known-unsoundness corpus; this
file is the session-type ALGEBRA those channels are typed by.)

## Session types and duality (§11.1 / §11.2)

A `SessionType` is the protocol a channel endpoint follows: `endSession` (the completed protocol), a `send` or
`receive` of a payload followed by the continuation, and the binary internal/external choices `selectChoice`
(select — this endpoint picks) and `branchOffer` (branch — this endpoint offers).  The payload is the message
TYPE; duality is payload-agnostic (only the DIRECTION flips), so we model the payload as an opaque type tag
(`Nat`).  Recursive (`rec X. S`) sessions are omitted — they need a binder; the send/receive/choice core
already exhibits the full involution structure.

`dual` (§11.2) is the protocol of the OTHER endpoint, by which a channel is created as a pair of dual types:

  * `dual (send p . S) = receive p . dual S`  and  `dual (receive p . S) = send p . dual S` — the direction flips.
  * `dual (selectChoice L R) = branchOffer (dual L) (dual R)`  and the reverse — select ↔ branch (one endpoint's
    choice is the other's offer).
  * `dual endSession = endSession` — the completed protocol is self-dual.

## What lands here (all zero-axiom)

  * `SessionType` (5-ctor inductive, `DecidableEq`) + `SessionType.dual` + the five per-constructor duality
    equations (`dual_endSession` / `dual_send` / `dual_receive` / `dual_selectChoice` / `dual_branchOffer`, each
    `rfl` — the §11.2 swaps hold definitionally).
  * **`SessionType.dual_involutive`** — the headline structure: `dual (dual S) = S`.  Duality is an involution;
    taking the opposite endpoint twice returns the original protocol (so a channel's two endpoints are mutually
    dual — §11.2's "creating a channel produces a pair with dual types").
  * **`SessionType.dual_injective`** — duality is INJECTIVE, hence (being involutive) a BIJECTION on the protocol
    space: each session has exactly one dual partner.
  * **`selfDual_iff_endSession`** — `endSession` is the UNIQUE self-dual protocol (`dual S = S ↔ S = endSession`):
    every protocol that actually communicates (any `send` / `receive` / choice) has a DISTINCT dual, since the
    head constructor flips; only the empty protocol is its own dual.
  * `sessionDualityIsInvolutionButNotIdentity` — the bundled headline: duality is an involution (`∀ S, dual (dual
    S) = S`) but NOT the identity (`∃ S, dual S ≠ S`, e.g. a `send` is not its own dual) — a genuine reversal,
    the structural signature distinguishing this dimension from the order/algebra dimensions.

## Zero-axiom verification

`SessionType` is a plain (non-indexed) inductive with derived `DecidableEq`; `dual` is a 5-case structural
recursion (no wildcards, propext-free).  `dual_involutive` closes by `induction` over the plain recursor
(propext-free for a non-indexed inductive) + `congrArg`; `dual_injective` applies `dual` to both sides and
rewrites by the involution; `selfDual_iff_endSession` is `cases` + `SessionType.noConfusion` (the flipped head
constructor) on the forward direction and `subst`/`rfl` on the backward; the non-identity witness is `by decide`
over the `DecidableEq`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- A session type (§11.1): the completed protocol `endSession`, a `send` / `receive` of a payload (the message
type, modeled as an opaque `Nat` tag) followed by the continuation, and the binary choices `selectChoice` (this
endpoint selects) / `branchOffer` (this endpoint offers a branch). -/
inductive SessionType where
  | endSession
  | send (payload : Nat) (rest : SessionType)
  | receive (payload : Nat) (rest : SessionType)
  | selectChoice (left : SessionType) (right : SessionType)
  | branchOffer (left : SessionType) (right : SessionType)
  deriving DecidableEq

/-- Session DUALITY (§11.2): the protocol of the OPPOSITE endpoint.  `send` ↔ `receive`, `selectChoice` ↔
`branchOffer`, `endSession` self-dual; the payload is unchanged (only the direction flips), and duality recurses
into the continuation.  Full 5-case structural recursion, propext-free. -/
def SessionType.dual : SessionType → SessionType
  | .endSession => .endSession
  | .send payload rest => .receive payload rest.dual
  | .receive payload rest => .send payload rest.dual
  | .selectChoice left right => .branchOffer left.dual right.dual
  | .branchOffer left right => .selectChoice left.dual right.dual

/-- `endSession` is self-dual (§11.2). -/
theorem dual_endSession : SessionType.endSession.dual = SessionType.endSession := rfl

/-- `dual (send p . S) = receive p . dual S` — sending becomes receiving (§11.2). -/
theorem dual_send (payload : Nat) (rest : SessionType) :
    (SessionType.send payload rest).dual = SessionType.receive payload rest.dual := rfl

/-- `dual (receive p . S) = send p . dual S` — receiving becomes sending (§11.2). -/
theorem dual_receive (payload : Nat) (rest : SessionType) :
    (SessionType.receive payload rest).dual = SessionType.send payload rest.dual := rfl

/-- `dual (selectChoice L R) = branchOffer (dual L) (dual R)` — this endpoint's selection is the other's
offered branch (§11.2 select ↔ branch). -/
theorem dual_selectChoice (left right : SessionType) :
    (SessionType.selectChoice left right).dual = SessionType.branchOffer left.dual right.dual := rfl

/-- `dual (branchOffer L R) = selectChoice (dual L) (dual R)` — the dual of an offered branch is a selection
(§11.2 branch ↔ select). -/
theorem dual_branchOffer (left right : SessionType) :
    (SessionType.branchOffer left right).dual = SessionType.selectChoice left.dual right.dual := rfl

/-- ★ **Duality is an INVOLUTION** — `dual (dual S) = S`.  Taking the opposite endpoint twice returns the
original protocol; this is the structural signature of the protocol dimension (§6.3 Dim 6), and the reason a
channel is created as a pair of mutually dual endpoint types (§11.2). -/
theorem SessionType.dual_involutive (session : SessionType) : session.dual.dual = session := by
  induction session with
  | endSession => rfl
  | send payload rest ih => exact congrArg (SessionType.send payload) ih
  | receive payload rest ih => exact congrArg (SessionType.receive payload) ih
  | selectChoice left right ihLeft ihRight =>
      exact (congrArg (fun hole => SessionType.selectChoice hole right.dual.dual) ihLeft).trans
            (congrArg (SessionType.selectChoice left) ihRight)
  | branchOffer left right ihLeft ihRight =>
      exact (congrArg (fun hole => SessionType.branchOffer hole right.dual.dual) ihLeft).trans
            (congrArg (SessionType.branchOffer left) ihRight)

/-- **Duality is INJECTIVE** — `dual S1 = dual S2 → S1 = S2`.  Combined with the involution, duality is a
BIJECTION on the protocol space: each session has exactly one dual partner. -/
theorem SessionType.dual_injective {firstSession secondSession : SessionType}
    (dualsEqual : firstSession.dual = secondSession.dual) : firstSession = secondSession := by
  have viaInvolution := congrArg SessionType.dual dualsEqual
  rwa [SessionType.dual_involutive, SessionType.dual_involutive] at viaInvolution

/-- **`endSession` is the UNIQUE self-dual protocol** — `dual S = S ↔ S = endSession`.  Every protocol that
communicates (any `send` / `receive` / `selectChoice` / `branchOffer`) has a DISTINCT dual, because the head
constructor flips under duality; only the completed protocol is its own dual. -/
theorem selfDual_iff_endSession (session : SessionType) :
    session.dual = session ↔ session = SessionType.endSession := by
  constructor
  · intro selfDual
    cases session with
    | endSession => rfl
    | send payload rest => exact SessionType.noConfusion selfDual
    | receive payload rest => exact SessionType.noConfusion selfDual
    | selectChoice left right => exact SessionType.noConfusion selfDual
    | branchOffer left right => exact SessionType.noConfusion selfDual
  · intro isEnd; subst isEnd; rfl

/-- ★ **Session duality is an involution but NOT the identity.**  `dual (dual S) = S` for every protocol, yet
some protocol differs from its dual (`send 0 . end` dualizes to `receive 0 . end ≠ send 0 . end`) — a genuine
direction reversal.  This is the structural signature distinguishing the protocol dimension from the
order/algebra dimensions: it is an involutive type, not a graded semiring or a lattice. -/
theorem sessionDualityIsInvolutionButNotIdentity :
    (∀ session : SessionType, session.dual.dual = session) ∧
    (∃ session : SessionType, session.dual ≠ session) :=
  ⟨SessionType.dual_involutive,
   ⟨SessionType.send 0 SessionType.endSession, by decide⟩⟩

end FX1Poly.Modal
