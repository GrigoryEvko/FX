import FX1Poly.Modal.SoundnessCollisionSchema
import FX1Poly.Modal.ThreeWayCollisionClassifiedAsyncSession
import FX1Poly.Modal.UnifiedGradeMonoid

/-! # FX1Poly/Modal/FlagshipMultiDimensionSignature
    — the §1.3 flagship `encrypt_and_send`: a multi-dimension grade configuration that is JOINTLY
      §6.8-ADMISSIBLE — the POSITIVE counterpart to the collision corpus

The §6.8 corpus (`PrecisionOverflowCollision` #1021, `SoundnessCollisionSchema` #1022,
`ThreeWayCollisionClassifiedAsyncSession` #1026) is the NEGATIVE face of the "the dimensions are not
orthogonal" thesis: it catalogs which capability combinations are jointly UNSOUND.  This file ships
the POSITIVE face, which §1.3 demands but the corpus never states: a SINGLE realistic signature that
exercises many dimensions at once and lands SQUARELY in the §6.8-admissible region across every
relevant collision axis simultaneously.

The canonical example is §1.3's `encrypt_and_send<a, r, eff>(buffer, key, ch)`: a `secret ref(r)` key
(classified + borrowed), `with IO, Crypto, Async, eff` (impure + async), over a session-typed channel
`ch`.  That signature touches usage, security, effect, lifetime, protocol, and constant-time at once.

## The headline tension §1.3 forces (and its resolution)

The flagship literally co-occurs classified data + `Async` + a session channel — exactly the three
flags of #1026's `classified × async × session` collision.  Under #1026's COARSE co-occurrence model
the flagship reads as `IsClassifiedAsyncSessionAdmissible true true true`, which is FALSE
(`classifiedAsyncSessionCollision`).  So the coarse model would REJECT the canonical sound example.

The resolution is §12.2's implicit-flow discipline: the leak fires only when the classified value
CONTROLS the async session scheduling, not when it merely co-occurs with async + sessions.  In
`encrypt_and_send` the secret key flows into constant-time encryption (§12.5 `with CT`), NOT into a
branch that selects which session message to send — so it does not control scheduling, and the
signature is genuinely sound.

This file mechanizes that as a REFINEMENT of #1026:

  * `IsImplicitFlowAdmissible (classifiedControlsScheduling async session)` — the same shape as #1026,
    but the first flag's MEANING is sharpened from "classified present" to "classified CONTROLS
    scheduling" (the §12.2 implicit-flow capability).
  * `encryptAndSendImplicitFlowAdmissible` — the flagship is admissible (the secret does not control
    scheduling), even with async + session granted.
  * `secretControlsSchedulingCollision` — the genuine attack (secret DOES control scheduling) still
    collides — the refinement is not vacuous.
  * `implicitFlowAdmissible_ofCoOccurrenceAdmissible` — SOUNDNESS of the refinement: anything the
    coarse co-occurrence model accepts, the implicit-flow model accepts too (it is more permissive).
  * `flagshipDistinguishesModels` — the refinement is STRICTLY more permissive on the flagship itself:
    coarse REJECTS, implicit-flow ACCEPTS.  This is precisely why §12.2 tracks implicit flow through
    control structure rather than mere co-occurrence — the coarse model is a sound-but-incomplete
    over-approximation; the implicit-flow model is the precise constraint.

## The grade vector and the joint-admissibility headline

  * `encryptAndSendGradeMonoid` (+ `IsLawful`) — the concrete ≥3-factor grade vector for the site:
    usage × (security × effect), drawn from BOTH the resource family (usage, security) and the
    co-effect family (effect).  Lawful FREE from `productIsLawful` — extends the shipped 2-factor
    `securityEffectGradeMonoid` (#913) to three dimensions.  `encryptAndSendKeyGrade` is the flagship
    key parameter's concrete grade point: borrowed (`ref`, usage ω = shared) × classified (secret) ×
    impure (IO/Crypto/Async).
  * **`encryptAndSendJointlyAdmissible` (★)** — the headline: under its declared grade configuration
    the signature satisfies EVERY §6.8 constraint touching its dimensions at once — the implicit-flow
    3-way (secret does not control scheduling), `monotonic × concurrent` (the key is accessed
    sequentially), and `decimal × overflow` (no exact-decimal arithmetic on the byte buffer).  The
    mechanized realization of §1.3's "a single function exercises many dimensions simultaneously, and
    they compose."

## Honest scope boundary

This is the COMBINE-time JOINT-admissibility witness over the signature's declared grade configuration
— the algebraic face of §1.3.  It does not operationally verify the encryption term; the side
conditions the witness assumes (`classifiedControlsScheduling = false` — the secret flows only into CT
encryption; sequential access to the read-only borrow; no decimal arithmetic) are exactly what the
term-level checker (§12.2 implicit-flow, §12.5 CT, the grade-vector checker) discharges per-term.  The
joint-admissibility theorem IS the ternary/binary constraint such a checker enforces at the site.

## Zero-axiom verification

The admissibility facts are `Bool.noConfusion` on the impossible conjunct / structure projection; the
grade-vector lawfulness threads the shipped `productIsLawful`; the per-collision consistency reuses
`sequentialConsistentWithEveryMutation` and the `inexact.isExact = false` reduction.  No `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-! ## Part 1 — the implicit-flow refinement of the `classified × async × session` collision -/

/-- **The implicit-flow REFINEMENT of #1026's 3-way collision.**  Same shape as
`IsClassifiedAsyncSessionAdmissible`, but the first flag is sharpened from "classified data present"
to `classifiedControlsScheduling` — does the classified value CONTROL the async session scheduling
(the §12.2 implicit-flow capability)?  The collision fires only when the secret controls scheduling
AND async AND a session are all granted. -/
def IsImplicitFlowAdmissible (classifiedControlsScheduling async session : Bool) : Prop :=
  ¬ (classifiedControlsScheduling = true ∧ async = true ∧ session = true)

/-- **The §1.3 flagship is admissible.**  `encrypt_and_send` grants async + a session channel and
carries a classified (secret) key, yet is admissible: the secret flows into constant-time encryption,
NOT into a branch selecting the session message — so it does not CONTROL the scheduling
(`classifiedControlsScheduling = false`).  No implicit-flow leak through the interleaving. -/
theorem encryptAndSendImplicitFlowAdmissible :
    IsImplicitFlowAdmissible false true true :=
  fun conjunction => Bool.noConfusion conjunction.1

/-- **The refinement is not vacuous**: the genuine attack — a classified value that DOES control the
async session scheduling — still collides.  This is the real §6.8 unsoundness the constraint rules
out. -/
theorem secretControlsSchedulingCollision :
    ¬ IsImplicitFlowAdmissible true true true :=
  fun admissible => admissible ⟨rfl, rfl, rfl⟩

/-- **Soundness of the refinement.**  Anything the coarse co-occurrence model (#1026) accepts, the
implicit-flow model accepts too — provided the control-flow flag is bounded by classified-presence
(you cannot control scheduling with a value that is not classified).  So replacing the coarse
constraint by the implicit-flow constraint never admits a configuration the coarse model rejected as
unsound: the refinement only ADDS permissiveness on genuinely-sound sites. -/
theorem implicitFlowAdmissible_ofCoOccurrenceAdmissible
    {classifiedPresent classifiedControlsScheduling async session : Bool}
    (coarseAdmissible : IsClassifiedAsyncSessionAdmissible classifiedPresent async session)
    (controlBoundedByPresence : classifiedControlsScheduling = true → classifiedPresent = true) :
    IsImplicitFlowAdmissible classifiedControlsScheduling async session :=
  fun conjunction =>
    coarseAdmissible ⟨controlBoundedByPresence conjunction.1, conjunction.2.1, conjunction.2.2⟩

/-- **The refinement is STRICTLY more permissive on the flagship itself.**  The SAME real signature —
classified present, async, session, but the secret does not control scheduling — is REJECTED by the
coarse co-occurrence model (`IsClassifiedAsyncSessionAdmissible true true true` is false) yet ACCEPTED
by the implicit-flow model.  This is exactly why §12.2 tracks implicit flow through control structure
rather than mere co-occurrence: the coarse model is a sound-but-incomplete over-approximation; the
implicit-flow model is the precise constraint that admits the canonical sound example. -/
theorem flagshipDistinguishesModels :
    ¬ IsClassifiedAsyncSessionAdmissible true true true ∧
    IsImplicitFlowAdmissible false true true :=
  ⟨classifiedAsyncSessionCollision, encryptAndSendImplicitFlowAdmissible⟩

/-! ## Part 2 — the concrete ≥3-dimension grade vector for the signature site -/

/-- The grade vector for the `encrypt_and_send` site: usage × (security × effect) — a resource
dimension (usage), a resource dimension (security), and a co-effect dimension (effect) in ONE grade
monoid.  Extends the shipped 2-factor `securityEffectGradeMonoid` (#913) to three factors, drawn from
BOTH §6.8 dimension families. -/
def encryptAndSendGradeMonoid : CommutativeGradeMonoid :=
  fxUsageSemiring.toCommutativeGradeMonoid.product securityEffectGradeMonoid

/-- **The 3-factor grade vector is a lawful grade monoid** — FREE from `productIsLawful`, no
per-product proof.  Concretely realizes §6.1's "the dimensions compose pointwise in the grade vector"
at ≥3 dimensions spanning both the resource (usage, security) and co-effect (effect) families. -/
theorem encryptAndSendGradeMonoidIsLawful :
    IsLawfulCommutativeGradeMonoid encryptAndSendGradeMonoid :=
  CommutativeGradeMonoid.productIsLawful
    (fxUsageSemiring.toCommutativeGradeMonoid_isLawful fxUsageSemiring_isLawful)
    securityEffectGradeMonoidIsLawful

/-- The flagship key parameter's concrete grade point: borrowed (`ref`, usage ω = shared/duplicable
per §6.4), classified (the key is `secret`), under the impure ambient function effect (IO/Crypto/Async
join to `impureEffect`).  An element of the 3-factor grade-vector carrier. -/
def encryptAndSendKeyGrade : encryptAndSendGradeMonoid.Carrier :=
  (UsageGrade.omega, (SecurityGrade.classified, EffectGrade.impureEffect))

/-- The grade vector's monoid structure COMPUTES on the concrete flagship configuration: combining the
key grade with the vector identity returns it unchanged (componentwise unit across all three
dimensions). -/
theorem encryptAndSendKeyGrade_combine_identity :
    encryptAndSendGradeMonoid.combine encryptAndSendKeyGrade encryptAndSendGradeMonoid.identity
      = encryptAndSendKeyGrade :=
  encryptAndSendGradeMonoidIsLawful.combine_identity encryptAndSendKeyGrade

/-! ## Part 3 — the signature lands in the §6.8-admissible region across every relevant collision -/

/-- `monotonic × concurrent` (Dim 18 × Dim 19): the key is accessed SEQUENTIALLY within the function
body (a read-only `ref` borrow, no unsynchronized concurrent access), so the access is consistent with
EVERY mutation mode — no `monotonic × concurrent` collision at this site. -/
theorem encryptAndSendMutationConcurrencyConsistent :
    monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.sequential MutationGrade.immutable :=
  sequentialConsistentWithEveryMutation MutationGrade.immutable

/-- `decimal × overflow(wrap)` (Dim 14 × Dim 16): the crypto signature performs no exact-decimal
arithmetic (it operates on the byte `buffer`), so the precision demand is weak (`inexact`) and
consistent with every overflow mode — no `decimal × overflow` collision at this site. -/
theorem encryptAndSendPrecisionOverflowConsistent :
    decimalOverflowSchema.IsConsistent PrecisionGrade.inexactPrecision OverflowGrade.wrapGrade :=
  fun absurdFlag => Bool.noConfusion absurdFlag

/-- ★ **The §1.3 flagship is JOINTLY §6.8-admissible.**  Under its declared grade configuration the
`encrypt_and_send` signature satisfies EVERY §6.8 cross-dimension soundness constraint that touches its
dimensions, SIMULTANEOUSLY:

  * the 3-way `classified × async × session` (refined to implicit flow — the secret key does not
    control session scheduling),
  * `monotonic × concurrent` (the key is accessed sequentially),
  * `decimal × overflow(wrap)` (no exact-decimal arithmetic).

This is the POSITIVE counterpart to the collision corpus (#1021/#1022/#1026): those show what FAILS
jointly; this shows a REAL multi-dimension signature SUCCEEDS jointly — the mechanized face of §1.3's
"a single function exercises many dimensions simultaneously, and they compose." -/
theorem encryptAndSendJointlyAdmissible :
    IsImplicitFlowAdmissible false true true ∧
    monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.sequential MutationGrade.immutable ∧
    decimalOverflowSchema.IsConsistent PrecisionGrade.inexactPrecision OverflowGrade.wrapGrade :=
  ⟨encryptAndSendImplicitFlowAdmissible,
   encryptAndSendMutationConcurrencyConsistent,
   encryptAndSendPrecisionOverflowConsistent⟩

end FX1Poly.Modal
