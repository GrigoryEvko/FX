/-! # FX1Poly/Modal/ThreeWayCollisionClassifiedAsyncSession
    — the genuinely THREE-WAY §6.8 collision, irreducible to any pair

`PrecisionOverflowCollision` (#1021) and `SoundnessCollisionSchema` (#1022) mechanized the §6.8 cross-dimension
soundness collisions as TWO-WAY collisions: a strong guarantee-demand from one dimension is unsound with a
capability from ANOTHER single dimension (`decimal × overflow(wrap)`, `monotonic × concurrent`).  Every such
collision is one `SoundnessCollisionSchema` value — a collision on a single dimension PAIR.

But §6.8's catalog has ONE entry that is NOT a pair: **`classified × async × session`** — the only genuinely
three-way collision.  Information flow (classified data) leaks through the INTERLEAVING of asynchronous session
communications: an attacker observing the order/timing of async session messages can recover a classified value
that controls that scheduling.  Crucially, ANY TWO of the three capabilities compose soundly — classified+async
without sessions, classified+session without async, async+session without classified are each fine — so NO
two-dimension restriction (no `SoundnessCollisionSchema` instance over any pair) captures it.  The collision is
IRREDUCIBLE to pairwise: it genuinely requires all three.

This file mechanizes that:

  * `IsClassifiedAsyncSessionAdmissible (classified async session : Bool)` — the joint-admissibility predicate:
    NOT all three risky capabilities granted at once (`¬ (classified ∧ async ∧ session)`).
  * **`classifiedAsyncSessionCollision` (★)** — the collision: granting all three is inadmissible.
  * **`classifiedAsyncSessionIrreducible`** — the IRREDUCIBILITY witness: each of the three PAIRS (the remaining
    capability withheld) IS admissible.  No proper subset of `{classified, async, session}` collides — this is a
    genuinely three-way collision, structurally unlike the two-way `decimal × overflow` (#1021) /
    `monotonic × concurrent` (#1022), which collide on a single pair.
  * `isAdmissible_iff` — the decidable characterization: admissible iff at least one capability is withheld
    (De Morgan).

Together with the two-way corpus, this spans §6.8 structurally: the catalog is two-way collisions (reducible to a
pair, schema #1022) PLUS this one irreducible three-way collision.

## Honest scope boundary

This models the COMBINE-time joint-admissibility CONSTRAINT over the three dimension flags — the algebraic face of
the §6.8 three-way entry, and the precise statement that no pairwise restriction suffices.  It does not derive the
leak operationally from the async/session/security semantics (that is the term-level information-flow checker's
job); the irreducibility theorem IS the constraint such a checker must enforce as a genuine ternary clause.

## Zero-axiom verification

The admissibility facts are `Bool.noConfusion` on the impossible `false = true` conjunct (the withheld
capability); the collision is `fun admissible => admissible ⟨rfl, rfl, rfl⟩`; the characterization is a
`cases`-driven De Morgan with `Bool.noConfusion` leaves.  No `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The §6.8 three-way joint-admissibility constraint for `classified × async × session`: the three risky
capabilities (classified information present, `Async` effect granted, session-typed channel in use) may NOT all be
granted together.  Each flag is `true` when that dimension's capability is granted. -/
def IsClassifiedAsyncSessionAdmissible (classified async session : Bool) : Prop :=
  ¬ (classified = true ∧ async = true ∧ session = true)

/-- ★ **The three-way collision.**  Granting all three of classified flow, async, and session at once is
inadmissible — the classified value's ordering leaks through the async session interleaving.  §6.8's only
genuinely three-way cross-dimension soundness collision. -/
theorem classifiedAsyncSessionCollision :
    ¬ IsClassifiedAsyncSessionAdmissible true true true :=
  fun admissible => admissible ⟨rfl, rfl, rfl⟩

/-- **Pair (1/3): classified + async WITHOUT session is admissible.**  Without a session channel there is no
interleaving to leak through. -/
theorem classifiedAsync_admissibleWithoutSession :
    IsClassifiedAsyncSessionAdmissible true true false :=
  fun conjunction => Bool.noConfusion conjunction.2.2

/-- **Pair (2/3): classified + session WITHOUT async is admissible.**  Without async there is no scheduling
non-determinism to observe. -/
theorem classifiedSession_admissibleWithoutAsync :
    IsClassifiedAsyncSessionAdmissible true false true :=
  fun conjunction => Bool.noConfusion conjunction.2.1

/-- **Pair (3/3): async + session WITHOUT classified is admissible.**  Without classified data there is nothing
secret to leak. -/
theorem asyncSession_admissibleWithoutClassified :
    IsClassifiedAsyncSessionAdmissible false true true :=
  fun conjunction => Bool.noConfusion conjunction.1

/-- **The collision is GENUINELY three-way (irreducible to any pair).**  Each of the three pairs — withholding the
remaining capability — is admissible, so no proper subset of `{classified, async, session}` collides.  Unlike the
two-way collisions (`decimal × overflow` #1021, `monotonic × concurrent` #1022), which collide on a single
dimension pair, this collision needs all three: no `SoundnessCollisionSchema` (#1022) over any pair captures it. -/
theorem classifiedAsyncSessionIrreducible :
    IsClassifiedAsyncSessionAdmissible true true false ∧
    IsClassifiedAsyncSessionAdmissible true false true ∧
    IsClassifiedAsyncSessionAdmissible false true true :=
  ⟨classifiedAsync_admissibleWithoutSession,
   classifiedSession_admissibleWithoutAsync,
   asyncSession_admissibleWithoutClassified⟩

/-- **The decidable admissibility law.**  A `(classified, async, session)` configuration is admissible iff at
least one of the three capabilities is withheld — the De Morgan dual of the three-way forbidden clause, exactly
what a grade-vector checker would decide at a site exercising all three dimensions. -/
theorem isAdmissible_iff (classified async session : Bool) :
    IsClassifiedAsyncSessionAdmissible classified async session ↔
      (classified = false ∨ async = false ∨ session = false) := by
  unfold IsClassifiedAsyncSessionAdmissible
  constructor
  · intro notAll
    cases classified
    · exact Or.inl rfl
    · cases async
      · exact Or.inr (Or.inl rfl)
      · cases session
        · exact Or.inr (Or.inr rfl)
        · exact absurd ⟨rfl, rfl, rfl⟩ notAll
  · rintro disjunct ⟨hClassified, hAsync, hSession⟩
    cases disjunct with
    | inl h => rw [hClassified] at h; exact Bool.noConfusion h
    | inr h => cases h with
      | inl h => rw [hAsync] at h; exact Bool.noConfusion h
      | inr h => rw [hSession] at h; exact Bool.noConfusion h

end FX1Poly.Modal
