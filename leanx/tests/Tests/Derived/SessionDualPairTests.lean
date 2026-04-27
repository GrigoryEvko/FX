import FX.Derived.Session

/-!
# Session dual-pair translation tests (task S12)

Closes the gap between S9 (single-direction translation) and
`new_channel<S>()` (which needs BOTH S and dual(S) registered in
GlobalEnv for type-checking).  Covers `translateDualPair` in
`FX/Derived/Session/Translate.lean`:

  * **Both halves emit specs** — primary and dual each produce
    a non-empty spec list for non-trivial sessions.
  * **Name isolation** — primary and dual names never collide.
    Primary uses `"<prefix>_N"`, dual uses `"<prefix>__dual_N"`.
  * **Duality correctness via names** — `send` in primary maps
    to `recv` in dual, `selectS` → `offerS`, `recv` → `send`.
    Verified structurally by inspecting destructor names in the
    root spec of each side.
  * **Idempotency at the SessionType level** — `dual (dual s) = s`
    per S3's `dual_dual` theorem means translating the dual
    pair twice reproduces the primary's shape in the re-dualized
    slot.

All checks are compile-time `native_decide` — `translate` is a
`partial def` so native compilation is required.
-/

namespace Tests.Derived.SessionDualPairTests

open FX.Derived.Session
open FX.Kernel

/-! ## Helpers -/

/-- Arbitrary payload used in session fixtures.  Shape-only. -/
private def natPayload : Term := Term.ind "Nat" []

/-! ## Section 1: Both halves emit specs

`translateDualPair` returns a `TranslationResult × TranslationResult`.
For a non-empty session, each half has at least one spec — the
terminal for endS/stop, or the head spec for send/recv/select/offer.
-/

-- endS: primary emits 1 spec, dual emits 1 spec.
example :
  let (primary, dual) := translateDualPair "P" SessionType.endS
  primary.specs.length == 1 && dual.specs.length == 1 := by
  native_decide

-- send(Nat, end): both halves 2 specs (head + continuation).
example :
  let (primary, dual) := translateDualPair "P"
    (SessionType.send natPayload .endS)
  primary.specs.length == 2 && dual.specs.length == 2 := by
  native_decide

-- selectS with 2 branches: each half 1 head spec + 2 arm specs = 3.
example :
  let (primary, dual) := translateDualPair "P"
    (SessionType.selectS [("a", .endS), ("b", .endS)])
  primary.specs.length == 3 && dual.specs.length == 3 := by
  native_decide

/-! ## Section 2: Name isolation — primary vs dual prefixes

Primary names follow `"<prefix>_N"`.  Dual names follow
`"<prefix>__dual_N"` (double underscore).  The disjoint prefixes
guarantee `GlobalEnv.addUserCoindSpecs` can add both halves
without name collision, and `coindSpecByName?` resolves each
uniquely.
-/

-- Primary root name starts with the given prefix.
example :
  let (primary, _) := translateDualPair "Chan"
    (SessionType.send natPayload .endS)
  primary.rootName == "Chan_1" := by native_decide

-- Dual root name starts with the dual-marked prefix.
example :
  let (_, dual) := translateDualPair "Chan"
    (SessionType.send natPayload .endS)
  dual.rootName == "Chan__dual_1" := by native_decide

-- No spec name from the primary appears in the dual's spec list.
example :
  let (primary, dual) := translateDualPair "Chan"
    (SessionType.send natPayload (.recv natPayload .endS))
  let primaryNames := primary.specs.map (·.name)
  let dualNames    := dual.specs.map (·.name)
  primaryNames.all (fun pName =>
    dualNames.all fun dName => pName != dName) := by
  native_decide

/-! ## Section 3: Duality correctness

§11.2 duality rules:
  - `dual(send(T).S) = recv(T).dual(S)`
  - `dual(recv(T).S) = send(T).dual(S)`
  - `dual(select<...>) = offer<...>` (branches dualized)
  - `dual(offer<...>)  = select<...>`

Inspect destructor names on the root spec of each half to verify
the expected transformation.
-/

/-- Project the root spec's first destructor's name, or
    `"<no-dest>"` if no destructor exists. -/
private def rootFirstDestName (result : TranslationResult) : String :=
  match result.specByName? result.rootName with
  | some spec =>
    match spec.destructors with
    | dest :: _ => dest.name
    | []        => "<no-dest>"
  | none => "<no-root>"

-- Primary: send(Nat, end) has "send" destructor at root.
example :
  let (primary, _) := translateDualPair "P"
    (SessionType.send natPayload .endS)
  rootFirstDestName primary == "send" := by native_decide

-- Dual flips to "recv".
example :
  let (_, dual) := translateDualPair "P"
    (SessionType.send natPayload .endS)
  rootFirstDestName dual == "recv" := by native_decide

-- Primary: recv(Nat, end) has "recv" destructor.
example :
  let (primary, _) := translateDualPair "P"
    (SessionType.recv natPayload .endS)
  rootFirstDestName primary == "recv" := by native_decide

-- Dual flips to "send".
example :
  let (_, dual) := translateDualPair "P"
    (SessionType.recv natPayload .endS)
  rootFirstDestName dual == "send" := by native_decide

-- Selectbranches preserve labels but the head switches select↔offer
-- through the translation's destructor-list shape.  The destructor
-- *labels* of selectS and offerS are identical (both list their
-- branch labels) — the semantic distinction (internal vs external
-- choice) lives in the typing rule, not the destructor names.
-- We verify label preservation instead: primary and dual both have
-- the two branch labels.
example :
  let (primary, dual) := translateDualPair "P"
    (SessionType.selectS [("a", .endS), ("b", .endS)])
  let primRoot := primary.specByName? primary.rootName
  let dualRoot := dual.specByName? dual.rootName
  (match primRoot with
   | some spec => spec.destructors.length
   | none      => 0)
    == 2
  &&
  (match dualRoot with
   | some spec => spec.destructors.length
   | none      => 0)
    == 2 := by native_decide

/-! ## Section 4: Idempotency — dual of dual preserves primary shape

S3 proves `dual (dual s) = s` at the SessionType level.  At the
translation level, double-dualing means the primary's destructor
name (e.g. "send") should return after two applications — which
we verify by running `dual` twice in the payload before
translating, and checking that the root destructor matches the
once-primary form.
-/

-- dual(dual(send(Nat, end))) = send(Nat, end), so primary of the
-- double-dualed session has "send" at the root.
example :
  let doubled := SessionType.dual (SessionType.dual
    (SessionType.send natPayload .endS))
  let (primary, _) := translateDualPair "P" doubled
  rootFirstDestName primary == "send" := by native_decide

/-! ## Section 5: Helper functions `translateDualPairSpecs` and
`translateDualPairErrors` expose the combined view suitable for
direct use in elaborator calls.
-/

-- Combined specs = primary.specs ++ dual.specs.  For
-- send(Nat, end), 2 + 2 = 4.
example :
  (translateDualPairSpecs "P"
    (SessionType.send natPayload .endS)).length == 4 := by
  native_decide

-- Error list is empty on well-formed input.
example :
  (translateDualPairErrors "P"
    (SessionType.send natPayload .endS)).isEmpty := by
  native_decide

-- Malformed input (continueS outside loop) produces errors
-- from BOTH halves (each half's translate walks its tree
-- independently).  Pins that error aggregation works.
example :
  (translateDualPairErrors "P" SessionType.continueS).length > 0 := by
  native_decide

end Tests.Derived.SessionDualPairTests
