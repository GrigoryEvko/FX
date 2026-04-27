import FX.Kernel.Grade.Usage
import FX.Kernel.Grade.Effect
import FX.Kernel.Grade.Mutation
import FX.Kernel.Grade
import FX.Kernel.Typing
import FX.Kernel.Inductive

/-!
# Unsoundness corpus — known-witness regression tests

Implements **layer 1** of `fx_design.md` §27.3's five-layer
defense:  every known type-theory bug from the literature is a
permanent regression test.  The corpus is indexed in
`docs/MetatheoryCorpus.md`; this file is the Lean realization.

## Status (Phase 1)

Only the entries whose rejectors already exist in `leanx` Phase-1
kernel (grade semirings for Usage + friends) are exercised as
**realized** `example : … := …` tests.  The rest are listed as
`-- TODO` comments keyed to the corpus entry number, the source
paper, and the phase that unlocks them (per SPEC.md §7).

## Contract

Each realized test is a `example : <rejection-lemma>`, where the
rejection lemma is of shape:

  * "the grade arithmetic that would admit this witness is actually
    arithmetic that our kernel rejects" — proved by `decide` or
    pattern match.

Deferred tests are commented `-- TODO(§27.2, entry #N, paper): …`
with enough context that the test author at the relevant phase
can drop the placeholder and write the concrete rejection lemma.

## Append-only discipline

New corpus entries arrive as PRs that add both a row to
`docs/MetatheoryCorpus.md` and a matching test here.  Removing an
entry requires an RFC under `docs/rfcs/`.  The file only grows.
-/

namespace Tests.Metatheory.UnsoundnessCorpusTests

open FX.Kernel

/-! ## Category A — Grade and linearity (§27.2) -/

/-- **Corpus entry #1 — Atkey 2018 Lam rule (LICS 2018).**

The broken rule `context, x :_r A ⊢_s b : B ⟹ context ⊢_s lambdax.b : (x :_r A) → B`
allowed a linear variable `f : i64 → i64` at grade `1` to appear in
a closure built at grade `omega`, using it twice (`f(f(x))`).

Wood-Atkey LICS 2022 replaces the outer context with `context/s`.  For
Usage, `1 / omega = 0`:  division erases a linear binding from a
replicable-closure context, so the ill-typed program is rejected.

This test witnesses the division computing the correct result.  See
`FX/Kernel/Grade/Usage.lean` for the full `div` specification and
its universal property (`div_spec`). -/
example : Usage.div Usage.one Usage.omega = Usage.zero := by
  decide

/-- **Corpus entry #1b — end-to-end Atkey witness at `Term.infer`.**

This constructs the actual term `lambda(f : Nat→Nat). lambda(x : Nat). f(f(x))`
and asks the kernel whether it type-checks.

**Current status: ACCEPTS — bug present.**  Phase-2.2's `infer`
calls `Ctx.divByUsage g.usage` at Pi-intro per §27.1's corrected
Lam rule, but the App rule does not yet track per-variable usage
accumulation (see `FX/Kernel/Typing.lean:44-48` documenting this
as a deferred Phase-3 enforcement, and task A9 in the plan).
The div itself computes `1/1 = 1` at the inner lam, so `f` stays
linear — but nothing counts that `f` is *used twice* inside the
body, so the witness slips through.

This test is a **ratchet**: when task A9 (linearity exit check)
lands and App threads usage vectors per §6.2's `p1 + r * p2`
rule, this expectation flips to `.error _` and the test must be
updated accordingly.  Until then, the test documents that the
kernel presently under-rejects at the end-to-end level, while
the arithmetic lemma above still witnesses the Wood/Atkey
mechanism at the grade layer.

Relevant: `fx_design.md` §27.1 (the broken vs corrected rule),
§6.2 (App/Lam typing), Appendix H.2 Pi-intro (Wood-Atkey with
context division).  See `Typing.lean` App case for where the
grade arithmetic is currently dropped. -/
private def natTy : FX.Kernel.Term := .ind "Nat" []
private def natArrow : FX.Kernel.Term :=
  .piTot FX.Kernel.Grade.default natTy natTy
private def atkeyWitness : FX.Kernel.Term :=
  .lam FX.Kernel.Grade.default natArrow (
    .lam FX.Kernel.Grade.default natTy (
      .app (.var 1) (.app (.var 1) (.var 0))))

/-- The kernel rejects this with `M001` — `f` has usage grade
    `1` (linear, the default) yet appears twice in the body
    `f(f(x))`.  The check: the Pi-intro exit rule counts var-0
    occurrences in the body (treating type positions as erased)
    and requires the count `≤` the binder's declared grade.  For
    the outer `f`-binder, the inner body `app (var 1) (app (var 1)
    (var 0))` references `var 1` twice, giving `one + one = omega`,
    which exceeds the declared `one`.

    Witnesses the corrected Wood-Atkey Lam rule in action. -/
example : (FX.Kernel.Term.infer [] atkeyWitness).isOk = false := by
  native_decide

example :
  (match FX.Kernel.Term.infer [] atkeyWitness with
   | .error typeError => typeError.code == "M001"
   | .ok _            => false) = true := by native_decide

/-- **Corpus entry #2 — Session endpoint aliased (MPST negative).**

A linear session endpoint must not appear twice in the same
context — using it both sides of parallel composition double-sends.
In our Usage semiring, the sum `1 + 1` is `omega` (not `1`), so a linear
binding used on both sides of an `if` fails the exit check which
demands grade `1`.

This test witnesses the addition rule itself. -/
example : Usage.add Usage.one Usage.one = Usage.omega := by
  decide

-- TODO(§27.2, entry #3, Wright 1995): ML value restriction —
--   polymorphism under a `ref` is unsound.  Rejected by the
--   product of the Usage grade and the (Phase-3) Mutation grade.
--   Deferred to Phase 3 per SPEC.md §7.

/-! ## Category B — Dependent / higher-order (§27.2) -/

/-- **Corpus entry #4 — Type:Type (Girard 1972, Coquand 1986).**

If `Type : Type` were admitted, Girard's paradox derives
`False`.  FX avoids it via a strict universe hierarchy:
`type u : type (succ u)`, never `type u : type u`.

The kernel's `.type u` case in `infer` returns `type (succ u)`.
A `check` against `type u` as expected asks whether
`type (succ u) ≤ type u`, which holds only if `succ u ≤ u` —
false for any concrete level.  So checking `type 0` against
expected `type 0` MUST fail.

Witness: `check [] typeZero typeZero` errors with `T002` (the
§10.10 "type mismatch" code).  A broken kernel that dropped
the `succ` and returned `type u : type u` would accept here
and would unlock Girard's paradox downstream.

Relevant: `fx_design.md` Appendix H.1 (U-hier rule), §31.4
(universe cumulativity — which does NOT extend to this case
because cumul only relaxes `u ≤ v` upward, never downward). -/
example :
  (match FX.Kernel.Term.check []
    (.type .zero) (.type .zero) with
   | .error typeError => typeError.code == "T002"
   | .ok _            => false) = true := by native_decide

-- Paired positive: `check [] typeZero typeOne` SUCCEEDS —
-- typeZero's type is typeOne, so the check is trivially true.
-- A broken kernel that over-rejected universe checks would
-- fail here while still passing the #4 test above.
example :
  (FX.Kernel.Term.check []
    (.type .zero) (.type (.succ .zero))).isOk = true := by native_decide

-- Deeper: `type 1 : type 1` also fails (same shape, different
-- level).  Distinguishes correct universe hierarchy from
-- "only type 0 is special" bugs.
example :
  (match FX.Kernel.Term.check []
    (.type (.succ .zero)) (.type (.succ .zero)) with
   | .error typeError => typeError.code == "T002"
   | .ok _            => false) = true := by native_decide

/-- **Corpus entry #5 — Strict positivity (Coq 2.0, 1991).**

A self-reference in negative (left-of-arrow) position in a
constructor argument type admits non-termination:

    inductive Bad where
      mk : (Bad → Bad) → Bad

lets `fn bang(b: Bad) : Bad = match b; mk(f) => f(b); end match`
loop via `bang(mk(bang))` and derive `False` through Curry-
Howard.  FX's kernel rejects this via
`StrictPositivity.isSatisfied`, which walks every ctor arg's
type and fails when the type being defined appears to the
left of a Pi.

The positivity check is at the `IndSpec`-registration layer.
A constructed-in-Lean IndSpec with a negative occurrence MUST
return `false` from `isSatisfied` — if it returned `true`,
the kernel would admit the spec and Phase-3 elab could
dispatch on it, opening the paradox.

Well-formed specs (Bool, Nat, List) MUST pass.  A broken
checker that always returned `true` (admit everything) would
pass the positive tests below but fail the negative one;
a broken checker that always returned `false` (reject
everything) would fail the positive tests.  Both directions
are pinned. -/

-- Positive: Bool's ctors have empty arg lists — trivially positive.
example : StrictPositivity.isSatisfied Inductive.boolSpec = true := by
  native_decide

-- Positive: Nat.Succ's arg is `ind "Nat" []` (positive recursive
-- occurrence in final-codomain position — allowed).
example : StrictPositivity.isSatisfied Inductive.natSpec = true := by
  native_decide

-- Negative: construct an IndSpec with a NEGATIVE self-occurrence.
-- `Bad.mk : (Bad → Bad) → Bad` — the arg type is
-- `Pi _ (Ind "Bad" []) (Ind "Bad" [])`, which has `Bad` on the
-- LEFT of the Pi.  `StrictPositivity.absent "Bad" domain` returns
-- false because `domain = Ind "Bad" []` mentions Bad.  So
-- `strictlyPositive "Bad" (pi _ (ind "Bad" []) (ind "Bad" []))` is
-- false — the spec is malformed.
def badSpec : IndSpec :=
  { name := "Bad"
  , params := []
  , ctors := [{
      name := "mk"
    , args := [.piTot Grade.default (.ind "Bad" []) (.ind "Bad" [])] }] }

example : StrictPositivity.isSatisfied badSpec = false := by native_decide

-- Deeper negative: `DeepBad.mk : ((DeepBad → Nat) → Nat) → DeepBad`
-- — DeepBad appears NEGATIVELY under TWO Pis (left of outer-
-- outer arrow).  Still rejected.
def deepBadSpec : IndSpec :=
  { name := "DeepBad"
  , params := []
  , ctors := [{
      name := "mk"
    , args := [.piTot Grade.default
                (.piTot Grade.default
                  (.ind "DeepBad" [])
                  (.ind "Nat" []))
                (.ind "DeepBad" [])] }] }

example : StrictPositivity.isSatisfied deepBadSpec = false := by native_decide

-- TODO(§27.2, entry #6, Coquand 1993): coinductive data without a
--   guardedness / sized check diverges silently.  Rejected by the
--   Abel-Pientka copattern check in `FX/Kernel/Check.lean`
--   (Phase 6).

/-! ## Category C — Information flow (§27.2) -/

/-- **Corpus entry #7 — Implicit flow (Volpano-Smith-Irvine 1996).**

A branch on a `classified` (secret) value cannot produce an
`unclassified` (public) result without explicit declassify —
otherwise the attacker can observe the output and learn one bit
about the secret scrutinee.

FX's `Security` grade is a two-element join-semilattice:
`unclassified ≤ classified`, `add = mul = join`.  An `if
secretGuard then X else Y` compiling to `indRec` combines the
scrutinee's grade (classified) with each arm's grade via the
kernel's grade arithmetic.  `classified + unclassified` joins
to `classified`, so the result type's Security dim CANNOT be
`unclassified` unless both arms AND the scrutinee are all
public — which would require `declassify` to drop the secret.

Phase-5 activation plugs this into the typing rule for
`indRec`/match; Phase-2 exercises the arithmetic that sits
beneath.  Witness: `add classified unclassified = classified`,
not `unclassified`.  A broken lattice that returned
`unclassified` here would admit the leak.

Paired with the dual: `add unclassified unclassified = unclassified`
(pure public flow — no leak).  Catches a broken lattice that
over-classified everything. -/

-- Classified ⊔ unclassified = classified (join, leak detected).
example : Security.add .classified .unclassified = .classified := by decide

-- Symmetric: order of operands doesn't matter (commutativity).
example : Security.add .unclassified .classified = .classified := by decide

-- Pure public: no leak.
example : Security.add .unclassified .unclassified = .unclassified := by decide

-- Classified is the top — subsumption ordering enforces that a
-- public context cannot accept a classified value.
example : ¬ Security.LessEq .classified .unclassified := by
  intro hLe; cases hLe

-- TODO(§27.2, entry #8, Almeida et al. 2016): constant-time
--   violation — a secret-indexed array read leaks the index.
--   Rejected by the Observability grade on array indexing under
--   `with CT`; Phase-5 activation.

/-! ## Category D — Concurrency / permissions (§27.2) -/

/-- **Corpus entry #9 — Fractional permission over-allocation.**

Boyland SAS 2003 warns that a naive sum of fractions can exceed `1`,
silently granting more access than the resource has.  FX's
three-element quotient `{0, 1, omega}` closes under `+` with `omega` at
the top, which is the abstract analog of "more-than-one" and
rejects a subsequent linear exit check.

Witness:  `1 + omega = omega`, so once a linear binding has been "shared
more than once" it can never be consumed as linear again. -/
example : Usage.add Usage.one Usage.omega = Usage.omega := by
  decide

/-- **Corpus entry #10 — Mutex aliased (O'Hearn SAS 2004).**

A `ref mut` (exclusive borrow) captured twice produces unsound
concurrent updates: both aliases see the same mutable storage
and concurrent writes race.  FX's Mutation dimension is a
four-element chain `immutable ≤ append_only ≤ monotonic ≤
read_write` with `add = mul = join`.  At a closure-capture site
that duplicates the ref, the Usage grade becomes `w` (captured
`omega`) while the Mutation grade stays `read_write` — the
aggregate grade product rejects this as "too permissive for a
linear exclusive borrow".

This test pins the Mutation arithmetic that sits beneath the
rejection: combining `read_write` with anything still returns
`read_write` (the top absorbs), so a borrow once exposed at
`read_write` cannot be down-graded to `immutable` without
re-borrowing.  The Phase-3 typing rule consuming this is the
Pi-intro mode check — it will refuse a `ref mut` binder in a
context that's been `join`ed with any other `ref mut` source. -/
example : Mutation.add Mutation.readWrite Mutation.immutable = Mutation.readWrite := by decide

example : Mutation.add Mutation.readWrite Mutation.readWrite = Mutation.readWrite := by decide

/-- Mutation top absorbs — readWrite can never be subsumed to
    immutable.  This is the lattice-level proof that a consumer
    asking for `immutable` cannot accept a `ref mut` binding. -/
example : ¬ Mutation.LessEq Mutation.readWrite Mutation.immutable := by
  intro hLe
  -- LessEq is rank ≤ rank; readWrite has rank 3, immutable has
  -- rank 0.  3 ≤ 0 is false.
  exact absurd hLe (by decide)

/-! ## Category E — Effects / handlers (§27.2) -/

/-- **Corpus entry #11 — Effect row escape (Leijen 2014).**

An untyped handler that drops the effect row loses the guarantee
that the body's effects were actually handled.  If a function
body performs `IO` but its signature declares `Tot`, the callee
can leak side effects past a boundary the caller trusted to be
pure.

FX's Effect grade is a bounded join-semilattice with `Tot` as the
identity.  Subsumption `LessEq` is pointwise implication: every
bit set in the smaller side must be set in the larger side.  For
a body-effect `{IO}` and a declared `Tot`, `LessEq {IO} Tot`
fails at the IO bit — `IO = true` in the body, `IO = false` in
the declared row.  A13's `inferDeclBodyEffect` + `Effect.subsumes`
at pass 2 of checkFile is exactly this check: body subsumes
declared is REQUIRED, and a violation emits E044.

The arithmetic-level witness: the subsumption from `IO`-tagged
to `Tot` is false.  A broken lattice that admitted this would
let `IO`-tainted bodies slip through `Tot` signatures. -/
example : ¬ Effect.LessEq Effect.io_ Effect.tot := by
  intro hLe
  -- hLe is an 8-tuple of implications; the IO component says
  -- `Effect.io_.io = true → Effect.tot.io = true`.  But
  -- `Effect.io_.io = true` and `Effect.tot.io = false`, so the
  -- implication fires and derives `true = false`.
  have ioImpl := hLe.1
  have : Effect.tot.io = true := ioImpl rfl
  cases this

/-- Paired positive: `Effect.LessEq tot io_` DOES hold.  A pure
    body trivially satisfies an IO-capable signature (callers
    expecting IO can safely receive Tot).  Catches a broken
    lattice that forbade all widening. -/
example : Effect.LessEq Effect.tot Effect.io_ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro h <;> cases h

/-- Write must not escape as Tot — same shape as IO, different
    bit.  Ensures no single-effect escape slips through. -/
example : ¬ Effect.LessEq Effect.write_ Effect.tot := by
  intro hLe
  have writeImpl := hLe.2.2.2.2.2.2.1
  have : Effect.tot.write = true := writeImpl rfl
  cases this

/-- Combined effects accumulate via join — `IO + Async` must not
    escape as `IO` alone (Async is forgotten otherwise).
    Asymmetric subsumption. -/
example : ¬ Effect.LessEq (Effect.add Effect.io_ Effect.async_) Effect.io_ := by
  intro hLe
  have asyncImpl := hLe.2.2.2.2.2.2.2
  have : Effect.io_.async = true := asyncImpl rfl
  cases this

-- TODO(§27.2, entry #12, Hillerström-Lindley 2018): multi-shot
--   continuation captures a linear variable.  Rejected by the
--   (Usage × Effect) interaction that forbids multi-shot resumes
--   over a grade-1 capture; Phase 3 (needs handler grammar).

/-! ## Category F — Aggregate grade-vector soundness -/

/-- **Corpus entry #13 — Grade-vector double-consume.**

At the aggregate `Grade` level, a linear binding consumed along
two parallel paths (e.g., both arms of an `if`) composes via
`Grade.add`.  The Usage component rises from `one` to `omega`
(`1 + 1 = omega`); the aggregate `Grade.add` threads this
through the Option-valued bind, so the resulting grade's Usage
field is the joined value.

If a downstream typing rule demanded `Usage.one` on exit, the
aggregate would carry `Usage.omega` and fail the exit check.
This test witnesses the pointwise arithmetic — the Grade
aggregator actually propagates the Usage semiring's join. -/
example :
  (Grade.add { Grade.default with usage := Usage.one }
             { Grade.default with usage := Usage.one }).map (·.usage)
    = some Usage.omega := by native_decide

/-- Paired dual: adding `zero` (ghost) to `one` leaves `one`
    unchanged — ghost components don't count toward the linear
    exit obligation.  This is why `ghost` bindings can freely
    coexist with linear ones. -/
example :
  (Grade.add { Grade.default with usage := Usage.zero }
             { Grade.default with usage := Usage.one }).map (·.usage)
    = some Usage.one := by native_decide

/-- **Corpus entry #14 — Aggregate Security propagation.**

When a classified binding is joined with a public one via
`Grade.add`, the Security component must stay classified (high-
water mark).  Downgrading to unclassified here is the implicit-
flow leak entry #7 at the aggregate layer — this test pins the
propagation. -/
example :
  (Grade.add { Grade.default with security := Security.classified }
             { Grade.default with security := Security.unclassified }).map (·.security)
    = some Security.classified := by native_decide

example :
  (Grade.add { Grade.default with security := Security.unclassified }
             { Grade.default with security := Security.unclassified }).map (·.security)
    = some Security.unclassified := by native_decide

end Tests.Metatheory.UnsoundnessCorpusTests
