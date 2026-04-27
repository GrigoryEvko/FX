import FX.Derived.Session.Binary
import FX.Derived.Session.Translate

/-!
# Derived spec — Session types (§11)

Umbrella module for FX's session-type machinery.  Session
types govern the protocols of message-passing channels per
§11 of the design document, and they translate to kernel
`CoindSpec` terms under the mapping of §11.24.

The implementation proceeds in 25 stages (S1–S25), tracked
in the task list.  Each stage lands as one focused change
preserving CI green at every step; the submodules of this
directory are populated in stage order.

## Roadmap

The 25 stages divide into seven phases.  Early phases
establish provable foundations in Lean 4; middle phases
extend the kernel and wire the elaborator; later phases
implement runtime, advanced typing, and the integration
with §14 contracts that makes a session into a partial
wire-level contract.

### Phase 1 — provable foundations (S1–S5)

All in `FX/Derived/Session/Binary.lean`.  Data type (S1,
landed), `dual` function (S2), `dual_dual` involutive
theorem (S3), well-formedness predicate (S4), synchronous
Gay-Hole subtyping (S5).

### Phase 2 — kernel extension (S6–S9)

Complete `Coind-form` / `Coind-intro` / `Coind-elim` typing
rules in `FX/Kernel/Typing.lean` (S6), `ν` reduction in
`FX/Kernel/Reduction.lean` (S7), Protocol grade (dim 6,
Tier T) session-state wiring (S8), and the `SessionType`
→ `CoindSpec` translation (S9).

### Phase 3 — surface elaboration (S10–S14)

Parser wiring for `session_decl` (S10), the elaborator
branch that turns a session declaration into a registered
`CoindSpec` (S11), the `new_channel<P>()` primitive that
mints a dual pair (S12), `send` and `receive` desugaring
to kernel destructor calls (S13), and compilation of
`select` and `offer` branch patterns (S14).

### Phase 4 — runtime (S15–S17)

Runtime representation of channel values with an in-process
bounded queue (S15), send/receive evaluation with
linearity enforcement (S16), and the `cancel` primitive
that propagates crash-stop through the existing `Fail`
effect (S17).

### Phase 5 — advanced typing (S18–S21)

Queue types σ with a balanced+ composition-site check
(S18), global types and projection (S19), association
Δ ⊑_s G per HYK24 (S20), and precise asynchronous
subtyping via SISO decomposition bounded at a
configurable depth (S21).

### Phase 6 — contract bridge (S22–S23)

The sessions-as-partial-contracts integration: each
message's payload is routed through a named contract's
validator and format binding (S22), and session
declarations support version and migration clauses that
reuse the §14 contract-migration machinery (S23).
Together these two stages make a session declaration
constitute a partial wire-level contract — the protocol
structure is session-type, the payload discipline is
contract-type, and the compiler generates one unified
validator and migration set at the wire boundary.

### Phase 7 — patterns, diagnostics, conformance (S24–S25)

A pattern library for canonical session shapes
(RequestResponse, FanOut, FanIn, ScatterGather, 2PC, and
so on), the S001–S021 error-code taxonomy from §11.27
wired into `FX/Util/Diagnostic.lean` (S24), and an
end-to-end conformance suite of `.fx` programs
exercising the full stack including contract-bridged
sessions (S25).

## Untrusted layer

Everything in `FX/Derived/Session/` is L3 untrusted per
SPEC.md §5.  The kernel-level soundness obligations sit on
the Appendix H.5 `CoindSpec` axioms once S6 and S9 land;
until then the session machinery is standalone and the
surface declaration stays rejected at E010 by the
elaborator.
-/
