import FX1Poly.Typed.TypingRoleEngineBridge

/-! # FX1Poly/Typed/UntypableHeadDecision — the decidable cascade-free untypability decision procedure (GTL-ROLE follow-up)

`HasTypeDescPiDataHeadUntyped.lean` proves, for each of a dozen specific data heads (`gen_boolElim`,
`gen_fst`, `gen_natElim`, `gen_pair`, …), a bespoke "this cell is untyped" theorem — each a one-line
`apply cellHasNoTypingWhenRootGenericallyExcluded <;> …`.  `TypingRoleEngineBridge.lean` (firing 99) distilled
the general criterion `HasTypeDescPi.cellUntypedWhenRolelessAndNonBespoke`: a cell head that is ROLELESS
(`typingRoleOf = none`) AND neither bespoke typed head (`≠ gen_var`, `≠ gen_universeCode`) has no grown typing.

This file makes that criterion DECIDABLE and CASCADE-FREE — the precondition is a pure-syntax `Bool` decision
over the generator, so a NEW data former's untypability is a `rfl`-check (a `decide` that computes), never a new
proof.  This is the untyping-direction realization of the FRAME-2 extensibility thesis: the genuinely-untyped
heads are exactly those the decision procedure accepts, and adding a data generator costs zero metatheory.

  * **`isUntypableHead`** — the decision procedure: `decide (typingRoleOf g = none ∧ g ≠ gen_var ∧
    g ≠ gen_universeCode)`.  Pure syntax over the generator; computes to `true`/`false` by `rfl`.
  * **`isUntypableHead_sound`** — soundness: `isUntypableHead g = true` ⟹ a cell rooted at `g` has no grown
    typing.  Routes `of_decide_eq_true` (the propext-free `decide`-elimination) into
    `cellUntypedWhenRolelessAndNonBespoke`.  THE cascade-free untypability theorem — one statement for every
    untypable head, present and future.
  * `isUntypableHead_{boolTrue,fst,natElim,emptyCode}` — `rfl` witnesses that the procedure accepts a data
    CONSTRUCTOR, a PROJECTION, a RECURSIVE eliminator, and the deferred Empty TYPE-CODE — the untyped-head
    shapes, classified uniformly by computation.
  * `isUntypableHead_{var,universeCode,lam}_false` — `rfl` witnesses that it correctly REJECTS the two bespoke
    typed heads (roleless yet typed) and the table-driven heads (here `gen_lam`): the procedure does not
    over-claim untypability.
  * **`HasTypeDescPi.natElimCellUntypedViaDecision`** — the concrete consumer: a typed `gen_natElim` cell
    yields `False` through `isUntypableHead_sound rfl`, rederiving the bespoke `natElimCellHasNoTyping` via the
    single decidable route.

## Zero-axiom

`isUntypableHead` is `decide` over a conjunction of `DecidableEq` facts (`Option TypingRole`, `Generator`,
both flat-enum-derived); soundness is `of_decide_eq_true` (a `Decidable`-cases function, NOT `decide_eq_true_eq`
which would pull `propext`) feeding the firing-99 criterion; the witnesses are `rfl`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The decidable untypability decision procedure.**  A generator heads a genuinely-untyped cell iff it is
ROLELESS (`typingRoleOf = none`) AND neither bespoke typed head (`≠ gen_var`, `≠ gen_universeCode`).  All three
conjuncts are `DecidableEq` facts, so this is a pure-syntax `Bool` that computes by `rfl`. -/
def isUntypableHead (generator : Generator) : Bool :=
  decide (typingRoleOf generator = none ∧
    generator ≠ Generator.gen_var ∧ generator ≠ Generator.gen_universeCode)

/-- ★ **Soundness of the untypability decision procedure** — the cascade-free untypability theorem.  A cell
whose head `g` satisfies `isUntypableHead g = true` has no grown typing.  Eliminates the `decide` with
`of_decide_eq_true` (propext-free) to recover the three `typingRoleOf = none` / `≠ gen_var` /
`≠ gen_universeCode` facts, then feeds the firing-99 criterion `cellUntypedWhenRolelessAndNonBespoke`.  ONE
theorem covering every untypable head: a new data generator's untypability is `isUntypableHead g = true` by
`rfl`, with no new proof. -/
theorem isUntypableHead_sound {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {classifier : RawTerm scope}
    (untypable : isUntypableHead generator = true)
    (typed : HasTypeDescPi profile context (.mkGen generator payload children) classifier) :
    False := by
  obtain ⟨roleless, notVar, notUniverse⟩ := of_decide_eq_true untypable
  exact typed.cellUntypedWhenRolelessAndNonBespoke roleless notVar notUniverse

/-! ## The procedure ACCEPTS every untyped-head shape (constructor / projection / recursor / deferred type-code) -/

/-- `gen_boolTrue` (a data CONSTRUCTOR) is classified untypable. -/
theorem isUntypableHead_boolTrue : isUntypableHead .gen_boolTrue = true := rfl

/-- `gen_fst` (a PROJECTION eliminator) is classified untypable. -/
theorem isUntypableHead_fst : isUntypableHead .gen_fst = true := rfl

/-- `gen_natElim` (a RECURSIVE eliminator) is classified untypable. -/
theorem isUntypableHead_natElim : isUntypableHead .gen_natElim = true := rfl

/-- `gen_emptyCode` (the deferred Empty TYPE-CODE, CON-A1) is classified untypable — its formation row is not
yet in `typingRuleDescOf`, so it is roleless and non-bespoke. -/
theorem isUntypableHead_emptyCode : isUntypableHead .gen_emptyCode = true := rfl

/-! ## The procedure REJECTS the typed heads — no over-claiming -/

/-- `gen_var` (the bespoke `var`-arm typed head) is NOT classified untypable (roleless yet typed). -/
theorem isUntypableHead_var_false : isUntypableHead .gen_var = false := rfl

/-- `gen_universeCode` (the bespoke `universeFormation`-arm typed head) is NOT classified untypable. -/
theorem isUntypableHead_universeCode_false : isUntypableHead .gen_universeCode = false := rfl

/-- `gen_lam` (a table-driven INTRODUCTION head) is NOT classified untypable (it carries an intro role). -/
theorem isUntypableHead_lam_false : isUntypableHead .gen_lam = false := rfl

/-! ## The concrete consumer — bespoke untyping rederived through the single decidable route -/

/-- **A typed `gen_natElim` cell is impossible, via the decision procedure.**  `isUntypableHead .gen_natElim =
true` (by `rfl`), so `isUntypableHead_sound` fires — rederiving `HasTypeDescPiDataHeadUntyped`'s bespoke
`natElimCellHasNoTyping` through the unified cascade-free decision rather than the per-generator inequalities. -/
theorem HasTypeDescPi.natElimCellUntypedViaDecision {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_natElim.payload scope}
    {children : RawTermChildren Generator.gen_natElim.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_natElim payload children) classifier) :
    False :=
  isUntypableHead_sound rfl typed

end FX1Poly.Typed
