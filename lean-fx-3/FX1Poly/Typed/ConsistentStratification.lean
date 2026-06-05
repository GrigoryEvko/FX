import FX1Poly.Typed.ValidTyping

/-! # FX1Poly/Typed/ConsistentStratification
    — the level-inference invariant for the route-A leveling-bridge assembly (toward SN-027/#662)

**Route-A crosscheck (off the critical path — BFT/OB-5 `#794` already closed SN-043 unconditionally;
this is the independent ValidTyping-route 2nd proof feeding the SN-150 triangulation).**

The totalBridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027/#662) is an induction
that must SYNTHESIZE a `contextLevels : Fin scope → Nat` from the LEVEL-FREE context.  The make-or-break
constraint is the conv-to-type-VARIABLE arm (`validTypingBridgeConvPinnedReclassifier`,
`LevelingBridge.lean`): reclassifying a subject `x` to a bare type variable `var typeIndex` needs that type
variable — which `ValidTyping.var` PINS at `contextLevels typeIndex` — to sit at `contextLevels (x's index) + 1`.

`ConsistentStratification` is exactly the static invariant a candidate `contextLevels` must satisfy for that
arm: every binding whose looked-up type IS a type variable sits one level below that type variable.  This file
ships the invariant plus its two basic structural consequences (it is acyclic at every node and strictly
orders the type-variable edge); the binder-extension preservation + the full assembly are the subsequent
multi-fire steps of #662 (the binder-extension case needs the `weaken`/`lookup_cons` variable-image lemmas).

## What is proved

  * `ConsistentStratification` — the invariant: a binding whose type is `var typeIndex` is one level below it.
  * `consistentStratification_empty` — the empty context is consistently stratified (vacuously).
  * `ConsistentStratification.strictlyBelowType` — a binding sits STRICTLY below its type variable.
  * `ConsistentStratification.noSelfType` — no binding is its own type (`lookup index = var index` is
    impossible: it would force `contextLevels index = contextLevels index + 1`).

## Zero-axiom verification

Direct `Nat` arithmetic (`Nat.lt_succ_self` / `Nat.lt_irrefl`) over the invariant + `Fin.elim0` for the empty
base.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The level-inference invariant** a totalBridge `contextLevels` must satisfy: every binding whose type is
a TYPE VARIABLE `variableCell typeIndex` sits exactly one level below that type variable.  This is the static
fact the conv-to-type-variable arm consumes — a term `x : X` with `X = var typeIndex` is at
`contextLevels (x's index)`, and `var typeIndex` (its reclassifier) is needed one level above. -/
def ConsistentStratification {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope) : Prop :=
  ∀ (termIndex typeIndex : Fin scope),
    context.lookup termIndex = variableCell typeIndex →
    contextLevels typeIndex = contextLevels termIndex + 1

/-- **The empty context is consistently stratified** at any (vacuous) level vector — there are no bindings
to constrain (`Fin 0` is empty). -/
theorem consistentStratification_empty {profile : PolyProfile}
    (contextLevels : Fin 0 → Nat) :
    ConsistentStratification contextLevels (TypingContext.empty : TypingContext profile 0) :=
  fun termIndex _typeIndex _isVarType => termIndex.elim0

/-- **A binding sits STRICTLY below its type variable.**  If binding `termIndex` has type `var typeIndex`,
then `contextLevels termIndex < contextLevels typeIndex` — the strict order on the type-variable edge,
read directly off the `+ 1` in the invariant. -/
theorem ConsistentStratification.strictlyBelowType {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    (consistent : ConsistentStratification contextLevels context)
    {termIndex typeIndex : Fin scope}
    (isVarType : context.lookup termIndex = variableCell typeIndex) :
    contextLevels termIndex < contextLevels typeIndex := by
  rw [consistent termIndex typeIndex isVarType]
  exact Nat.lt_succ_self _

/-- **No binding is its OWN type** under a consistent stratification: `context.lookup index = variableCell
index` is impossible (it would force `contextLevels index = contextLevels index + 1`).  Acyclicity of the
type-variable graph at every single node. -/
theorem ConsistentStratification.noSelfType {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    (consistent : ConsistentStratification contextLevels context) (index : Fin scope) :
    context.lookup index ≠ variableCell index := by
  intro isSelfType
  exact absurd (consistent.strictlyBelowType isSelfType) (Nat.lt_irrefl _)

end FX1Poly.Typed
