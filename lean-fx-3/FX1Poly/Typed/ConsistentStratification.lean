import FX1Poly.Typed.ValidTyping
import FX1Poly.Typed.HasTypeWeakening
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Core.CandidateInterpretationRename

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
  * `rename_eq_variableCell_inversion` — a renamed term equal to a variable cell WAS a variable cell whose
    renamed index is the observed one (the key lemma for the binder-extension step).
  * `levelCons_weaken` — `levelCons` at a `weaken`-shifted index reads the tail vector at the original index.
  * `ConsistentStratification.cons` — the binder-extension preservation: extending a consistent stratification
    by one binder (whose type, if a variable, sits one level below the fresh head level) stays consistent.

## Zero-axiom verification

Direct `Nat` arithmetic (`Nat.lt_succ_self` / `Nat.lt_irrefl`) over the invariant + `Fin.elim0` for the empty
base; the binder-extension step is the propext-free `⟨0,_⟩`/`⟨k+1,_⟩` `Fin`-position match (mirroring
`ReducibleEnvVec.cons`, NOT `Fin.cases`) feeding the rename-variable inversion + the `rfl`-closed
`levelCons_weaken` computation.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

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

/-- **Rename-variable inversion** — the binder-extension key lemma.  If a RENAMED term is a variable cell,
the ORIGINAL term was a variable cell whose renamed index is the observed one.  Assembled from
`RawTerm.rename_rootGenerator` (rename preserves the head generator), `eq_variableCell_of_headGenerator`
(a head-`gen_var` cell IS a variable), `rename_variableCell` (the forward action), and `mkGen` injectivity.

This is exactly what the cons-preservation step of the totalBridge needs: a context's `lookup` weakens its
stored type by `RawTerm.rename RawRenaming.weaken`, so deciding whether `(context.cons d).lookup index` is a
variable — to discharge / use the stratification constraint — reduces (via this inversion) to whether the
underlying stored type was a variable. -/
theorem rename_eq_variableCell_inversion {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {typeIndex : Fin targetScope}
    (isVar : RawTerm.rename rawRenaming term = variableCell typeIndex) :
    ∃ sourceIndex : Fin sourceScope,
      term = variableCell sourceIndex ∧ rawRenaming sourceIndex = typeIndex := by
  have headIsVariable : RawTerm.headGenerator term = Generator.gen_var := by
    have renamedHead : (RawTerm.rename rawRenaming term).rootGenerator = Generator.gen_var := by
      rw [isVar]; rfl
    rwa [RawTerm.rename_rootGenerator] at renamedHead
  obtain ⟨sourceIndex, termIsVariable⟩ := eq_variableCell_of_headGenerator headIsVariable
  refine ⟨sourceIndex, termIsVariable, ?_⟩
  rw [termIsVariable, rename_variableCell] at isVar
  injection isVar with _generatorEq indexEq

/-- `levelCons` at a `weaken`-shifted index reads the tail vector at the original index.  `weaken` sends
`index` to `Fin.succ index`, which `levelCons` matches in its `priorValue + 1` arm and projects back to
`tailLevels index` (the residual `Fin` proof is irrelevant, so the equality is definitional).  This is the
computation the binder-extension preservation needs after the inversion pins a looked-up type variable's
index to `weaken sourceIndex`. -/
theorem levelCons_weaken {scope : Nat} (headLevel : Nat)
    (tailLevels : Fin scope → Nat) (index : Fin scope) :
    levelCons headLevel tailLevels (RawRenaming.weaken index) = tailLevels index :=
  rfl

/-- **Binder-extension preservation** — a consistent stratification stays consistent when the context is
extended by one binder whose own type, if it is a type variable, sits one level below the fresh head level.

Given `consistent : ConsistentStratification contextLevels context` and the local edge condition
`domainConstraint` (when the new binding's type `domainCode` IS a variable `var sourceIndex`, that source sits
at `headLevel + 1`), the extended context `context.cons domainCode` is consistently stratified by
`levelCons headLevel contextLevels`.  Both lookup positions reduce through the rename-variable inversion:
the newest binding (index 0) looks up `weaken domainCode`, so its type variable comes from `domainCode` and
the constraint applies; an older binding (index `position + 1`) looks up `weaken (context.lookup …)`, so its
type variable comes from the tail and `consistent` applies.  In both cases the looked-up type variable's
index is `weaken sourceIndex`, on which `levelCons` reads the original `contextLevels sourceIndex`
(`levelCons_weaken`), leaving exactly the `+ 1` edge each branch supplies. -/
theorem ConsistentStratification.cons {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    (consistent : ConsistentStratification contextLevels context)
    {headLevel : Nat} {domainCode : RawTerm scope}
    (domainConstraint : ∀ sourceIndex : Fin scope,
      domainCode = variableCell sourceIndex → contextLevels sourceIndex = headLevel + 1) :
    ConsistentStratification (levelCons headLevel contextLevels) (context.cons domainCode) := by
  intro termIndex typeIndex isVarType
  match termIndex with
  | ⟨0, isLt⟩ =>
      rw [TypingContext.lookup_cons_zero context domainCode isLt] at isVarType
      obtain ⟨sourceIndex, domainIsVariable, weakenedIndexEq⟩ :=
        rename_eq_variableCell_inversion RawRenaming.weaken isVarType
      rw [← weakenedIndexEq]
      show levelCons headLevel contextLevels (RawRenaming.weaken sourceIndex) = headLevel + 1
      rw [levelCons_weaken]
      exact domainConstraint sourceIndex domainIsVariable
  | ⟨position + 1, isLtSucc⟩ =>
      rw [TypingContext.lookup_cons_succ context domainCode position isLtSucc] at isVarType
      obtain ⟨sourceIndex, lookupIsVariable, weakenedIndexEq⟩ :=
        rename_eq_variableCell_inversion RawRenaming.weaken isVarType
      rw [← weakenedIndexEq]
      show levelCons headLevel contextLevels (RawRenaming.weaken sourceIndex)
        = contextLevels ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩ + 1
      rw [levelCons_weaken]
      exact consistent ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩ sourceIndex lookupIsVariable

end FX1Poly.Typed
