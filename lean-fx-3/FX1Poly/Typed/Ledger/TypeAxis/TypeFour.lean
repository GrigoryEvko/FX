import FX1Poly.Tier0.Term.Core.RawTermChildrenUnique
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDesc
import FX1Poly.Typed.Engine.WfContext.WfContextDesc
import FX1Poly.Typed.Engine.IsTypeDesc.IsTypeDescDecidableGeneric
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable

/-! # type-4 — indexed W-types, induction-recursion, induction-induction (the advanced-scheme rung)

The advanced-inductive-scheme rung of the type axis.  Task #1516 names THREE distinct schemes that go
beyond `type-1`'s simple initial algebras: indexed W-types (general indexed tree types), induction-recursion
(Dybjer-Setzer: a type defined simultaneously with a recursive function INTO an earlier type), and
induction-induction (a type together with a family indexed BY it, defined simultaneously — the Con/Ty
shape).  As an OBJECT-LEVEL type-theory feature, all three are DEFERRED (no typed former ships).  What this
ledger genuinely BACKS is the kernel's own META-LEVEL mutual structure — the Lean inductives and
description-driven judgment that are the in-kernel substitute for these schemes — plus the W-recursor reduct
demo's adequacy.  Like `type-1`/`type-2`/`type-3`, a NON-DUPLICATIVE cross-layer ledger ABOVE Typed: markers
+ `_isBacked` referencing named shipped theorems.

## What this rung backs (each `= true`, conjoined with named shipped theorems)

  * **`fxType_hasScopedSyntaxMutual`** — the well-scoped MUTUAL inductive `RawTerm` / `RawTermChildren` (term
    and child-spine defined simultaneously, the spine indexed by the `List Nat` binder-shift word).  This is
    the kernel's deliberate SUBSTITUTE for the induction-induction that Lean's mutual-index rule forbids
    (sibling index references are rejected — see the deferral below).  Backed by the structurality witness
    `RawTermChildren.eq_childNil` (`[]`-indexed spine is uniquely `childNil`).
  * **`fxType_hasDescriptionDrivenTyping`** — the META-LEVEL mutual judgment `HasTypeDesc` / `DescTelescope`
    (the description-driven typing judgment defined simultaneously with its premise-telescope, cross-
    referencing in constructor PREMISES): the closest in-kernel realization of inductive-inductive-style
    typing.  Backed by the description-table row `typingRuleDescOf_unitCode` (`rfl`) AND a concrete derivation
    THROUGH the mutual — the unit former types via `genFormation` + `DescTelescope.nil`.
  * **`fxType_hasStructuralMutualDecider`** — STRUCTURAL recursion over the mutual inductive: `IsTypeDesc` is
    decidable for any classifier under a formation-well-formed context
    (`IsTypeDesc.decidableOfWellFormedGeneric`, the cascade-free term↔telescope mutual decider), AND the
    decision is CONSTRUCTIVE — when the classifier is a type, the decider exhibits a witnessing level/flag at
    which it has a `HasTypeDesc` derivation (extracted from `IsTypeDesc.decideTypeGeneric`'s positive
    `Σ'`-witness).  The eliminator side of the mutual judgment.
  * **`fxType_hasInductiveInductiveCrossRef`** — the mutual judgment's cross-reference genuinely FIRES: the
    one-child `list` former types through `genFormation` over a `DescTelescope.cons` whose `headTyped` premise
    is the unit former itself (`HasTypeDesc` / `DescTelescope.cons` / `typingRuleDescOf_listCode` /
    `typingRuleDescOf_unitCode`).  This exercises the constructor that references `HasTypeDesc` in its
    premises — the in-engine induction-induction the nullary case never reaches.
  * **`fxType_hasWStyleRecursorDemo`** — EXT-1 readiness: the W-RECURSOR reduct skeleton COMPUTES.  The demo
    rule `wStyleRecursiveBinderDemoRule` fires to a fresh-binder reduct
    `lam(zeroBranch, app(pred↑, var 0))` — the `wRec (sup a f) ↝ step a f (λ x. wRec … (f x))` shape
    (`wStyleRecursiveBinderDemoRule_interpretsTarget`).

## What is deferred (the genuine object-level advanced-scheme frontier)

  * `fxType_hasIndexedWTypes` — OBJECT-LEVEL indexed W-types / indexed inductive families as a typed former.
    Only the demo reduct skeleton exists (`wStyleRecursiveBinderDemoRule`, built on `gen_natElim`, NOT
    registered in `iotaRuleTable`, no typing rule, no reducibility member); there is no W-former code, no
    indexed-container (shape `S` + position family `P : S → Type`) calculus.  Route: EXT-1 (W-types as rule
    rows) → `type-16` (the polynomial-functor calculus).  `= false`.
  * `fxType_hasInductionRecursion` — OBJECT-LEVEL induction-recursion (Dybjer-Setzer: a type defined
    simultaneously with a recursive function into a previously-given type).  FX's universe is morally
    IR-shaped (a Tarski universe IS the canonical IR example) but is mechanized as CODES plus a SEPARATELY
    defined decode — NOT the IR scheme; IR is reserved-only (`LogRelSpec`).  No IR codes / IR former.
    `= false`.
  * `fxType_hasInductionInduction` — OBJECT-LEVEL induction-induction (a type together with a family indexed
    BY it, defined simultaneously — Con/Ty).  Lean's mutual-index rule FORBIDS the sibling index references
    genuine II needs, which is exactly why the kernel uses the well-scoped Nat-indexed `RawTerm` /
    `RawTermChildren` mutual (backed above) as the substitute.  An object-level II former routes through the
    QIIT encoding at `type-5`.  `= false`.

## Zero-axiom verification

Four `Bool` markers `:= true` (each `_isBacked` conjunction closed by `rfl` + named shipped theorems:
`RawTermChildren.eq_childNil`; `typingRuleDescOf_unitCode` + `HasTypeDesc.genFormation`/`DescTelescope.nil`;
`IsTypeDesc.decidableOfWellFormedGeneric`; `wStyleRecursiveBinderDemoRule_interpretsTarget`) and three
`:= false` deferral markers.  All cited substrate is `FX1Poly.Core` / `FX1Poly.Typed`, funext-free.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditTier0TypeFour.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core
open FX1Poly.Typed
open FX1Poly.Universe

/-! ## The well-scoped mutual syntax (the II substitute) -/

/-- **Honesty marker** — `type-4` (well-scoped mutual syntax).  `RawTerm` / `RawTermChildren` is a genuine
MUTUAL inductive (term + child-spine defined simultaneously, spine indexed by the binder-shift word) — the
kernel's substitute for the induction-induction Lean's mutual-index rule forbids.  Backed in
`fxType_scopedSyntaxMutual_isBacked`.  `= true`. -/
def fxType_hasScopedSyntaxMutual : Bool := true

/-- ★ **Backed flip (well-scoped mutual syntax).**  The marker is `true` AND the child-spine half of the
mutual is structural: the `[]`-indexed spine has the unique inhabitant `childNil`
(`RawTermChildren.eq_childNil`). -/
theorem fxType_scopedSyntaxMutual_isBacked :
    fxType_hasScopedSyntaxMutual = true
      ∧ (∀ {scope : Nat} (children : RawTermChildren [] scope), children = .childNil) := by
  refine ⟨rfl, ?_⟩
  intro scope children
  exact RawTermChildren.eq_childNil children

/-! ## The description-driven mutual typing judgment (the inductive-inductive-style core) -/

/-- **Honesty marker** — `type-4` (description-driven mutual typing).  `HasTypeDesc` / `DescTelescope` is the
META-LEVEL mutual judgment (typing judgment defined simultaneously with its premise-telescope) — the closest
in-kernel realization of inductive-inductive-style typing.  Backed in
`fxType_descriptionDrivenTyping_isBacked`.  `= true`. -/
def fxType_hasDescriptionDrivenTyping : Bool := true

/-- ★ **Backed flip (description-driven mutual typing).**  The marker is `true` AND (i) the nullary unit
description row is the flag-pinned `nullaryFormerOutput` (`typingRuleDescOf_unitCode`); (ii) the unit former
genuinely types THROUGH the mutual — `genFormation` consuming that row with an empty `DescTelescope.nil`
premise yields `Unit : Type@0(standard)`. -/
theorem fxType_descriptionDrivenTyping_isBacked :
    fxType_hasDescriptionDrivenTyping = true
      ∧ typingRuleDescOf .gen_unitCode = some { outputType := nullaryFormerOutput }
      ∧ (∀ {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
          (_flag : UniverseFlag),
          HasTypeDesc profile context (.mkGen .gen_unitCode () .childNil)
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) := by
  refine ⟨rfl, typingRuleDescOf_unitCode, ?_⟩
  intro profile scope context flag
  exact HasTypeDesc.genFormation context .gen_unitCode () .childNil [] flag
    { outputType := nullaryFormerOutput } typingRuleDescOf_unitCode
    (DescTelescope.nil (profile := profile) (baseScope := scope) (currentDepth := 0) context flag)

/-! ## Structural recursion over the mutual (the eliminator side) -/

/-- **Honesty marker** — `type-4` (structural mutual decider).  STRUCTURAL recursion over the mutual
inductive: `IsTypeDesc` is decidable for any classifier under a formation-well-formed context (the cascade-
free term↔telescope mutual decider).  Backed in `fxType_structuralMutualDecider_isBacked`.  `= true`. -/
def fxType_hasStructuralMutualDecider : Bool := true

/-- ★ **Backed flip (structural mutual decider).**  The marker is `true` AND (i) formation type-hood is
decidable under a formation-well-formed context — for every classifier, `IsTypeDesc` either holds or is
refuted (`IsTypeDesc.decidableOfWellFormedGeneric`); (ii) the decision is CONSTRUCTIVE — when the classifier
IS a type, the decider EXHIBITS a witnessing level / flag at which the classifier has a `HasTypeDesc`
derivation (extracted from `IsTypeDesc.decideTypeGeneric`, whose positive side carries that `Σ'`-witness),
strictly more than the bare disjunction. -/
theorem fxType_structuralMutualDecider_isBacked :
    fxType_hasStructuralMutualDecider = true
      ∧ (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
          (_wellFormed : WfContextDesc context) (classifier : RawTerm scope),
          IsTypeDesc profile context classifier ∨ ¬ IsTypeDesc profile context classifier)
      ∧ (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
          (_wellFormed : WfContextDesc context) (classifier : RawTerm scope),
          IsTypeDesc profile context classifier →
          ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
            HasTypeDesc profile context classifier (universeCodeCell levelExpr flag)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro profile scope context wellFormed classifier
    cases IsTypeDesc.decidableOfWellFormedGeneric wellFormed classifier with
    | isTrue isType => exact Or.inl isType
    | isFalse notType => exact Or.inr notType
  · intro profile scope context wellFormed classifier isType
    cases IsTypeDesc.decideTypeGeneric wellFormed classifier with
    | inl witness => exact ⟨witness.1, witness.2.1, witness.2.2⟩
    | inr refute => exact absurd isType refute

/-! ## The W-recursor reduct demo (EXT-1 readiness) -/

/-- **Honesty marker** — `type-4` (W-recursor reduct demo).  The W-RECURSOR reduct skeleton COMPUTES: the
demo rule fires to the fresh-binder reduct `lam(zeroBranch, app(pred↑, var 0))`, the
`wRec (sup a f) ↝ step a f (λ x. wRec … (f x))` shape (EXT-1 readiness).  Backed in
`fxType_wStyleRecursorDemo_isBacked`.  `= true`. -/
def fxType_hasWStyleRecursorDemo : Bool := true

/-- ★ **Backed flip (W-recursor reduct demo).**  The marker is `true` AND for every motive / branches /
predecessor the W-style demo rule's `interpretTarget?` returns SOME concrete fresh-binder reduct
(`wStyleRecursiveBinderDemoRule_interpretsTarget`). -/
theorem fxType_wStyleRecursorDemo_isBacked :
    fxType_hasWStyleRecursorDemo = true
      ∧ (∀ {scope : Nat} (motive : RawTerm (scope + 1))
          (zeroBranch predecessor : RawTerm scope) (succBranch : RawTerm (scope + 2)),
          ∃ reduct, wStyleRecursiveBinderDemoRule.interpretTarget? ()
            (.childCons motive
              (.childCons zeroBranch
                (.childCons succBranch
                  (.childCons
                    (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                    .childNil))))
            = some reduct) := by
  refine ⟨rfl, ?_⟩
  intro scope motive zeroBranch predecessor succBranch
  exact ⟨_, wStyleRecursiveBinderDemoRule_interpretsTarget motive zeroBranch predecessor succBranch⟩

/-! ## The inductive-inductive cross-reference fires (the genuine II-in-the-engine demo) -/

/-- **Honesty marker** — `type-4` (inductive-inductive cross-reference).  The META-LEVEL mutual judgment's
cross-reference genuinely FIRES: `DescTelescope.cons` — the telescope constructor whose `headTyped` premise is
itself a `HasTypeDesc` derivation — is exercised by a ≥1-child former, not just the nullary `DescTelescope.nil`
case.  This is the in-engine realization of induction-induction (the typing judgment IS inductive-inductive),
distinct from the deferred OBJECT-LEVEL II former below.  Backed in
`fxType_inductiveInductiveCrossRef_isBacked`.  `= true`. -/
def fxType_hasInductiveInductiveCrossRef : Bool := true

/-- ★ **Backed flip (inductive-inductive cross-reference).**  The marker is `true` AND a ONE-CHILD former
(`list`) types THROUGH the mutual by consuming a `DescTelescope.cons` whose `headTyped` is a real former
derivation: `list(Unit)` types via `genFormation` over a `DescTelescope.cons` whose head premise is the unit
former itself (`HasTypeDesc.genFormation` + `DescTelescope.cons` + `typingRuleDescOf_listCode` +
`typingRuleDescOf_unitCode`).  This fires the constructor (`DescTelescope.cons`) that references `HasTypeDesc`
in its premises — the genuine inductive-inductive cross-reference the nullary case never exercises. -/
theorem fxType_inductiveInductiveCrossRef_isBacked :
    fxType_hasInductiveInductiveCrossRef = true
      ∧ (∀ {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope),
          HasTypeDesc profile context
            (.mkGen .gen_listCode () (.childCons (.mkGen .gen_unitCode () .childNil) .childNil))
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) := by
  refine ⟨rfl, ?_⟩
  intro profile scope context
  exact HasTypeDesc.genFormation context .gen_listCode ()
    (.childCons (.mkGen .gen_unitCode () .childNil) .childNil)
    [LevelExpr.lzero] UniverseFlag.standard
    { outputType := universeFormerOutput } typingRuleDescOf_listCode
    (DescTelescope.cons (profile := profile) (baseScope := scope) (currentDepth := 0) context
      (.mkGen .gen_unitCode () .childNil)
      LevelExpr.lzero [] UniverseFlag.standard .childNil
      (HasTypeDesc.genFormation context .gen_unitCode () .childNil [] UniverseFlag.standard
        { outputType := nullaryFormerOutput } typingRuleDescOf_unitCode
        (DescTelescope.nil (profile := profile) (baseScope := scope) (currentDepth := 0) context
          UniverseFlag.standard))
      (DescTelescope.nil (profile := profile) (baseScope := scope) (currentDepth := 1)
        (context.cons (.mkGen .gen_unitCode () .childNil)) UniverseFlag.standard))

/-! ## Honesty markers (the deferred object-level advanced-scheme frontier) -/

/-- **Honesty marker.**  OBJECT-LEVEL indexed W-types / indexed inductive families as a typed former — only
the demo reduct skeleton (`wStyleRecursiveBinderDemoRule`, on `gen_natElim`, unregistered, no typing rule, no
reducibility member); no W-former code, no indexed-container (shape + position family) calculus.  Route: EXT-1
(W-types as rows) → `type-16` (polynomial functors).  Deferred.  `= false`. -/
def fxType_hasIndexedWTypes : Bool := false

/-- **Honesty marker.**  OBJECT-LEVEL induction-recursion (Dybjer-Setzer) — FX's universe is morally
IR-shaped (a Tarski universe IS the canonical IR example) but is mechanized as Tarski CODES plus a SEPARATELY
defined decode, NOT the IR scheme; IR is reserved-only (`LogRelSpec`).  No IR codes / IR former.  Deferred.
`= false`. -/
def fxType_hasInductionRecursion : Bool := false

/-- **Honesty marker.**  OBJECT-LEVEL induction-induction (a type together with a family indexed BY it, the
Con/Ty shape) — Lean's mutual-index rule FORBIDS the sibling index references genuine II needs (which is why
the kernel uses the well-scoped `RawTerm` / `RawTermChildren` mutual, backed above, as the substitute).  An
object-level II former routes through the QIIT encoding at `type-5`.  Deferred.  `= false`. -/
def fxType_hasInductionInduction : Bool := false

end FX1Poly.Tier0
