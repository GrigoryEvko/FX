import LeanFX2.Term.StrengtheningImage.TotalOnWeakenCastAdvanced

/-! # Term/StrengtheningImage/TotalOnWeakenHeadlines

Closed atomic unweaken equations and bridge from aggregator totality to total-on-weaken.
-/

namespace LeanFX2

namespace Term

/-- BIG-ASS THEOREM headline — closed-atomic unweaken? recovers source.

For each of the 7 closed-atomic ctors, `Term.unweaken?` applied to
`Term.weaken newType (Term.<ctor>)` returns `some (Term.<ctor>)`.
Direct `rfl`-witnesses because the dispatcher's success and the
type/raw alignment unfolds atomically. -/
theorem unweaken?_weaken_unit {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.unit (context := context))) = some Term.unit := by
  rfl

theorem unweaken?_weaken_boolTrue {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.boolTrue (context := context))) = some Term.boolTrue := by
  rfl

theorem unweaken?_weaken_boolFalse {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.boolFalse (context := context))) = some Term.boolFalse := by
  rfl

theorem unweaken?_weaken_natZero {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.natZero (context := context))) = some Term.natZero := by
  rfl

theorem unweaken?_weaken_interval0 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.interval0 (context := context))) = some Term.interval0 := by
  rfl

theorem unweaken?_weaken_interval1 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.interval1 (context := context))) = some Term.interval1 := by
  rfl

theorem unweaken?_weaken_var {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) (position : Fin scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.var (context := context) position)) =
      some (Term.var position) := by
  rfl

/-- Phase 2.A: 0-IH parametric atomic — `universeCode` equation form. -/
theorem unweaken?_weaken_universeCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.universeCode (context := context) innerLevel outerLevel
          cumulOk levelLe)) =
      some (Term.universeCode innerLevel outerLevel cumulOk levelLe) := by
  rfl


/-- Genuine iff (atomic-base version) — non-tautological strengthening
of `weaken_image_iff_strengthenTyped?_some`.

The original Step-3 iff is structural sugar around `Term.unweaken?`'s
definition (both witnesses succeed under identical conditions because
`unweaken?` pattern-matches on `strengthenTyped?`).  This version
adds genuine totality content: on a CLOSED ATOMIC SOURCE TERM (one of
the 7 atomics), the iff witnesses are UNCONDITIONALLY inhabited — no
side hypothesis required.

Consumers proving Step.eta-cascade subject reduction on closed atomic
source terms can invoke this directly. -/
theorem weaken_image_iff_strengthenTyped?_some_TRUE_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    (∃ originalTerm,
        Term.unweaken? (Term.weaken (context := context) newType
            (Term.unit (context := context))) = some originalTerm) ∧
      ∃ result,
        strengthenTyped? (Term.weaken (context := context) newType
            (Term.unit (context := context))) = some result :=
  ⟨⟨Term.unit, unweaken?_weaken_unit newType⟩,
   ⟨partialStrengthenTypedUnit
      (ContextStrengthening.dropNewest context newType), rfl⟩⟩

/-! ## Phase X bridge: IsAggregatorTotal (weakened term) → IsTotalOnWeaken.

`IsTotalOnWeaken sourceTerm` asserts that the dispatcher succeeds on
the WEAKENED form `Term.weaken newType sourceTerm` for any
`newType : Ty level scope`.  `IsAggregatorTotal weakenedTerm` is the
strictly stronger universal-strengthening statement on a
sourceTerm-bearing weakenedTerm.

This bridge specializes the universal statement to the canonical
`dropNewest` strengthening: when `IsAggregatorTotal (Term.weaken
newType sourceTerm)` holds for every choice of `newType`, the
`dropNewest context newType` strengthening witnesses
`IsTotalOnWeaken sourceTerm` because the source/raw indices of
`Term.weaken newType sourceTerm` are already weakened forms of
`sourceTerm`'s indices, and `Ty.strengthen?_weaken` /
`RawTerm.strengthen?_weaken` discharge the index witnesses.

This is the load-bearing path for the three binder wrappers
(`lam`, `lamPi`, `pathLam`) whose body strengthens through the
LIFTED `dropNewest`: the body's `IsAggregatorTotal` IH supplies the
universal-strengthening parameter, the binder's
`isAggregatorTotal_<binder>` derivation lifts that into
`IsAggregatorTotal (Term.<binder> ...)`, and this bridge converts
the conclusion into the consumer-facing `IsTotalOnWeaken`
predicate. -/
theorem isTotalOnWeaken_of_weaken_isAggregatorTotal
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (weakenTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal (Term.weaken newType sourceTerm)) :
    IsTotalOnWeaken sourceTerm := by
  intro newType
  exact weakenTotal newType
    (ContextStrengthening.dropNewest context newType)
    (Ty.strengthen?_weaken sourceType)
    (RawTerm.strengthen?_weaken sourceRaw)

/-! ## Phase X: the three binder wrappers.

The non-binder ctors (the 75 already-shipped `isTotalOnWeaken_<ctor>`
theorems) all take `IsTotalOnWeaken child` IHs on their recursive
children — the narrow predicate suffices because the dispatcher's
recursion on a non-binder child uses `dropNewest`, matching the
predicate's `Term.weaken newType` shape directly.

The three binder ctors (`lam`, `lamPi`, `pathLam`) break this
pattern: their body's strengthening goes through `strengthening.lift`,
not `dropNewest`.  The narrow `IsTotalOnWeaken body` predicate cannot
transport through the lift; the strictly stronger
`IsAggregatorTotal body` (universal over all strengthenings of body)
must take its place as the binder IH.

Each wrapper's hypothesis is `weakenedBinderTotal`:
`∀ newType, IsAggregatorTotal (Term.weaken newType (Term.<binder> ...))`.
Downstream, this is constructed by:
1. taking `bodyTotal : IsAggregatorTotal body`,
2. transporting it under the binder's required renaming
   (`(weakenStep _).lift _` for the body of a weakened binder) — the
   typed rename-compatibility transport, ~78-case structural
   recursion, lives in the `Term.rename` cascade,
3. lifting through `isAggregatorTotal_<binder>`,
4. and arriving at the wrapper's `weakenedBinderTotal` hypothesis.

The bridge `isTotalOnWeaken_of_weaken_isAggregatorTotal` then
specializes the universal statement to `dropNewest` at each
`newType`, recovering `IsTotalOnWeaken (Term.<binder> ...)`. -/

/-- Binder totality wrapper: `Term.lam`.

Takes the per-`newType` `IsAggregatorTotal` on the weakened lam term,
which encapsulates the rename-transport of body's
`IsAggregatorTotal` through the dispatcher's lifted strengthening.
Converts to the consumer-facing `IsTotalOnWeaken` via the canonical
`dropNewest` specialization (the Phase X bridge above). -/
theorem isTotalOnWeaken_lam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {body : Term (context.cons domainType) codomainType.weaken bodyRaw}
    (weakenedLamTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal
          (Term.weaken newType
            (Term.lam (context := context) (domainType := domainType)
              (codomainType := codomainType) body))) :
    IsTotalOnWeaken
      (Term.lam (context := context) (domainType := domainType)
        (codomainType := codomainType) body) :=
  isTotalOnWeaken_of_weaken_isAggregatorTotal weakenedLamTotal

/-- Binder totality wrapper: `Term.lamPi`.

Dependent-Pi lambda; body lives at the lifted codomain inside the
binder.  Same structural shape as `isTotalOnWeaken_lam` modulo the
codomain's scope — proof is one application of the Phase X bridge. -/
theorem isTotalOnWeaken_lamPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {body : Term (context.cons domainType) codomainType bodyRaw}
    (weakenedLamPiTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal
          (Term.weaken newType
            (Term.lamPi (context := context) (domainType := domainType)
              (codomainType := codomainType) body))) :
    IsTotalOnWeaken
      (Term.lamPi (context := context) (domainType := domainType)
        (codomainType := codomainType) body) :=
  isTotalOnWeaken_of_weaken_isAggregatorTotal weakenedLamPiTotal

/-- Binder totality wrapper: `Term.pathLam`.

Cubical path lambda; body binds an interval slot with carrier
weakened.  Same Phase X bridge specialization as the other two
binders. -/
theorem isTotalOnWeaken_pathLam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {body :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw}
    (weakenedPathLamTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal
          (Term.weaken newType
            (Term.pathLam (context := context) modeIsUnivalent carrierType
              leftEndpoint rightEndpoint body))) :
    IsTotalOnWeaken
      (Term.pathLam (context := context) modeIsUnivalent carrierType
        leftEndpoint rightEndpoint body) :=
  isTotalOnWeaken_of_weaken_isAggregatorTotal weakenedPathLamTotal

end Term

end LeanFX2
