import FX1Poly.Core.DeltaRuleTable
import FX1Poly.Typed.SemanticTierSoundness

/-! # DeltaTypedSubjectReduction — RW-4: the typed δ-link (IOTA-T7 shape, told honestly)

`IotaRuleDesc` rows pair with `ElimRuleDesc` rows so a generic typed ι-SR
holds (IOTA-T7).  A δ-rule has the analogous typed obligation: if a typed
term δ-unfolds, the reduct must inhabit the same classifier — which, for a
constant `c := definiens`, reduces to a per-row **definiens-typing
certificate** (`c` and `definiens` share a classifier).

The CANONICAL demonstration `deltaRuleTable` deliberately keys on RESERVED
constant heads (`gen_hyperreal` / `gen_qubit`): generators with NO typing
row in any engine.  So a δ-redex cell is grown-UNTYPED, and typed δ-SR for
this table holds **vacuously** — the reduct-typing obligation never arises
because the subject is never typed in the first place.  That is the honest
typed tier: this δ-table is an OPERATIONAL-axis demonstration of the
rule-table schema (a reduction relation that is NOT wired into typing), so
the typed link is vacuous BY DESIGN.  A δ-rule on a LIVE constant head
would discharge a genuine definiens-typing certificate instead; the
schema (`DeltaRuleDesc`) admits both, this table exercises the reserved
case.

## Zero-axiom

The reserved-tier pins are `rfl` (`gen_hyperreal` / `gen_qubit` head no
typing engine and no redex rule), and the untyped facts compose the HON-7
`reservedTierUntypedByGrownEngine` soundness with the trivial head
equation.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation

/-! ## The canonical δ-constant heads are RESERVED -/

/-- Every constant head of the canonical δ table is `reserved` — no typing
engine types it and it fires no canonical redex.  The static reason the
typed δ-link is vacuous. -/
theorem deltaConstantHead_reserved {rule : DeltaRuleDesc}
    (isRow : rule ∈ deltaRuleTable) : semanticTier rule.constantHead = .reserved := by
  cases isRow with
  | head => rfl
  | tail _ isRow =>
      cases isRow with
      | head => rfl
      | tail _ isRow => cases isRow

/-! ## A δ-redex cell is grown-untyped -/

/-- **No δ-redex cell is grown-typed.**  A cell headed by a δ-table
constant has no `HasTypeDescPi` derivation at any classifier — the
operational δ relation never touches a typed subject at its root. -/
theorem deltaConstantCell_grownUntyped {rule : DeltaRuleDesc}
    (isRow : rule ∈ deltaRuleTable) {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (payload : rule.constantHead.payload scope)
    (children : RawTermChildren rule.constantHead.binderShifts scope)
    (classifier : RawTerm scope) :
    ¬ HasTypeDescPi profile context
        (.mkGen rule.constantHead payload children) classifier :=
  fun typed => reservedTierUntypedByGrownEngine (deltaConstantHead_reserved isRow) rfl typed

/-! ## ★ Typed δ-SR (vacuous for the reserved-head table) -/

/-- **★ Typed δ subject reduction for the canonical table — vacuously true.**
A δ-ROOT unfolding of a canonical δ-constant cell preserves the classifier:
the obligation is discharged by `exfalso`, because the subject (a reserved
constant cell) has no grown-typing derivation.  This is the honest typed
link for the reserved-head demonstration table — a δ-rule on a LIVE head
would discharge a real definiens-typing certificate here instead. -/
theorem deltaRootStep_typedSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {deltaSource deltaTarget classifier : RawTerm scope}
    (isCanonicalDeltaCell :
      deltaSource = .mkGen .gen_hyperreal () .childNil
      ∨ deltaSource = .mkGen .gen_qubit () .childNil)
    (typed : HasTypeDescPi profile context deltaSource classifier) :
    HasTypeDescPi profile context deltaTarget classifier := by
  exfalso
  cases isCanonicalDeltaCell with
  | inl hyperrealCell =>
      exact deltaConstantCell_grownUntyped hyperrealDeltaRow_memTable () .childNil classifier
        (hyperrealCell ▸ typed)
  | inr qubitCell =>
      exact deltaConstantCell_grownUntyped qubitDeltaRow_memTable () .childNil classifier
        (qubitCell ▸ typed)

end FX1Poly.Typed
