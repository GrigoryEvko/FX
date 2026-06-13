import FX1Poly.Typed.GeneratorSemanticTier

/-! # FX1Poly/Typed/NativityLedger — every live generator's semantics is a table row (NATIVE-61)

The nativity capstone-prerequisite.  The kernel's "one-engine" thesis is that every generator the
semantic-tier classifier brands `.live` has its semantics carried by a RULE TABLE — its STATIC
semantics by the typing-table union (`hasSomeTypingRule`, which NATIVE-40 rewrote as a pure
table-`isSome` over `typingRuleDescOf`/`introRuleDescOf`/`elimRuleDescOf`/`baseTypeRuleDescOf`/
`flatTypingRuleDescOf`/`termIndexedFormerRuleDescOf`, zero decides), and its OPERATIONAL semantics by
the reduction-table redex classifier (`Generator.hasRedexHead`, derived from `iotaRuleTable`).  No
bespoke per-generator arm carries any live generator's semantics — the tables do.

`semanticTier g = .live` is BY DEFINITION `hasSomeTypingRule g || g.hasRedexHead`, so the coverage is
exact: a live generator is typed-by-a-table-row OR is a reduction-table redex head (or both).  This
file packages that into the single named `NativityLedger`, with the typing/reduction split and the
non-vacuity witnesses showing both axes are genuinely populated and genuinely distinct.

  * `liveGeneratorIsTabled` — ★ every live generator is tabled (typed-row or redex-row).
  * `tabledSplitsIntoTypingOrRedexRow` — the disjunction split (typing-table row vs reduction-table row).
  * `NativityLedger` / `nativityLedgerHolds` — the capstone object: coverage + split + the two
    complementary witnesses (`gen_boolTrue` typed-only-live, `gen_natElim` redex-only-live).

Zero-axiom; gated in `FX1PolyAudit/AuditNativityLedger.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- ★ **Every live generator is tabled.**  If the semantic tier is `.live`, then the generator is
typed by the table union (`hasSomeTypingRule`) OR is a reduction-table redex head
(`hasRedexHead`) — read straight off the `semanticTier` definition. -/
theorem liveGeneratorIsTabled {g : Generator} (live : semanticTier g = .live) :
    (hasSomeTypingRule g || g.hasRedexHead) = true := by
  by_cases htabled : (hasSomeTypingRule g || g.hasRedexHead) = true
  · exact htabled
  · exfalso
    have tieredFalse : (hasSomeTypingRule g || g.hasRedexHead) = false := by
      cases hcase : (hasSomeTypingRule g || g.hasRedexHead) with
      | true => exact absurd hcase htabled
      | false => rfl
    have reservedEq : semanticTier g = SemanticTier.reserved := by
      unfold semanticTier; rw [tieredFalse]; decide
    rw [reservedEq] at live
    exact SemanticTier.noConfusion live

/-- A tabled generator's semantics splits into a TYPING-table row (`hasSomeTypingRule`) or a
REDUCTION-table redex row (`hasRedexHead`). -/
theorem tabledSplitsIntoTypingOrRedexRow {g : Generator}
    (tabled : (hasSomeTypingRule g || g.hasRedexHead) = true) :
    hasSomeTypingRule g = true ∨ g.hasRedexHead = true := by
  cases htyped : hasSomeTypingRule g with
  | true => exact Or.inl rfl
  | false =>
    cases hredex : g.hasRedexHead with
    | true => exact Or.inr rfl
    | false =>
      rw [htyped, hredex] at tabled
      exact absurd tabled (by decide)

/-- **The nativity ledger** — the single object certifying that every live generator's semantics is a
rule-table row.  Coverage + split + the two complementary non-vacuity witnesses (a generator live by
its typing-table row only, and one live by its reduction-table redex row only). -/
structure NativityLedger : Prop where
  /-- Coverage: every live generator is tabled. -/
  everyLiveGeneratorIsTabled : ∀ {g : Generator}, semanticTier g = .live →
    (hasSomeTypingRule g || g.hasRedexHead) = true
  /-- The static/operational split: tabled = typing-table row OR reduction-table redex row. -/
  tabledSplits : ∀ {g : Generator}, (hasSomeTypingRule g || g.hasRedexHead) = true →
    hasSomeTypingRule g = true ∨ g.hasRedexHead = true
  /-- Non-vacuity (typing axis): `gen_boolTrue` is live via a typing-table row alone (no redex head). -/
  typedRowOnlyLiveWitness :
    hasSomeTypingRule .gen_boolTrue = true ∧ Generator.gen_boolTrue.hasRedexHead = false
      ∧ semanticTier .gen_boolTrue = .live
  /-- Non-vacuity (reduction axis): `gen_idStrictRec` is live via a reduction-table redex row alone
  (statically untyped — TAB-CLS folded the data recursors natElim/natRec/listElim into the typing union, so
  the strict Id recursor is the residual redex-only head). -/
  redexRowOnlyLiveWitness :
    Generator.gen_idStrictRec.hasRedexHead = true ∧ hasSomeTypingRule .gen_idStrictRec = false
      ∧ semanticTier .gen_idStrictRec = .live

/-- **★ The nativity ledger holds.**  Coverage by `liveGeneratorIsTabled`, split by
`tabledSplitsIntoTypingOrRedexRow`, the two witnesses by `rfl`.  Every live generator's semantics is a
table row — the one-engine thesis, machine-checked. -/
theorem nativityLedgerHolds : NativityLedger where
  everyLiveGeneratorIsTabled := liveGeneratorIsTabled
  tabledSplits := tabledSplitsIntoTypingOrRedexRow
  typedRowOnlyLiveWitness := ⟨rfl, rfl, rfl⟩
  redexRowOnlyLiveWitness := ⟨rfl, rfl, rfl⟩

end FX1Poly.Typed
