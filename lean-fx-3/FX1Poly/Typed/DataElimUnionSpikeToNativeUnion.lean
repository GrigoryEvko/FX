import FX1Poly.Typed.DataIntroNativeRowConversion
import FX1Poly.Typed.DataElimUnionSpike

/-! # FX1Poly/Typed/DataElimUnionSpikeToNativeUnion — NATIVE-36: the NON-recursive data-eliminator
    spike transfers INTO the real union judgment

The NATIVE-28 spike (`DataElimUnionSpike`) locked the three non-recursive data-eliminator row shapes
(two-branch match / path-induction / projection).  NATIVE-36 lands native twins of those rows IN
`HasTypeNativeUnion` as the `twoBranchMatchElim` / `pathInductionElim` / `projectionElim` arms (plus the
`ofOptionIntro` / `ofEitherIntro` / `ofIdIntro` / `ofPairIntro` scrutinee embeddings).  This file proves
the TRANSFER: every spike derivation maps to a `HasTypeNativeUnion` typing at the same subject and
classifier.  Mirrors `RecursiveElimUnionSpike.toNativeUnion` exactly.

## The transfer

`DataElimUnionSpike.toNativeUnion` — `induction` over the spike's eight arms:

  * `ofUnion unionTyped` — the embedded union typing IS the witness.
  * `ofOptionIntro` / `ofEitherIntro` / `ofIdIntro` / `ofPairIntro` — the union's own scrutinee
    embedding arms (identity-ish embed).
  * `twoBranchMatchRow` / `pathInductionRow` / `projectionRow` — the SPIKE's table hit
    (`twoBranchMatchRuleOf generator = some rule` etc.) is inverted by the spike-table-inversion lemmas
    here (decidable case analysis over the OPTION table, never an elimination over a derivation), pinning
    the generator and the spike row; the spike row's cell builders are DEFINITIONALLY the native row's,
    so the union arm fires with the IH-translated premises at the (defeq) native row.

## Zero-axiom

The spike-table-inversion lemmas are `by_cases` / `if_pos` / `if_neg` / `Option.some.inj` /
`Option.noConfusion` over the if-then-else tables; the transfer is `induction` over the spike's arms with
those lemmas feeding the native arms at definitionally-equal cells.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditNativeWaveUnionResidency.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Spike-table inversion (the transfer ingredient; decidable, no derivation elimination) -/

/-- **A spike two-branch-match table hit pins one of the three spike rows.**  Decidable case analysis
over the spike's `twoBranchMatchRuleOf` if-then-else table. -/
theorem twoBranchMatchRuleOf_spikeCases {generator : Generator} {rule : TwoBranchMatchElimRule}
    (tableHit : twoBranchMatchRuleOf generator = some rule) :
    (generator = .gen_boolElim ∧ rule = boolElimMatchRule) ∨
    (generator = .gen_optionMatch ∧ rule = optionMatchMatchRule) ∨
    (generator = .gen_eitherMatch ∧ rule = eitherMatchMatchRule) := by
  unfold twoBranchMatchRuleOf at tableHit
  by_cases isBoolElim : generator = .gen_boolElim
  · rw [if_pos isBoolElim] at tableHit
    exact Or.inl ⟨isBoolElim, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isBoolElim] at tableHit
    by_cases isOptionMatch : generator = .gen_optionMatch
    · rw [if_pos isOptionMatch] at tableHit
      exact Or.inr (Or.inl ⟨isOptionMatch, (Option.some.inj tableHit).symm⟩)
    · rw [if_neg isOptionMatch] at tableHit
      by_cases isEitherMatch : generator = .gen_eitherMatch
      · rw [if_pos isEitherMatch] at tableHit
        exact Or.inr (Or.inr ⟨isEitherMatch, (Option.some.inj tableHit).symm⟩)
      · rw [if_neg isEitherMatch] at tableHit
        exact absurd tableHit (by intro hit; cases hit)

/-- **A spike path-induction table hit pins the idJ spike row.** -/
theorem pathInductionRuleOf_spikeCases {generator : Generator} {rule : PathInductionElimRule}
    (tableHit : pathInductionRuleOf generator = some rule) :
    generator = .gen_idJ ∧ rule = idJPathInductionRule := by
  unfold pathInductionRuleOf at tableHit
  by_cases isIdJ : generator = .gen_idJ
  · rw [if_pos isIdJ] at tableHit
    exact ⟨isIdJ, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isIdJ] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- **A spike projection table hit pins one of the two spike rows.** -/
theorem projectionRuleOf_spikeCases {generator : Generator} {rule : ProjectionElimRule}
    (tableHit : projectionRuleOf generator = some rule) :
    (generator = .gen_fst ∧ rule = fstProjectionRule) ∨
    (generator = .gen_snd ∧ rule = sndProjectionRule) := by
  unfold projectionRuleOf at tableHit
  by_cases isFst : generator = .gen_fst
  · rw [if_pos isFst] at tableHit
    exact Or.inl ⟨isFst, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isFst] at tableHit
    by_cases isSnd : generator = .gen_snd
    · rw [if_pos isSnd] at tableHit
      exact Or.inr ⟨isSnd, (Option.some.inj tableHit).symm⟩
    · rw [if_neg isSnd] at tableHit
      exact absurd tableHit (by intro hit; cases hit)

/-! ## ★ The spike→union transfer -/

/-- **★ Every NATIVE-28 `DataElimUnionSpike` derivation maps to a `HasTypeNativeUnion` typing at the
same subject and classifier.**  Induction over the spike's eight arms; the four intro embeddings map to
the union's matching embedding arms, the three table rows map to the union's matching table arms via the
spike-table-inversion lemmas at definitionally-equal cells.  Mirrors `RecursiveElimUnionSpike.toNativeUnion`. -/
theorem DataElimUnionSpike.toNativeUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : DataElimUnionSpike profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  induction derivation with
  | ofUnion unionTyped => exact unionTyped
  | ofOptionIntro optionTyped => exact optionTyped.toNativeRows
  | ofEitherIntro eitherTyped => exact eitherTyped.toNativeRows
  | ofIdIntro idTyped => exact idTyped.toNativeRows
  | ofPairIntro pairTyped => exact pairTyped.toNativeRows
  | twoBranchMatchRow generator rule motive firstBranch secondBranch scrutinee
      typeParamA typeParamB resultType isTwoBranchMatch
      _scrutineeTyped _firstTyped _secondTyped scrutineeUnion firstUnion secondUnion =>
      rcases twoBranchMatchRuleOf_spikeCases isTwoBranchMatch with
        ⟨_generatorEq, ruleEq⟩ | ⟨_generatorEq, ruleEq⟩ | ⟨_generatorEq, ruleEq⟩
      · subst ruleEq
        exact HasTypeNativeUnion.twoBranchMatchElim _ .gen_boolElim boolElimNativeMatchRule
          motive firstBranch secondBranch scrutinee typeParamA typeParamB resultType rfl
          scrutineeUnion firstUnion secondUnion
      · subst ruleEq
        exact HasTypeNativeUnion.twoBranchMatchElim _ .gen_optionMatch optionMatchNativeMatchRule
          motive firstBranch secondBranch scrutinee typeParamA typeParamB resultType rfl
          scrutineeUnion firstUnion secondUnion
      · subst ruleEq
        exact HasTypeNativeUnion.twoBranchMatchElim _ .gen_eitherMatch eitherMatchNativeMatchRule
          motive firstBranch secondBranch scrutinee typeParamA typeParamB resultType rfl
          scrutineeUnion firstUnion secondUnion
  | pathInductionRow generator rule motive baseCase witness typeCode endpoint resultType
      isPathInduction _witnessTyped _baseCaseTyped witnessUnion baseCaseUnion =>
      rcases pathInductionRuleOf_spikeCases isPathInduction with ⟨_generatorEq, ruleEq⟩
      subst ruleEq
      exact HasTypeNativeUnion.pathInductionElim _ .gen_idJ idJNativePathInductionRule
        motive baseCase witness typeCode endpoint resultType rfl witnessUnion baseCaseUnion
  | projectionRow generator rule pairTerm firstType secondType isProjection _pairTyped pairUnion =>
      rcases projectionRuleOf_spikeCases isProjection with
        ⟨_generatorEq, ruleEq⟩ | ⟨_generatorEq, ruleEq⟩
      · subst ruleEq
        exact HasTypeNativeUnion.projectionElim _ .gen_fst fstNativeProjectionRule
          pairTerm firstType secondType rfl pairUnion
      · subst ruleEq
        exact HasTypeNativeUnion.projectionElim _ .gen_snd sndNativeProjectionRule
          pairTerm firstType secondType rfl pairUnion

/-! ## The transfer gate -/

/-- **The NATIVE-36 data-elim transfer evidence record.**  An inhabitant certifies the non-recursive
data-eliminator spike transfers wholesale into the real union. -/
structure DataElimUnionTransferEvidence (profile : PolyProfile) : Prop where
  /-- Every spike derivation transfers to the union. -/
  spikeTransfers : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    DataElimUnionSpike profile context subject classifier →
    HasTypeNativeUnion profile context subject classifier

/-- **★ The NATIVE-36 data-elim transfer gate** — inhabited by the shipped witness. -/
theorem dataElimUnionTransferWitness {profile : PolyProfile} :
    DataElimUnionTransferEvidence profile where
  spikeTransfers := fun derivation => derivation.toNativeUnion

end FX1Poly.Typed
