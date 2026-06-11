import FX1Poly.Typed.DataIntroNaryUnionSpike

/-! # FX1Poly/Typed/DataIntroNaryUnionSpikeToNativeUnion — NATIVE-36: the n-ary / recursive
    data-constructor intro spike transfers INTO the real union judgment

The NATIVE-34 spike (`DataIntroNaryUnionSpike`) locked the seven n-ary / recursive data-constructor
introduction row shapes.  NATIVE-36 lands native twins of those rows IN `HasTypeNativeUnion` as the
`recursiveUnaryIntro` / `recursiveBinaryIntro` / `pinnedUnaryIntro` / `nullaryFreeTypeIntro` /
`coproductIntro` / `nonDependentBinaryIntro` / `reflexiveIntro` arms (plus the `ofListIntro`
embedding — `ofNatIntro` and `ofDataIntro` already on the union).  This file proves the TRANSFER: every
spike derivation maps to a `HasTypeNativeUnion` typing at the same subject and classifier.  Mirrors
`RecursiveElimUnionSpike.toNativeUnion`.

## The transfer

`DataIntroNaryUnionSpike.toNativeUnion` — `induction` over the spike's eleven arms:

  * `ofUnion` — identity.  `ofNullaryDataIntro` → `ofDataIntro`.  `ofNatIntro` → `ofNatIntro`.
    `ofListIntro` → `ofListIntro`.
  * The two RECURSIVE rows (`recursiveUnaryRow` / `recursiveBinaryRow`) need the IH-translated recursive
    child / tail premise; the other five rows carry their grown / formedness premises verbatim.  Each
    row's table hit is inverted by the spike-table-inversion lemmas here (decidable case analysis over
    the OPTION tables), pinning the spike row; the spike row's cell builders are definitionally the
    native row's, so the union arm fires at the (defeq) native row.

## Zero-axiom

The spike-table-inversion lemmas are `by_cases` over the if-then-else tables; the transfer is `induction`
over the spike's arms with those lemmas feeding the native arms at definitionally-equal cells.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditNativeWaveUnionResidency.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Spike-table inversion (the transfer ingredients; decidable, no derivation elimination) -/

/-- **A spike recursive-unary table hit pins the natSucc spike row.** -/
theorem recursiveUnaryDataIntroRuleOf_spikeCases {generator : Generator}
    {rule : RecursiveUnaryDataIntroRule}
    (tableHit : recursiveUnaryDataIntroRuleOf generator = some rule) :
    generator = .gen_natSucc ∧ rule = natSuccRecursiveUnaryRule := by
  unfold recursiveUnaryDataIntroRuleOf at tableHit
  by_cases isNatSucc : generator = .gen_natSucc
  · rw [if_pos isNatSucc] at tableHit
    exact ⟨isNatSucc, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isNatSucc] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- **A spike recursive-binary table hit pins the listCons spike row.** -/
theorem recursiveBinaryDataIntroRuleOf_spikeCases {generator : Generator}
    {rule : RecursiveBinaryDataIntroRule}
    (tableHit : recursiveBinaryDataIntroRuleOf generator = some rule) :
    generator = .gen_listCons ∧ rule = listConsRecursiveBinaryRule := by
  unfold recursiveBinaryDataIntroRuleOf at tableHit
  by_cases isListCons : generator = .gen_listCons
  · rw [if_pos isListCons] at tableHit
    exact ⟨isListCons, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isListCons] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- **A spike pinned-unary table hit pins the optionSome spike row.** -/
theorem pinnedUnaryDataIntroRuleOf_spikeCases {generator : Generator}
    {rule : PinnedUnaryDataIntroRule}
    (tableHit : pinnedUnaryDataIntroRuleOf generator = some rule) :
    generator = .gen_optionSome ∧ rule = optionSomePinnedUnaryRule := by
  unfold pinnedUnaryDataIntroRuleOf at tableHit
  by_cases isOptionSome : generator = .gen_optionSome
  · rw [if_pos isOptionSome] at tableHit
    exact ⟨isOptionSome, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isOptionSome] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- **A spike nullary-free-type table hit pins the optionNone spike row.** -/
theorem nullaryFreeTypeDataIntroRuleOf_spikeCases {generator : Generator}
    {rule : NullaryFreeTypeDataIntroRule}
    (tableHit : nullaryFreeTypeDataIntroRuleOf generator = some rule) :
    generator = .gen_optionNone ∧ rule = optionNoneNullaryFreeTypeRule := by
  unfold nullaryFreeTypeDataIntroRuleOf at tableHit
  by_cases isOptionNone : generator = .gen_optionNone
  · rw [if_pos isOptionNone] at tableHit
    exact ⟨isOptionNone, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isOptionNone] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- **A spike coproduct table hit pins one of the two spike rows.** -/
theorem coproductDataIntroRuleOf_spikeCases {generator : Generator}
    {rule : CoproductDataIntroRule}
    (tableHit : coproductDataIntroRuleOf generator = some rule) :
    (generator = .gen_eitherInl ∧ rule = eitherInlCoproductRule) ∨
    (generator = .gen_eitherInr ∧ rule = eitherInrCoproductRule) := by
  unfold coproductDataIntroRuleOf at tableHit
  by_cases isInl : generator = .gen_eitherInl
  · rw [if_pos isInl] at tableHit
    exact Or.inl ⟨isInl, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isInl] at tableHit
    by_cases isInr : generator = .gen_eitherInr
    · rw [if_pos isInr] at tableHit
      exact Or.inr ⟨isInr, (Option.some.inj tableHit).symm⟩
    · rw [if_neg isInr] at tableHit
      exact absurd tableHit (by intro hit; cases hit)

/-- **A spike non-dependent-binary table hit pins the pair spike row.** -/
theorem nonDependentBinaryDataIntroRuleOf_spikeCases {generator : Generator}
    {rule : NonDependentBinaryDataIntroRule}
    (tableHit : nonDependentBinaryDataIntroRuleOf generator = some rule) :
    generator = .gen_pair ∧ rule = pairNonDependentBinaryRule := by
  unfold nonDependentBinaryDataIntroRuleOf at tableHit
  by_cases isPair : generator = .gen_pair
  · rw [if_pos isPair] at tableHit
    exact ⟨isPair, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isPair] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- **A spike reflexive table hit pins the refl spike row.** -/
theorem reflexiveDataIntroRuleOf_spikeCases {generator : Generator}
    {rule : ReflexiveDataIntroRule}
    (tableHit : reflexiveDataIntroRuleOf generator = some rule) :
    generator = .gen_refl ∧ rule = reflReflexiveRule := by
  unfold reflexiveDataIntroRuleOf at tableHit
  by_cases isRefl : generator = .gen_refl
  · rw [if_pos isRefl] at tableHit
    exact ⟨isRefl, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isRefl] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-! ## ★ The spike→union transfer -/

/-- **★ Every NATIVE-34 `DataIntroNaryUnionSpike` derivation maps to a `HasTypeNativeUnion` typing at
the same subject and classifier.**  Induction over the spike's eleven arms; the four embeddings map to
the union's embedding arms (`ofNullaryDataIntro`→`ofDataIntro`), the seven table rows map to the union's
table arms via the spike-table-inversion lemmas at definitionally-equal cells.  The two recursive rows
thread the IH-translated recursive premise. -/
theorem DataIntroNaryUnionSpike.toNativeUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : DataIntroNaryUnionSpike profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  induction derivation with
  | ofUnion unionTyped => exact unionTyped
  | ofNullaryDataIntro nullaryTyped => exact HasTypeNativeUnion.ofDataIntro nullaryTyped
  | ofNatIntro natTyped => exact HasTypeNativeUnion.ofNatIntro natTyped
  | ofListIntro listTyped => exact HasTypeNativeUnion.ofListIntro listTyped
  | recursiveUnaryRow generator rule child isRecursiveUnary _childTyped childUnion =>
      rcases recursiveUnaryDataIntroRuleOf_spikeCases isRecursiveUnary with ⟨_generatorEq, ruleEq⟩
      subst ruleEq
      exact HasTypeNativeUnion.recursiveUnaryIntro _ .gen_natSucc natSuccNativeRecursiveUnaryRule
        child rfl childUnion
  | recursiveBinaryRow generator rule head tail elementType isRecursiveBinary
      headTyped _tailTyped tailUnion =>
      rcases recursiveBinaryDataIntroRuleOf_spikeCases isRecursiveBinary with ⟨_generatorEq, ruleEq⟩
      subst ruleEq
      exact HasTypeNativeUnion.recursiveBinaryIntro _ .gen_listCons listConsNativeRecursiveBinaryRule
        head tail elementType rfl headTyped tailUnion
  | pinnedUnaryRow generator rule child elementType isPinnedUnary childTyped =>
      rcases pinnedUnaryDataIntroRuleOf_spikeCases isPinnedUnary with ⟨_generatorEq, ruleEq⟩
      subst ruleEq
      exact HasTypeNativeUnion.pinnedUnaryIntro _ .gen_optionSome optionSomeNativePinnedUnaryRule
        child elementType rfl childTyped
  | nullaryFreeTypeRow generator rule elementType elementLevel flag isNullaryFreeType
      elementTypeFormed =>
      rcases nullaryFreeTypeDataIntroRuleOf_spikeCases isNullaryFreeType with ⟨_generatorEq, ruleEq⟩
      subst ruleEq
      exact HasTypeNativeUnion.nullaryFreeTypeIntro _ .gen_optionNone
        optionNoneNativeNullaryFreeTypeRule elementType elementLevel flag rfl elementTypeFormed
  | coproductRow generator rule value pinnedType freeType freeLevel flag isCoproduct
      valueTyped freeTypeFormed =>
      rcases coproductDataIntroRuleOf_spikeCases isCoproduct with
        ⟨_generatorEq, ruleEq⟩ | ⟨_generatorEq, ruleEq⟩
      · subst ruleEq
        exact HasTypeNativeUnion.coproductIntro _ .gen_eitherInl eitherInlNativeCoproductRule
          value pinnedType freeType freeLevel flag rfl valueTyped freeTypeFormed
      · subst ruleEq
        exact HasTypeNativeUnion.coproductIntro _ .gen_eitherInr eitherInrNativeCoproductRule
          value pinnedType freeType freeLevel flag rfl valueTyped freeTypeFormed
  | nonDependentBinaryRow generator rule firstChild secondChild firstType secondType
      isNonDependentBinary firstTyped secondTyped =>
      rcases nonDependentBinaryDataIntroRuleOf_spikeCases isNonDependentBinary with
        ⟨_generatorEq, ruleEq⟩
      subst ruleEq
      exact HasTypeNativeUnion.nonDependentBinaryIntro _ .gen_pair pairNativeNonDependentBinaryRule
        firstChild secondChild firstType secondType rfl firstTyped secondTyped
  | reflexiveRow generator rule witness witnessType isReflexive witnessTyped =>
      rcases reflexiveDataIntroRuleOf_spikeCases isReflexive with ⟨_generatorEq, ruleEq⟩
      subst ruleEq
      exact HasTypeNativeUnion.reflexiveIntro _ .gen_refl reflNativeReflexiveRule
        witness witnessType rfl witnessTyped

/-! ## The transfer gate -/

/-- **The NATIVE-36 data-intro transfer evidence record.**  An inhabitant certifies the n-ary /
recursive data-constructor intro spike transfers wholesale into the real union. -/
structure DataIntroNaryUnionTransferEvidence (profile : PolyProfile) : Prop where
  /-- Every spike derivation transfers to the union. -/
  spikeTransfers : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    DataIntroNaryUnionSpike profile context subject classifier →
    HasTypeNativeUnion profile context subject classifier

/-- **★ The NATIVE-36 data-intro transfer gate** — inhabited by the shipped witness. -/
theorem dataIntroNaryUnionTransferWitness {profile : PolyProfile} :
    DataIntroNaryUnionTransferEvidence profile where
  spikeTransfers := fun derivation => derivation.toNativeUnion

end FX1Poly.Typed
