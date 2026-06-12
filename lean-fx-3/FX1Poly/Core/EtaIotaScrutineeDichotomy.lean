import FX1Poly.Core.EtaStabilityDefinedness

/-! # EtaIotaScrutineeDichotomy — ETA-T5 increment 4.4b: the per-spec
case split for cong-eta before a root iota firing

The quasi-commutation's cong-then-redex case holds an eta step inside
the eliminator spine and a row firing on the POST-eta spine.  Per
declared scrutinee, the source-side read relates to the target-side
cell in exactly one of three ways: the reads are EQUAL, the source
cell steps by CONGRUENCE (same head, same payload — the pattern match
transfers backward verbatim), or the source slot holds a table-eta
REDEX whose contraction is the target cell — the eta/iota DUALITY
(eta intro roots are exactly the constructor heads iota scrutinizes),
which no backward firing can absorb and which gets its own per-pair
treatment downstream.

This file proves the dichotomy: either EVERY scrutinee is
equal-or-cong — yielding the backward pattern match
(`scrutineesFire` on the source spine) plus the
`ScrutineeCellsEtaRelated` hypothesis the stability and definedness
inductions consume — or SOME scrutinee exhibits the duality witness.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaIotaScrutineeDichotomy.lean`. -/

namespace FX1Poly.Core

/-! ## The per-spec shapes -/

/-- The GOOD shape at one scrutinee spec: any source-side cell read of
the declared head is mirrored at the related spine with the SAME head
and payload and pointwise-eta-star children — the per-spec slice of
`ScrutineeCellsEtaRelated`, keyed on raw slot reads. -/
def IotaRuleDesc.CellGoodAtSpec (rule : IotaRuleDesc)
    (etaTable : List EtaRuleDesc) {scope : Nat}
    (spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope)
    (spec : ScrutineeSpec) : Prop :=
  ∀ {matchedPayload : spec.head.payload scope}
    {matchedChildren : RawTermChildren spec.head.binderShifts scope},
    (scopedChildAt? spine.toScopedChildren spec.slot).bind
        ScopedChild.atShiftZero?
      = some (.mkGen spec.head matchedPayload matchedChildren) →
    ∃ matchedChildren',
      (scopedChildAt? spine'.toScopedChildren spec.slot).bind
          ScopedChild.atShiftZero?
        = some (.mkGen spec.head matchedPayload matchedChildren')
      ∧ EtaChildrenPointwiseStar etaTable matchedChildren
          matchedChildren'

/-- The DUALITY shape at one scrutinee spec: the source slot holds a
raw-tier table-eta redex whose contraction is exactly the related
spine's scrutinee cell.  Eta intro heads are constructor heads, and
constructor heads are what iota rows scrutinize — this is the one
configuration where an eta step inside the spine cannot be reordered
after the firing by pattern-match transfer alone. -/
def IotaRuleDesc.DualityAtSpec (rule : IotaRuleDesc)
    (etaTable : List EtaRuleDesc) {scope : Nat}
    (spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope)
    (spec : ScrutineeSpec) : Prop :=
  ∃ (etaRule : EtaRuleDesc), etaRule ∈ etaTable
    ∧ etaRule.requiresTypedFiring = false
    ∧ ∃ (introPayload : etaRule.introGenerator.payload scope)
        (introChildren :
          RawTermChildren etaRule.introGenerator.binderShifts scope)
        (targetPayload : spec.head.payload scope)
        (targetChildren : RawTermChildren spec.head.binderShifts scope),
      (scopedChildAt? spine.toScopedChildren spec.slot).bind
          ScopedChild.atShiftZero?
        = some (.mkGen etaRule.introGenerator introPayload introChildren)
      ∧ (scopedChildAt? spine'.toScopedChildren spec.slot).bind
          ScopedChild.atShiftZero?
        = some (.mkGen spec.head targetPayload targetChildren)
      ∧ etaRule.contractsOn? introChildren
          = some (.mkGen spec.head targetPayload targetChildren)

/-- The row-level duality: SOME declared scrutinee exhibits the duality
shape. -/
def IotaRuleDesc.HasEtaDualityAt (rule : IotaRuleDesc)
    (etaTable : List EtaRuleDesc) {scope : Nat}
    (spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Prop :=
  ∃ spec, spec ∈ rule.scrutinees
    ∧ rule.DualityAtSpec etaTable spine spine' spec

/-! ## The per-spec analysis -/

/-- ★ **Per-spec trichotomy resolved to a dichotomy**: under a
pointwise (at most one step per position) eta relation on the spines,
a spec firing on the RELATED spine either fires on the SOURCE spine
with the good cell shape, or exhibits the duality witness. -/
theorem IotaRuleDesc.scrutineeSpecFires_etaDisjunction
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwise etaTable spine spine')
    (spec : ScrutineeSpec)
    (specFires' : rule.scrutineeSpecFires spine' spec = true) :
    (rule.scrutineeSpecFires spine spec = true
      ∧ rule.CellGoodAtSpec etaTable spine spine' spec)
    ∨ rule.DualityAtSpec etaTable spine spine' spec := by
  obtain ⟨targetPayload, targetChildren, targetRead⟩ :=
    rule.scrutineeSpecFires_slotHoldsHead specFires'
  obtain ⟨sourceTerm, sourceRead⟩ :=
    composedReadAtShiftZero_equiDefined spine' spine spec.slot targetRead
  obtain ⟨targetTerm, targetReadAgain, eqOrStep⟩ :=
    spineRelated.lookupAtShiftZeroRelated spec.slot sourceRead
  have targetIsCell :
      targetTerm = .mkGen spec.head targetPayload targetChildren :=
    Option.some.inj (targetReadAgain.symm.trans targetRead)
  cases eqOrStep with
  | inl sourceIsTarget =>
      have sourceIsCell :
          sourceTerm = .mkGen spec.head targetPayload targetChildren :=
        sourceIsTarget.trans targetIsCell
      subst sourceIsCell
      refine Or.inl ⟨?_, ?_⟩
      · dsimp only [IotaRuleDesc.scrutineeSpecFires] at specFires' ⊢
        rw [sourceRead]
        rw [targetRead] at specFires'
        exact specFires'
      · intro matchedPayload matchedChildren cellRead
        have cellsAgree := Option.some.inj (sourceRead.symm.trans cellRead)
        injection cellsAgree with _scopeRefl _genRefl payloadEq childrenEq
        subst payloadEq
        subst childrenEq
        exact ⟨_, targetRead, EtaChildrenPointwiseStar.refl _⟩
  | inr etaStep =>
      cases etaStep with
      | etaRedex isRow isRawTier introPayload contracts =>
          rw [targetIsCell] at contracts
          exact Or.inr ⟨_, isRow, isRawTier, introPayload, _,
            targetPayload, targetChildren, sourceRead, targetRead,
            contracts⟩
      | cong gen payload childStep =>
          have headsAgree : gen = spec.head := congrArg
            (fun cell => match cell with
              | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
            targetIsCell
          subst headsAgree
          injection targetIsCell with _scopeRefl _genRefl payloadEq
            childrenEq
          subst payloadEq
          subst childrenEq
          refine Or.inl ⟨?_, ?_⟩
          · dsimp only [IotaRuleDesc.scrutineeSpecFires] at specFires' ⊢
            rw [sourceRead]
            rw [targetRead] at specFires'
            exact specFires'
          · intro matchedPayload matchedChildren cellRead
            have cellsAgree :=
              Option.some.inj (sourceRead.symm.trans cellRead)
            injection cellsAgree with _scopeRefl2 _genRefl2 payloadEq2
              childrenEq2
            subst payloadEq2
            subst childrenEq2
            exact ⟨_, targetRead,
              EtaChildrenPointwiseStar.ofChildrenStep childStep⟩

/-! ## The membership fold -/

/-- Rebuild a list pattern test from per-member firings. -/
theorem IotaRuleDesc.scrutineesFire_ofMemberFires (rule : IotaRuleDesc)
    {scope : Nat}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope} :
    (specs : List ScrutineeSpec) →
    (∀ spec, spec ∈ specs →
      rule.scrutineeSpecFires spine spec = true) →
    rule.scrutineesFire spine specs = true
  | [], _ => rfl
  | spec :: restSpecs, memberFires => by
      dsimp only [IotaRuleDesc.scrutineesFire]
      rw [memberFires spec (.head _),
        rule.scrutineesFire_ofMemberFires restSpecs
          (fun innerSpec isInRest =>
            memberFires innerSpec (.tail _ isInRest))]
      rfl

/-- Fold the per-spec disjunction over a spec list: either every
member is good, or some member exhibits the duality. -/
theorem IotaRuleDesc.scrutineeList_etaDisjunction (rule : IotaRuleDesc)
    {etaTable : List EtaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwise etaTable spine spine') :
    (specs : List ScrutineeSpec) →
    (∀ spec, spec ∈ specs →
      rule.scrutineeSpecFires spine' spec = true) →
    (∀ spec, spec ∈ specs →
      rule.scrutineeSpecFires spine spec = true
        ∧ rule.CellGoodAtSpec etaTable spine spine' spec)
    ∨ ∃ spec, spec ∈ specs
        ∧ rule.DualityAtSpec etaTable spine spine' spec
  | [], _ => Or.inl (fun _ isMember => nomatch isMember)
  | spec :: restSpecs, memberFires' =>
      match rule.scrutineeSpecFires_etaDisjunction spineRelated spec
          (memberFires' spec (.head _)) with
      | Or.inr headDuality => Or.inr ⟨spec, .head _, headDuality⟩
      | Or.inl headGood =>
          match rule.scrutineeList_etaDisjunction spineRelated restSpecs
              (fun innerSpec isInRest =>
                memberFires' innerSpec (.tail _ isInRest)) with
          | Or.inr ⟨dualSpec, isInRest, restDuality⟩ =>
              Or.inr ⟨dualSpec, .tail _ isInRest, restDuality⟩
          | Or.inl restGood =>
              Or.inl (fun innerSpec isMember =>
                match isMember with
                | .head _ => headGood
                | .tail _ isInRest => restGood innerSpec isInRest)

/-! ## The row-level dichotomy -/

/-- ★ **The cong-eta/iota dichotomy**: a row firing on the POST-eta
spine either fires on the PRE-eta spine with the full
`ScrutineeCellsEtaRelated` hypothesis (the equal/congruence cases —
every consumer of the stability and definedness inductions is now
armed), or some declared scrutinee slot holds an eta redex contracting
to the fired cell — the duality, dispatched per intro/elim row pair
downstream. -/
theorem IotaRuleDesc.scrutineePattern_etaDichotomy (rule : IotaRuleDesc)
    {etaTable : List EtaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwise etaTable spine spine')
    (allFire' : rule.scrutineesFire spine' rule.scrutinees = true) :
    (rule.scrutineesFire spine rule.scrutinees = true
      ∧ ScrutineeCellsEtaRelated rule etaTable spine spine')
    ∨ rule.HasEtaDualityAt etaTable spine spine' := by
  match rule.scrutineeList_etaDisjunction spineRelated rule.scrutinees
      (fun spec isMember =>
        rule.scrutineesFire_memberFires rule.scrutinees allFire'
          isMember) with
  | Or.inr ⟨dualSpec, isMember, duality⟩ =>
      exact Or.inr ⟨dualSpec, isMember, duality⟩
  | Or.inl allGood =>
      refine Or.inl ⟨?_, ?_⟩
      · exact rule.scrutineesFire_ofMemberFires rule.scrutinees
          (fun spec isMember => (allGood spec isMember).left)
      · intro scrutineeIndex spec specEq matchedPayload matchedChildren
          termEq
        have specIsMember : spec ∈ rule.scrutinees :=
          listEntryAt?_mem rule.scrutinees scrutineeIndex specEq
        have rawRead :
            (scopedChildAt? spine.toScopedChildren spec.slot).bind
                ScopedChild.atShiftZero?
              = some (.mkGen spec.head matchedPayload matchedChildren)
            := by
          dsimp only [IotaRuleDesc.scrutineeTermAt?] at termEq
          rw [specEq, optionSomeBindExplicit] at termEq
          exact termEq
        obtain ⟨matchedChildren', rawReadRelated, childrenStar⟩ :=
          (allGood spec specIsMember).right rawRead
        refine ⟨matchedChildren', ?_, childrenStar⟩
        dsimp only [IotaRuleDesc.scrutineeTermAt?]
        rw [specEq, optionSomeBindExplicit]
        exact rawReadRelated

end FX1Poly.Core
