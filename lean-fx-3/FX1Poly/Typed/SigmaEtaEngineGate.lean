import FX1Poly.Typed.UnitEtaJudgmentalEquality
import FX1Poly.Typed.HasTypeDescSigmaProjection
import FX1Poly.Typed.HasTypeDescPiDataHeadUntyped

/-! # FX1Poly/Typed/SigmaEtaEngineGate — the Σ-η spike: why the readback has no Σ arm (#361)

The mandated pre-construction spike for Σ-η in the type-directed readback (η-M15c).  The #481
campaign asked whether the quote can η-expand at product classifiers the way it η-expands at Π
(`pair(fst t, snd t)` for non-pair subjects at `productTypeCell A B`).  The census answer is NO,
for reasons DEEPER than a missing readback arm — the typed substrate cannot state the Σ-η
equation at all.  This module pins that as machine-checked gate theorems.

## The two independent engine gates

  1. **The scrutinee gate** (`scrutineeIsLiteralPair` / `fstOfVariableHasNoTyping`): the
     Σ-projection engine types `fst(p)`/`snd(p)` ONLY for scrutinees that are LITERAL `pair`
     cells (`HasTypeDescSigmaProjection`'s premise is a `HasTypeDescPairIntro` derivation, whose
     subjects are pinned to `pairCell` by `subjectIsPair`).  A projection of a VARIABLE — the
     subject the η-expansion needs — is untypeable in the projection engine (here) AND in the
     grown engine (`fstCellHasNoTyping`/`sndCellHasNoTyping`, shipped).  No engine types the
     components of an η-expanded neutral.
  2. **The chaining gate** (`componentsGrownTyped` / `etaPairExpansion_hasNoPairIntroTyping`):
     even where projections ARE typed (literal-pair scrutinees), the η-expansion
     `pair(fst p, snd p)` is untypeable — `pairIntro` demands GROWN (`HasTypeDescPi`) component
     typings, but `fst p` is grown-UNTYPED for EVERY `p` (`fstCellHasNoTyping`).  The standalone
     engines do not chain: projection-typed terms cannot feed pair introduction.

## The consequence: Σ-η is unstateable, not merely unproven

`pairCellOutsideDomain` + `sigmaEtaEquation_underivable`: pair cells are outside the domain of
the typed judgmental equality `DefEqUnitEta` ENTIRELY — both its arms (`ofBetaEtaConv` and
`unitEta`) presuppose a typing of each endpoint, and no engine feeding those arms types a `pair`
cell whose components are projections.  So `pair(fst t, snd t) ≡ t` is underivable at EVERY
classifier, for EVERY `t` — while the raw layer happily fires `Step.eta.etaPair`.  The gap is
the typed/raw η mismatch the honest-boundary discipline predicted: raw η over-fires (the shipped
`core_eta_modal_glue_raw_overclaim` finding), and the typed layer cannot consume even the
legitimate instances yet.

## Route A vs Route B — the costed decision record (engine-shape change = user decision, T2 #1198)

**Route A — widen the STANDALONE engines (4 bricks, recommended):**
  * R1: neutral-scrutinee projection arms — type `fst(p)`/`snd(p)` from a GROWN-typed scrutinee
    at a literal `productTypeCell A B` (new arms or a sibling judgment; the classifier-rigidity
    finding `FormationClassifierRigidity` says literal product matching loses nothing).
  * R2: pair-introduction union-component arm — accept projection-typed components
    (`HasTypeDescPi ∨ HasTypeDescSigmaProjection`), so the η-expansion of a typed scrutinee
    types at its product classifier.
  * R3: `DefEqUnitEta.ofBetaEtaConv` union widening — the βη arm over the engine union
    (precedent: `unitEta` already takes `HasTypeDescDataIntro ∨ HasTypeDescPi`).
  * R4: the readback Σ arm at `productTypeCell` (NOT `sigmaTyCodeCell` — dependent Σ has no
    intro rule anywhere) + its soundness clause in `readbackAtClassifier_congruent`.
  Cost: ~4 campaign bricks; touches two standalone inductives + the judgmental equality + the
  readback.  SR/weakening/subst for the widened arms rides the shipped flat-template metatheory.
  CAVEAT: R1/R2 change engine shapes, so the gate theorems below that `cases` those engines
  (`scrutineeIsLiteralPair`, `fstOfVariableHasNoTyping`, `etaPairExpansion_hasNoPairIntroTyping`,
  and the capstones citing them) get NEW ARMS and must be consciously revisited — they are the
  regression tripwires for the widening, by design.

**Route B — add pair/fst/snd arms to the GROWN engine itself (rejected):**
  breaks `subjectRootGenerator`'s six-way classification, which invalidates
  `cellHasNoTypingWhenRootGenericallyExcluded` and with it the ENTIRE iota-vacuity leg of the SR
  dispatcher, the canonical-forms boundary, and the shipped refutation corpus.  The standalone
  engine architecture exists precisely to avoid this cascade.

DECISION: Route A, pending user sign-off on the R1/R2 engine widenings.  Until then the readback
correctly has NO Σ arm, and `etaPair` collapse remains out of NbE scope — gate, not gap.

## Zero-axiom verification

Free-index `cases` + threaded subject equations (the propext-safe inversion recipe), `injection`
drilling through `mkGen`/`childCons`, `congrArg RawTerm.headGenerator` + `Generator.noConfusion`
discrimination, `Option.noConfusion` on the data-intro table miss, and the shipped grown-engine
refutations.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The data-intro nullary table has no `gen_pair` row (the pair is n-ary, not nullary) — the
table-miss fact feeding `pairCellHasNoDataIntroTyping`. -/
theorem dataIntroNullaryRuleDescOf_pairIsNone :
    dataIntroNullaryRuleDescOf .gen_pair = none := rfl

/-- **The data-intro engine types no pair cell.**  `HasTypeDescDataIntro`'s sole arm is
table-driven over the NULLARY table, which has no `gen_pair` row.  Subject-threaded (the
propext-safe inversion direction). -/
theorem HasTypeDescDataIntro.pairCellHasNoDataIntroTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    (typed : HasTypeDescDataIntro profile context subject classifier)
    (subjectIsPair : subject = pairCell firstValue secondValue) : False := by
  cases typed with
  | nullaryIntro generator _payload _children rule isDataIntro =>
      have generatorIsPair : generator = Generator.gen_pair :=
        congrArg RawTerm.headGenerator subjectIsPair
      rw [generatorIsPair, dataIntroNullaryRuleDescOf_pairIsNone] at isDataIntro
      exact nomatch isDataIntro

/-- **Pair-introduction inversion (component typings).**  A pair-intro-typed `pairCell a b`
has GROWN-typed components at the product classifier's component types.  The premise-extraction
companion of the shipped `subjectIsPair`/`classifierIsProduct`; subject-threaded, `injection`
drilling through `mkGen`/`childCons`. -/
theorem HasTypeDescPairIntro.componentsGrownTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {leftComponent rightComponent : RawTerm scope}
    (derivation : HasTypeDescPairIntro profile context subject classifier)
    (subjectIsPair : subject = pairCell leftComponent rightComponent) :
    ∃ (firstType secondType : RawTerm scope),
      classifier = productTypeCell firstType secondType ∧
      HasTypeDescPi profile context leftComponent firstType ∧
      HasTypeDescPi profile context rightComponent secondType := by
  cases derivation with
  | pairIntro firstValue secondValue firstType secondType firstTyped secondTyped =>
      injection subjectIsPair with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _headScopeEq _shiftEq _restShiftsEq firstComponentEq restChildrenEq
      injection restChildrenEq with _headScopeEq2 _shiftEq2 _restShiftsEq2 secondComponentEq _nilEq
      subst firstComponentEq
      subst secondComponentEq
      exact ⟨firstType, secondType, rfl, firstTyped, secondTyped⟩

/-- **★ The scrutinee gate (positive form): every Σ-projection typing has a LITERAL-pair
scrutinee.**  The projection engine's premise is a `HasTypeDescPairIntro` derivation, whose
subject is pinned to a `pairCell` — so `fst`/`snd` of anything that is not literally a pair
(a variable, an application, an η-expansion target) is untypeable.  THE regression tripwire for
the Route-A R1 widening: a neutral-scrutinee arm makes this statement false by design. -/
theorem HasTypeDescSigmaProjection.scrutineeIsLiteralPair {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescSigmaProjection profile context subject classifier) :
    ∃ (scrutinee firstValue secondValue : RawTerm scope),
      scrutinee = pairCell firstValue secondValue ∧
      (subject = fstCell scrutinee ∨ subject = sndCell scrutinee) := by
  cases derivation with
  | fstIntro pairTerm _firstType _secondType pairTyped =>
      obtain ⟨firstValue, secondValue, isPair⟩ := pairTyped.subjectIsPair
      exact ⟨pairTerm, firstValue, secondValue, isPair, Or.inl rfl⟩
  | sndIntro pairTerm _firstType _secondType pairTyped =>
      obtain ⟨firstValue, secondValue, isPair⟩ := pairTyped.subjectIsPair
      exact ⟨pairTerm, firstValue, secondValue, isPair, Or.inr rfl⟩

/-- **The scrutinee gate at the variable (negative form): `fst(x)` is untypeable in the
projection engine.**  The subject the Σ-η readback arm would emit for a variable — combined with
the shipped grown-engine refutation (`fstCellHasNoTyping`), NO engine types it.  The `snd`
mirror is the same proof shape. -/
theorem HasTypeDescSigmaProjection.fstOfVariableHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {index : Fin scope}
    (typed : HasTypeDescSigmaProjection profile context subject classifier)
    (subjectIsVarProjection : subject = fstCell (variableCell index)) : False := by
  obtain ⟨scrutinee, firstValue, secondValue, scrutineeIsPair, subjectShape⟩ :=
    typed.scrutineeIsLiteralPair
  cases subjectShape with
  | inl subjectIsFst =>
      have projectionsAgree : fstCell (variableCell index) = fstCell scrutinee :=
        subjectIsVarProjection.symm.trans subjectIsFst
      injection projectionsAgree with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _headScopeEq _shiftEq _restShiftsEq scrutineeEq _nilEq
      rw [← scrutineeEq] at scrutineeIsPair
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator scrutineeIsPair :
          Generator.gen_var = Generator.gen_pair)
  | inr subjectIsSnd =>
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator (subjectIsVarProjection.symm.trans subjectIsSnd) :
          Generator.gen_fst = Generator.gen_snd)

/-- **★ The chaining gate: the η-pair expansion is untypeable by pair introduction.**  Even for
a LITERAL-pair `p`, `pair(fst p, snd p)` has no `HasTypeDescPairIntro` typing — `pairIntro`
demands GROWN component typings, but `fst _` is grown-untyped for EVERY scrutinee
(`fstCellHasNoTyping`).  The standalone engines do not chain. -/
theorem etaPairExpansion_hasNoPairIntroTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {pairTerm classifier : RawTerm scope}
    (typed : HasTypeDescPairIntro profile context
      (RawTerm.etaPairSource pairTerm) classifier) : False := by
  obtain ⟨_firstType, _secondType, _classifierIsProduct, fstComponentTyped, _sndComponentTyped⟩ :=
    typed.componentsGrownTyped (leftComponent := fstCell pairTerm)
      (rightComponent := sndCell pairTerm) rfl
  exact fstComponentTyped.fstCellHasNoTyping

/-- **The η-pair expansion is grown-untypeable** — it is a `pair` cell, outside the grown
engine's canonical-forms boundary (`pairCellHasNoTyping`).  Together with
`etaPairExpansion_hasNoPairIntroTyping` and `pairCellHasNoDataIntroTyping`: NO engine types the
Σ-η source. -/
theorem etaPairExpansion_hasNoGrownTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {pairTerm classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (RawTerm.etaPairSource pairTerm) classifier) :
    False :=
  typed.pairCellHasNoTyping

/-- **★ Pair cells are outside the domain of the typed judgmental equality.**  Both
`DefEqUnitEta` arms presuppose a typing of each endpoint; no arm-feeding engine types a `pair`
cell (grown: `pairCellHasNoTyping`; data-intro: `pairCellHasNoDataIntroTyping`).  So no
`DefEqUnitEta` derivation has a pair as its left endpoint — at ANY classifier. -/
theorem DefEqUnitEta.pairCellOutsideDomain {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {leftTerm rightTerm classifier : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    (defEq : DefEqUnitEta profile context leftTerm rightTerm classifier)
    (leftIsPair : leftTerm = pairCell firstValue secondValue) : False := by
  cases defEq with
  | ofBetaEtaConv _contextWellFormed leftTyped _rightTyped _convertible =>
      exact (leftIsPair ▸ leftTyped).pairCellHasNoTyping
  | unitEta leftTypedAtUnit _rightTypedAtUnit =>
      cases leftTypedAtUnit with
      | inl dataIntroTyped => exact dataIntroTyped.pairCellHasNoDataIntroTyping leftIsPair
      | inr grownTyped => exact (leftIsPair ▸ grownTyped).pairCellHasNoTyping

/-- **★ The Σ-η equation is UNDERIVABLE — the spike headline.**  `pair(fst t, snd t) ≡ t` has
no `DefEqUnitEta` derivation at any classifier, for any `t` (and any right endpoint at all) —
the source is a pair cell, outside the judgment's domain.  The raw layer fires
`Step.eta.etaPair` on exactly this source; the typed layer cannot consume it.  Σ-η in the
readback (#361) is ENGINE-gated, not readback-gated: the Route-A widenings (R1–R3) must land
before a readback Σ arm (R4) has anything sound to emit. -/
theorem sigmaEtaEquation_underivable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {pairTerm rightTerm classifier : RawTerm scope}
    (defEq : DefEqUnitEta profile context
      (RawTerm.etaPairSource pairTerm) rightTerm classifier) : False :=
  defEq.pairCellOutsideDomain
    (firstValue := fstCell pairTerm) (secondValue := sndCell pairTerm) rfl

end FX1Poly.Typed
