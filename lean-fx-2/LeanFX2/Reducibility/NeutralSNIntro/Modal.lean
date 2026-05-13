import LeanFX2.Reducibility.NeutralSNIntro.Sums

/-! # LeanFX2.Reducibility.NeutralSNIntro.Modal

`modIntro` / `modElim` SN preservation + the binary `pair`,
`fst_pair`, `snd_pair` Σ-projection ι-witnesses + neutral
`fst` / `snd` cong-only cases (raw + typed).

## Root status

Layer 3 metatheory leaf.  K12.20.C ctor introduction SN preservation
for the modal-introduction and Σ-projection families. -/

namespace LeanFX2


/-- **K12.20.Y modIntro SN preservation**.  Sister to the
optionSome / eitherInl / eitherInr helpers — unary cong-only ctor at
the modal-introduction ctor.  Powers future fundamental_modIntro at
parametric Ty.modal closures. -/
theorem RawTerm.modIntro_isStronglyNormalizing {scope : Nat}
    {innerTerm : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.modIntro innerTerm) := by
  induction innerIsSN with
  | intro currentInner _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.modIntro currentInner) ?_
    intro target progressStep
    obtain ⟨innerTarget, targetEq, innerStep⟩ :=
      RawStep.par.modIntro_inv progressStep.1
    subst targetEq
    have innerDistinct :
        currentInner ≠ innerTarget := fun innerEq =>
      progressStep.2 (congrArg RawTerm.modIntro innerEq)
    exact inductiveHypothesis innerTarget
      ⟨innerStep, innerDistinct⟩

/-- **K12.25 modal elimination SN preservation**.

`modElim` has a congruence arm plus the modal β arm
`modElim (modIntro payload) → payload`.  Congruent reducts recurse
through the inner SN witness.  β reducts first obtain SN of the
developed `modIntro payload`, then invert that constructor-shaped SN
back to SN of the payload. -/
theorem RawTerm.modElim_isStronglyNormalizing {scope : Nat}
    {innerTerm : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.modElim innerTerm) := by
  induction innerIsSN with
  | intro currentInner innerClosure innerIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.modElim currentInner) ?_
    intro target progressStep
    rcases RawStep.par.modElim_inv progressStep.1 with
      ⟨innerTarget, targetEq, innerStep⟩
      | ⟨payloadTarget, targetEq, innerStep⟩
    · subst targetEq
      by_cases innerEq : currentInner = innerTarget
      · subst innerEq
        exact (progressStep.2 rfl).elim
      · exact innerIH innerTarget ⟨innerStep, innerEq⟩
    · rw [targetEq]
      have introTargetIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.modIntro payloadTarget) := by
        by_cases innerEq :
            currentInner = RawTerm.modIntro payloadTarget
        · rw [← innerEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentInner innerClosure
        · exact innerClosure (RawTerm.modIntro payloadTarget)
            ⟨innerStep, innerEq⟩
      exact RawTerm.modIntro_inner_isStronglyNormalizing
        introTargetIsSN

/-- Typed wrapper for `RawTerm.modElim_isStronglyNormalizing`. -/
theorem Term.modElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modElim innerTerm) :=
  RawTerm.modElim_isStronglyNormalizing innerIsSN

/-- **K12.20.Z pair SN preservation** — first binary cong-only SN
helper.  Pair has two parallel subterms; the SN proof needs nested
induction (outer on firstIsSN with `generalizing` to expose
second's SN as IH input, inner on secondIsSN) plus a per-side
disequality split.  When `pair currentFirst currentSecond` steps
to `pair firstTarget secondTarget` with the pair distinct, at
least one side must have advanced; case-split on which to discharge
via the outer or inner IH. -/
theorem RawTerm.pair_isStronglyNormalizing {scope : Nat}
    {firstValue : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstValue) :
    ∀ {secondValue : RawTerm scope},
      RawTerm.isStronglyNormalizing secondValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.pair firstValue secondValue) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondValue secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pair currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq, firstStep, secondStep⟩ :=
        RawStep.par.pair_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        have secondDistinct : currentSecond ≠ secondTarget := fun secondEq =>
          progressStep.2 (congrArg (RawTerm.pair currentFirst) secondEq)
        exact innerIH secondTarget ⟨secondStep, secondDistinct⟩
      · have firstProgress : RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro currentSecond secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- Head-β SN expansion for first projection over a pair.

If both components are strongly normalizing, then `fst (pair first second)`
is strongly normalizing.  Congruence reducts recurse through the pair
components; β reducts land on a reduct of the first component. -/
theorem RawTerm.fst_pair_isStronglyNormalizing {scope : Nat}
    {firstValue : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstValue) :
    ∀ {secondValue : RawTerm scope},
      RawTerm.isStronglyNormalizing secondValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.fst (RawTerm.pair firstValue secondValue)) := by
  induction firstIsSN with
  | intro currentFirst firstClosure firstIH =>
    intro secondValue secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.fst (RawTerm.pair currentFirst currentSecond)) ?_
      intro target progressStep
      rcases RawStep.par.fst_inv progressStep.1 with
        ⟨pairTarget, targetEq, pairStep⟩
        | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
      · obtain ⟨firstTarget, secondTarget, pairTargetEq,
            firstStep, secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        subst pairTargetEq
        subst targetEq
        by_cases firstEq : currentFirst = firstTarget
        · subst firstEq
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact False.elim (progressStep.2 rfl)
          · exact innerIH secondTarget ⟨secondStep, secondEq⟩
        · have firstProgress :
              RawStep.parProgress currentFirst firstTarget :=
            ⟨firstStep, firstEq⟩
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact firstIH firstTarget firstProgress
              (RawTerm.isStronglyNormalizing.intro currentSecond secondClosure)
          · exact firstIH firstTarget firstProgress
              (secondClosure secondTarget ⟨secondStep, secondEq⟩)
      · obtain ⟨firstPairTarget, _secondPairTarget, pairTargetEq,
            firstStep, _secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        injection pairTargetEq with _scopeEq firstTargetEq _secondTargetEq
        rw [targetEq]
        have firstStepToTarget : RawStep.par currentFirst firstTarget := by
          rw [firstTargetEq]
          exact firstStep
        by_cases firstEq : currentFirst = firstTarget
        · subst firstEq
          exact RawTerm.isStronglyNormalizing.intro
            currentFirst firstClosure
        · exact firstClosure firstTarget ⟨firstStepToTarget, firstEq⟩

/-- Head-β SN expansion for second projection over a pair.

If both components are strongly normalizing, then `snd (pair first second)`
is strongly normalizing.  Congruence reducts recurse through the pair
components; β reducts land on a reduct of the second component. -/
theorem RawTerm.snd_pair_isStronglyNormalizing {scope : Nat}
    {firstValue : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstValue) :
    ∀ {secondValue : RawTerm scope},
      RawTerm.isStronglyNormalizing secondValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.snd (RawTerm.pair firstValue secondValue)) := by
  induction firstIsSN with
  | intro currentFirst firstClosure firstIH =>
    intro secondValue secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.snd (RawTerm.pair currentFirst currentSecond)) ?_
      intro target progressStep
      rcases RawStep.par.snd_inv progressStep.1 with
        ⟨pairTarget, targetEq, pairStep⟩
        | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
      · obtain ⟨firstTarget, secondTarget, pairTargetEq,
            firstStep, secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        subst pairTargetEq
        subst targetEq
        by_cases firstEq : currentFirst = firstTarget
        · subst firstEq
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact False.elim (progressStep.2 rfl)
          · exact innerIH secondTarget ⟨secondStep, secondEq⟩
        · have firstProgress :
              RawStep.parProgress currentFirst firstTarget :=
            ⟨firstStep, firstEq⟩
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact firstIH firstTarget firstProgress
              (RawTerm.isStronglyNormalizing.intro currentSecond secondClosure)
          · exact firstIH firstTarget firstProgress
              (secondClosure secondTarget ⟨secondStep, secondEq⟩)
      · obtain ⟨_firstPairTarget, secondPairTarget, pairTargetEq,
            _firstStep, secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        injection pairTargetEq with _scopeEq _firstTargetEq secondTargetEq
        rw [targetEq]
        have secondStepToTarget : RawStep.par currentSecond secondTarget := by
          rw [secondTargetEq]
          exact secondStep
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSecond secondClosure
        · exact secondClosure secondTarget ⟨secondStepToTarget, secondEq⟩

/-- Typed wrapper for pair SN expansion.

The raw proof is the computational content; this lemma exposes it at
the `Term` layer so future sigma-intro and head-expansion cases can
consume typed component SN witnesses directly. -/
theorem Term.pair_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsSN : Term.isStronglyNormalizing firstValue)
    (secondIsSN : Term.isStronglyNormalizing secondValue) :
    Term.isStronglyNormalizing
      (Term.pair (secondType := secondType) firstValue secondValue) :=
  RawTerm.pair_isStronglyNormalizing firstIsSN secondIsSN

/-- Typed wrapper for `fst (pair first second)` SN expansion.

This is still an SN bridge, not the full sigma-intro reducibility
middle conjunct.  Full `Reducible firstType (fst (pair ...))`
requires typed backward closure at the result type. -/
theorem Term.fst_pair_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsSN : Term.isStronglyNormalizing firstValue)
    (secondIsSN : Term.isStronglyNormalizing secondValue) :
    Term.isStronglyNormalizing
      (Term.fst
        (Term.pair (secondType := secondType) firstValue secondValue)) :=
  RawTerm.fst_pair_isStronglyNormalizing firstIsSN secondIsSN

/-- Typed wrapper for `snd (pair first second)` SN expansion. -/
theorem Term.snd_pair_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsSN : Term.isStronglyNormalizing firstValue)
    (secondIsSN : Term.isStronglyNormalizing secondValue) :
    Term.isStronglyNormalizing
      (Term.snd
        (Term.pair (secondType := secondType) firstValue secondValue)) :=
  RawTerm.snd_pair_isStronglyNormalizing firstIsSN secondIsSN

/-- Generic first-projection SN preservation.

The congruence arm recurses through the projected pair.  The β arm can
only fire after the pair term develops to an explicit `pair`; component
SN then follows from the existing pair-component inversion lemma. -/
theorem RawTerm.fst_isStronglyNormalizing {scope : Nat}
    {pairRaw : RawTerm scope}
    (pairIsSN : RawTerm.isStronglyNormalizing pairRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.fst pairRaw) := by
  induction pairIsSN with
  | intro currentPair pairClosure pairIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.fst currentPair) ?_
    intro target progressStep
    rcases RawStep.par.fst_inv progressStep.1 with
      ⟨pairTarget, targetEq, pairStep⟩
      | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
    · subst targetEq
      by_cases pairEq : currentPair = pairTarget
      · subst pairEq
        exact (progressStep.2 rfl).elim
      · exact pairIH pairTarget ⟨pairStep, pairEq⟩
    · rw [targetEq]
      have developedPairIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.pair firstTarget secondTarget) := by
        by_cases pairEq : currentPair =
            RawTerm.pair firstTarget secondTarget
        · rw [← pairEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentPair pairClosure
        · exact pairClosure (RawTerm.pair firstTarget secondTarget)
            ⟨pairStep, pairEq⟩
      exact RawTerm.pair_first_isStronglyNormalizing developedPairIsSN

/-- Generic second-projection SN preservation.

This mirrors `RawTerm.fst_isStronglyNormalizing`; the β arm extracts
the second component from an SN developed pair. -/
theorem RawTerm.snd_isStronglyNormalizing {scope : Nat}
    {pairRaw : RawTerm scope}
    (pairIsSN : RawTerm.isStronglyNormalizing pairRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.snd pairRaw) := by
  induction pairIsSN with
  | intro currentPair pairClosure pairIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.snd currentPair) ?_
    intro target progressStep
    rcases RawStep.par.snd_inv progressStep.1 with
      ⟨pairTarget, targetEq, pairStep⟩
      | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
    · subst targetEq
      by_cases pairEq : currentPair = pairTarget
      · subst pairEq
        exact (progressStep.2 rfl).elim
      · exact pairIH pairTarget ⟨pairStep, pairEq⟩
    · rw [targetEq]
      have developedPairIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.pair firstTarget secondTarget) := by
        by_cases pairEq : currentPair =
            RawTerm.pair firstTarget secondTarget
        · rw [← pairEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentPair pairClosure
        · exact pairClosure (RawTerm.pair firstTarget secondTarget)
            ⟨pairStep, pairEq⟩
      exact RawTerm.pair_second_isStronglyNormalizing developedPairIsSN

/-- Direct M04 SN case for first projection from any SN pair term. -/
theorem Term.fst_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsSN : Term.isStronglyNormalizing pairTerm) :
    Term.isStronglyNormalizing (Term.fst pairTerm) :=
  RawTerm.fst_isStronglyNormalizing pairIsSN

/-- Direct M04 SN case for second projection from any SN pair term. -/
theorem Term.snd_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsSN : Term.isStronglyNormalizing pairTerm) :
    Term.isStronglyNormalizing (Term.snd pairTerm) :=
  RawTerm.snd_isStronglyNormalizing pairIsSN


end LeanFX2
