import LeanFX2.Reducibility.StableBase.CubicalSN

/-! # LeanFX2.Reducibility.StableBase.SubtermSN

Shape-specialized SN inversions on subterms (`app` function
and argument, `natSucc` predecessor, `pair` first/second,
`optionSome` value, `eitherInl`/`eitherInr` value, `recordIntro`
field, `refineIntro` value, `glueIntro` base, `listCons`
head/tail, `modIntro` inner) plus the
`RawTerm.IsNeutral.isStronglyNormalizing_of_progress_closure`
raw CR3 gate and its Term wrapper.

## Root status

Layer 3 metatheory leaf.  Fourth and final slice of K12.20.U4
stable base. -/

namespace LeanFX2


/-- Shape-specialized inversion for application SN.  The induction is
over an arbitrary SN source and receives the application shape as an
equality, which keeps Lean's indexed-inductive eliminator in the
structural fragment. -/
theorem RawTerm.app_function_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {functionRaw argumentRaw : RawTerm scope},
      source = RawTerm.app functionRaw argumentRaw →
      RawTerm.isStronglyNormalizing functionRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro functionRaw argumentRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro functionRaw ?_
    intro functionTarget functionProgress
    have appProgress :
        RawStep.parProgress
          (RawTerm.app functionRaw argumentRaw)
          (RawTerm.app functionTarget argumentRaw) := by
      refine ⟨RawStep.par.app functionProgress.1
        (RawStep.par.refl argumentRaw), ?_⟩
      intro appEq
      apply functionProgress.2
      injection appEq
    exact inductiveHypothesis
      (RawTerm.app functionTarget argumentRaw) appProgress rfl

/-- If an application is strongly normalizing, its function subterm is
strongly normalizing.  This is used by SN-output eliminator CR3: branch
closures often expose SN only after applying a branch, while neutral
eliminator congruence needs SN of the branch term itself. -/
theorem RawTerm.app_function_isStronglyNormalizing {scope : Nat}
    {functionRaw argumentRaw : RawTerm scope}
    (appIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.app functionRaw argumentRaw)) :
    RawTerm.isStronglyNormalizing functionRaw :=
  RawTerm.app_function_isStronglyNormalizing_aux appIsSN rfl

/-- Shape-specialized inversion for application-argument SN.  This is
the argument-position sibling of `app_function_isStronglyNormalizing_aux`:
the induction is over an arbitrary SN source and receives the application
shape as an equality. -/
theorem RawTerm.app_argument_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {functionRaw argumentRaw : RawTerm scope},
      source = RawTerm.app functionRaw argumentRaw →
      RawTerm.isStronglyNormalizing argumentRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro functionRaw argumentRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro argumentRaw ?_
    intro argumentTarget argumentProgress
    have appProgress :
        RawStep.parProgress
          (RawTerm.app functionRaw argumentRaw)
          (RawTerm.app functionRaw argumentTarget) := by
      refine ⟨RawStep.par.app (RawStep.par.refl functionRaw)
        argumentProgress.1, ?_⟩
      intro appEq
      apply argumentProgress.2
      injection appEq
    exact inductiveHypothesis
      (RawTerm.app functionRaw argumentTarget) appProgress rfl

/-- If an application is strongly normalizing, its argument subterm is
strongly normalizing.  Used alongside function-position inversion when
head-β and eliminator proofs need to recover SN of raw subterms from an
already-normalizing application. -/
theorem RawTerm.app_argument_isStronglyNormalizing {scope : Nat}
    {functionRaw argumentRaw : RawTerm scope}
    (appIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.app functionRaw argumentRaw)) :
    RawTerm.isStronglyNormalizing argumentRaw :=
  RawTerm.app_argument_isStronglyNormalizing_aux appIsSN rfl

/-- Shape-specialized inversion for predecessor SN from successor SN. -/
theorem RawTerm.natSucc_predecessor_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {predecessorRaw : RawTerm scope},
      source = RawTerm.natSucc predecessorRaw →
      RawTerm.isStronglyNormalizing predecessorRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro predecessorRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro predecessorRaw ?_
    intro predecessorTarget predecessorProgress
    have succProgress :
        RawStep.parProgress
          (RawTerm.natSucc predecessorRaw)
          (RawTerm.natSucc predecessorTarget) := by
      refine ⟨RawStep.par.natSucc predecessorProgress.1, ?_⟩
      intro succEq
      apply predecessorProgress.2
      injection succEq
    exact inductiveHypothesis
      (RawTerm.natSucc predecessorTarget) succProgress rfl

/-- If a natural successor is strongly normalizing, its predecessor is
strongly normalizing.  Used by nat-eliminator successor ι expansions. -/
theorem RawTerm.natSucc_predecessor_isStronglyNormalizing {scope : Nat}
    {predecessorRaw : RawTerm scope}
    (successorIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.natSucc predecessorRaw)) :
    RawTerm.isStronglyNormalizing predecessorRaw :=
  RawTerm.natSucc_predecessor_isStronglyNormalizing_aux
    successorIsSN rfl

/-- Shape-specialized inversion for first component SN from pair SN. -/
theorem RawTerm.pair_first_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {firstRaw secondRaw : RawTerm scope},
      source = RawTerm.pair firstRaw secondRaw →
      RawTerm.isStronglyNormalizing firstRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro firstRaw secondRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro firstRaw ?_
    intro firstTarget firstProgress
    have pairProgress :
        RawStep.parProgress
          (RawTerm.pair firstRaw secondRaw)
          (RawTerm.pair firstTarget secondRaw) := by
      refine ⟨RawStep.par.pair firstProgress.1
        (RawStep.par.refl secondRaw), ?_⟩
      intro pairEq
      apply firstProgress.2
      injection pairEq
    exact inductiveHypothesis
      (RawTerm.pair firstTarget secondRaw) pairProgress rfl

/-- If a pair is strongly normalizing, its first component is strongly
normalizing. -/
theorem RawTerm.pair_first_isStronglyNormalizing {scope : Nat}
    {firstRaw secondRaw : RawTerm scope}
    (pairIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.pair firstRaw secondRaw)) :
    RawTerm.isStronglyNormalizing firstRaw :=
  RawTerm.pair_first_isStronglyNormalizing_aux pairIsSN rfl

/-- Shape-specialized inversion for second component SN from pair SN. -/
theorem RawTerm.pair_second_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {firstRaw secondRaw : RawTerm scope},
      source = RawTerm.pair firstRaw secondRaw →
      RawTerm.isStronglyNormalizing secondRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro firstRaw secondRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro secondRaw ?_
    intro secondTarget secondProgress
    have pairProgress :
        RawStep.parProgress
          (RawTerm.pair firstRaw secondRaw)
          (RawTerm.pair firstRaw secondTarget) := by
      refine ⟨RawStep.par.pair (RawStep.par.refl firstRaw)
        secondProgress.1, ?_⟩
      intro pairEq
      apply secondProgress.2
      injection pairEq
    exact inductiveHypothesis
      (RawTerm.pair firstRaw secondTarget) pairProgress rfl

/-- If a pair is strongly normalizing, its second component is strongly
normalizing. -/
theorem RawTerm.pair_second_isStronglyNormalizing {scope : Nat}
    {firstRaw secondRaw : RawTerm scope}
    (pairIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.pair firstRaw secondRaw)) :
    RawTerm.isStronglyNormalizing secondRaw :=
  RawTerm.pair_second_isStronglyNormalizing_aux pairIsSN rfl

/-- Shape-specialized inversion for option payload SN. -/
theorem RawTerm.optionSome_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw : RawTerm scope},
      source = RawTerm.optionSome valueRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have optionProgress :
        RawStep.parProgress
          (RawTerm.optionSome valueRaw)
          (RawTerm.optionSome valueTarget) := by
      refine ⟨RawStep.par.optionSome valueProgress.1, ?_⟩
      intro optionEq
      apply valueProgress.2
      injection optionEq
    exact inductiveHypothesis
      (RawTerm.optionSome valueTarget) optionProgress rfl

/-- If `optionSome value` is strongly normalizing, then `value` is
strongly normalizing. -/
theorem RawTerm.optionSome_value_isStronglyNormalizing {scope : Nat}
    {valueRaw : RawTerm scope}
    (optionIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.optionSome valueRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.optionSome_value_isStronglyNormalizing_aux optionIsSN rfl

/-- Shape-specialized inversion for either-left payload SN. -/
theorem RawTerm.eitherInl_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw : RawTerm scope},
      source = RawTerm.eitherInl valueRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have eitherProgress :
        RawStep.parProgress
          (RawTerm.eitherInl valueRaw)
          (RawTerm.eitherInl valueTarget) := by
      refine ⟨RawStep.par.eitherInl valueProgress.1, ?_⟩
      intro eitherEq
      apply valueProgress.2
      injection eitherEq
    exact inductiveHypothesis
      (RawTerm.eitherInl valueTarget) eitherProgress rfl

/-- If `eitherInl value` is strongly normalizing, then `value` is
strongly normalizing. -/
theorem RawTerm.eitherInl_value_isStronglyNormalizing {scope : Nat}
    {valueRaw : RawTerm scope}
    (eitherIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherInl valueRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.eitherInl_value_isStronglyNormalizing_aux eitherIsSN rfl

/-- Shape-specialized inversion for either-right payload SN. -/
theorem RawTerm.eitherInr_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw : RawTerm scope},
      source = RawTerm.eitherInr valueRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have eitherProgress :
        RawStep.parProgress
          (RawTerm.eitherInr valueRaw)
          (RawTerm.eitherInr valueTarget) := by
      refine ⟨RawStep.par.eitherInr valueProgress.1, ?_⟩
      intro eitherEq
      apply valueProgress.2
      injection eitherEq
    exact inductiveHypothesis
      (RawTerm.eitherInr valueTarget) eitherProgress rfl

/-- If `eitherInr value` is strongly normalizing, then `value` is
strongly normalizing. -/
theorem RawTerm.eitherInr_value_isStronglyNormalizing {scope : Nat}
    {valueRaw : RawTerm scope}
    (eitherIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherInr valueRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.eitherInr_value_isStronglyNormalizing_aux eitherIsSN rfl

/-- Shape-specialized inversion for single-field record payload SN. -/
theorem RawTerm.recordIntro_field_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {fieldRaw : RawTerm scope},
      source = RawTerm.recordIntro fieldRaw →
      RawTerm.isStronglyNormalizing fieldRaw := by
  induction sourceIsSN with
  | intro currentSource _ inductiveHypothesis =>
    intro fieldRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro fieldRaw ?_
    intro fieldTarget fieldProgress
    have recordProgress :
        RawStep.parProgress
          (RawTerm.recordIntro fieldRaw)
          (RawTerm.recordIntro fieldTarget) := by
      refine ⟨RawStep.par.recordIntroCong fieldProgress.1, ?_⟩
      intro recordEq
      apply fieldProgress.2
      injection recordEq
    exact inductiveHypothesis
      (RawTerm.recordIntro fieldTarget) recordProgress rfl

/-- If a record introduction is strongly normalizing, then its field is
strongly normalizing. -/
theorem RawTerm.recordIntro_field_isStronglyNormalizing {scope : Nat}
    {fieldRaw : RawTerm scope}
    (recordIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.recordIntro fieldRaw)) :
    RawTerm.isStronglyNormalizing fieldRaw :=
  RawTerm.recordIntro_field_isStronglyNormalizing_aux recordIsSN rfl

/-- Shape-specialized inversion for refinement-intro value payload SN. -/
theorem RawTerm.refineIntro_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw proofRaw : RawTerm scope},
      source = RawTerm.refineIntro valueRaw proofRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw proofRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have refineProgress :
        RawStep.parProgress
          (RawTerm.refineIntro valueRaw proofRaw)
          (RawTerm.refineIntro valueTarget proofRaw) := by
      refine ⟨RawStep.par.refineIntroCong valueProgress.1
        (RawStep.par.refl proofRaw), ?_⟩
      intro refineEq
      apply valueProgress.2
      injection refineEq
    exact inductiveHypothesis
      (RawTerm.refineIntro valueTarget proofRaw) refineProgress rfl

/-- If a refinement introduction is strongly normalizing, then its
value payload is strongly normalizing. -/
theorem RawTerm.refineIntro_value_isStronglyNormalizing {scope : Nat}
    {valueRaw proofRaw : RawTerm scope}
    (refineIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.refineIntro valueRaw proofRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.refineIntro_value_isStronglyNormalizing_aux refineIsSN rfl

/-- Shape-specialized inversion for Glue-intro base payload SN. -/
theorem RawTerm.glueIntro_base_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {baseRaw partialRaw : RawTerm scope},
      source = RawTerm.glueIntro baseRaw partialRaw →
      RawTerm.isStronglyNormalizing baseRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro baseRaw partialRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro baseRaw ?_
    intro baseTarget baseProgress
    have glueProgress :
        RawStep.parProgress
          (RawTerm.glueIntro baseRaw partialRaw)
          (RawTerm.glueIntro baseTarget partialRaw) := by
      refine ⟨RawStep.par.glueIntroCong baseProgress.1
        (RawStep.par.refl partialRaw), ?_⟩
      intro glueEq
      apply baseProgress.2
      injection glueEq
    exact inductiveHypothesis
      (RawTerm.glueIntro baseTarget partialRaw) glueProgress rfl

/-- If a Glue introduction is strongly normalizing, then its base
payload is strongly normalizing. -/
theorem RawTerm.glueIntro_base_isStronglyNormalizing {scope : Nat}
    {baseRaw partialRaw : RawTerm scope}
    (glueIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.glueIntro baseRaw partialRaw)) :
    RawTerm.isStronglyNormalizing baseRaw :=
  RawTerm.glueIntro_base_isStronglyNormalizing_aux glueIsSN rfl

/-- Shape-specialized inversion for list-cons head SN. -/
theorem RawTerm.listCons_head_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {headRaw tailRaw : RawTerm scope},
      source = RawTerm.listCons headRaw tailRaw →
      RawTerm.isStronglyNormalizing headRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro headRaw tailRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro headRaw ?_
    intro headTarget headProgress
    have consProgress :
        RawStep.parProgress
          (RawTerm.listCons headRaw tailRaw)
          (RawTerm.listCons headTarget tailRaw) := by
      refine ⟨RawStep.par.listCons headProgress.1
        (RawStep.par.refl tailRaw), ?_⟩
      intro consEq
      apply headProgress.2
      injection consEq
    exact inductiveHypothesis
      (RawTerm.listCons headTarget tailRaw) consProgress rfl

/-- If `listCons head tail` is strongly normalizing, then `head` is
strongly normalizing. -/
theorem RawTerm.listCons_head_isStronglyNormalizing {scope : Nat}
    {headRaw tailRaw : RawTerm scope}
    (consIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.listCons headRaw tailRaw)) :
    RawTerm.isStronglyNormalizing headRaw :=
  RawTerm.listCons_head_isStronglyNormalizing_aux consIsSN rfl

/-- Shape-specialized inversion for list-cons tail SN. -/
theorem RawTerm.listCons_tail_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {headRaw tailRaw : RawTerm scope},
      source = RawTerm.listCons headRaw tailRaw →
      RawTerm.isStronglyNormalizing tailRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro headRaw tailRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro tailRaw ?_
    intro tailTarget tailProgress
    have consProgress :
        RawStep.parProgress
          (RawTerm.listCons headRaw tailRaw)
          (RawTerm.listCons headRaw tailTarget) := by
      refine ⟨RawStep.par.listCons (RawStep.par.refl headRaw)
        tailProgress.1, ?_⟩
      intro consEq
      apply tailProgress.2
      injection consEq
    exact inductiveHypothesis
      (RawTerm.listCons headRaw tailTarget) consProgress rfl

/-- If `listCons head tail` is strongly normalizing, then `tail` is
strongly normalizing. -/
theorem RawTerm.listCons_tail_isStronglyNormalizing {scope : Nat}
    {headRaw tailRaw : RawTerm scope}
    (consIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.listCons headRaw tailRaw)) :
    RawTerm.isStronglyNormalizing tailRaw :=
  RawTerm.listCons_tail_isStronglyNormalizing_aux consIsSN rfl

/-- Shape-specialized inversion for modal-introduction payload SN. -/
theorem RawTerm.modIntro_inner_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {innerRaw : RawTerm scope},
      source = RawTerm.modIntro innerRaw →
      RawTerm.isStronglyNormalizing innerRaw := by
  induction sourceIsSN with
  | intro currentSource _ inductiveHypothesis =>
    intro innerRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro innerRaw ?_
    intro innerTarget innerProgress
    have introProgress :
        RawStep.parProgress
          (RawTerm.modIntro innerRaw)
          (RawTerm.modIntro innerTarget) := by
      refine ⟨RawStep.par.modIntro innerProgress.1, ?_⟩
      intro introEq
      apply innerProgress.2
      injection introEq
    exact inductiveHypothesis
      (RawTerm.modIntro innerTarget) introProgress rfl

/-- If `modIntro inner` is strongly normalizing, then `inner` is
strongly normalizing. -/
theorem RawTerm.modIntro_inner_isStronglyNormalizing {scope : Nat}
    {innerRaw : RawTerm scope}
    (introIsSN :
      RawTerm.isStronglyNormalizing (RawTerm.modIntro innerRaw)) :
    RawTerm.isStronglyNormalizing innerRaw :=
  RawTerm.modIntro_inner_isStronglyNormalizing_aux introIsSN rfl

/-- **K12.20.U2 raw CR3 skeleton**: a raw term is strongly
normalizing when every non-trivial parallel-progress reduct is
strongly normalizing.

This is the constructor direction of the SN definition, named because
the typed CR3 proof repeatedly reduces its SN-direct arms to exactly
this shape.  Neutrality is intentionally not required here: neutrality
is what makes the premise provable for variables and stuck eliminators;
the raw SN constructor itself only needs the reduct closure. -/
theorem RawTerm.isStronglyNormalizing.of_progress_closure {scope : Nat}
    {source : RawTerm scope}
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress source target →
        RawTerm.isStronglyNormalizing target) :
    RawTerm.isStronglyNormalizing source :=
  RawTerm.isStronglyNormalizing.intro source closure

/-- Typed wrapper around `RawTerm.isStronglyNormalizing.of_progress_closure`.
The term's type is irrelevant because typed SN is raw SN of the term's
structural raw index. -/
theorem Term.isStronglyNormalizing.of_raw_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Term.isStronglyNormalizing sourceTerm :=
  RawTerm.isStronglyNormalizing.of_progress_closure closure

/-- **K12.20.U2 raw CR3, neutral form**: a neutral raw term is SN
when all of its non-trivial progress reducts are SN.

The neutral witness is not computationally needed by the SN
constructor; it records the Tait CR3 contract at the call site.  In
later compound arms the neutral witness is what makes the reduct
closure available, while this lemma performs the final SN packaging. -/
theorem RawTerm.IsNeutral.isStronglyNormalizing_of_progress_closure
    {scope : Nat}
    {source : RawTerm scope}
    (_sourceIsNeutral : RawTerm.IsNeutral source)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress source target →
        RawTerm.isStronglyNormalizing target) :
    RawTerm.isStronglyNormalizing source :=
  RawTerm.isStronglyNormalizing.of_progress_closure closure

/-- Typed wrapper for the neutral raw CR3 form. -/
theorem Term.isStronglyNormalizing_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Term.isStronglyNormalizing sourceTerm :=
  RawTerm.IsNeutral.isStronglyNormalizing_of_progress_closure
    sourceIsNeutral closure



end LeanFX2
