import LeanFX2.Term.StrengtheningImage.AggregatorSoundUniversal

/-! # Term/StrengtheningImage/AggregatorTotalCore

Universal totality predicate plus closed-atomic and binder totality wrappers.
-/

namespace LeanFX2

namespace Term

/-! ## Universal totality predicate: `IsAggregatorTotal`.

`IsAggregatorTotal sourceTerm` asserts that for ANY context
strengthening from `sourceTerm`'s context to a target context, and
ANY index strengthening evidence (`sourceType.partialStrengthen?
strengthening.back = some _` and the analogous raw equation), the
typed strengthening dispatcher `partialStrengthenTyped? sourceTerm
strengthening` is guaranteed to return `some _` (not `none`).

This is the totality counterpart to `IsAggregatorSound`: the latter
asserts soundness of a dispatch result conditional on `some`;
`IsAggregatorTotal` asserts the `some` arm always fires when index
witnesses are provided.

The architectural reason for the universal-strengthening shape is
the binder ctors (`Term.lam`, `Term.lamPi`, `Term.pathLam`): their
body's strengthening is the `strengthening.lift` of the parent's,
not a `dropNewest`.  A predicate parameterized only by `newType`
(as in `IsTotalOnWeaken`) cannot transport through the lift; the
universal-strengthening shape can.

Specializing `IsAggregatorTotal sourceTerm` to
`strengthening := ContextStrengthening.dropNewest context newType`
recovers `IsTotalOnWeaken sourceTerm`, so the universal headline
`∀ sourceTerm, IsAggregatorTotal sourceTerm` discharges the
universal `IsTotalOnWeaken` headline by specialization. -/
def IsAggregatorTotal {mode : Mode} {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw) : Prop :=
  ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {targetSourceType : Ty level targetScope}
    {targetSourceRaw : RawTerm targetScope},
    sourceType.partialStrengthen? strengthening.back =
        some targetSourceType →
    sourceRaw.partialStrengthen? strengthening.back =
        some targetSourceRaw →
    (partialStrengthenTyped? sourceTerm strengthening).isSome

/-! ## Per-ctor totality wrappers under `IsAggregatorTotal`.

Each of the 78 ctors gets a wrapper.  The wrapper takes any
constructor-specific `IsAggregatorTotal` inductive hypotheses on
recursive children, plus the constructor's positional non-IH data,
and produces `IsAggregatorTotal` for the constructor application. -/

/-- 0-IH closed-atomic totality wrapper: `Term.unit`.  Atomic ctor
with no payload — every strengthening succeeds because the dispatcher
returns `some _` directly. -/
theorem isAggregatorTotal_unit {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.unit (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.boolTrue`. -/
theorem isAggregatorTotal_boolTrue {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.boolTrue (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.boolFalse`. -/
theorem isAggregatorTotal_boolFalse {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.boolFalse (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.natZero`. -/
theorem isAggregatorTotal_natZero {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.natZero (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.interval0`. -/
theorem isAggregatorTotal_interval0 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.interval0 (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.interval1`. -/
theorem isAggregatorTotal_interval1 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.interval1 (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH variable totality wrapper: `Term.var`.  Requires the
position to survive the strengthening's `back` map — which holds
because we have an index witness for the position's raw form. -/
theorem isAggregatorTotal_var {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (position : Fin sourceScope) :
    IsAggregatorTotal (Term.var (context := sourceCtx) position) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  -- rawStrengthens carries `strengthening.back position = some _`,
  -- which is exactly the dispatcher's surviving arm.
  dsimp only [partialStrengthenTyped?]
  dsimp only [RawTerm.partialStrengthen?, RawTerm.partialRename?] at rawStrengthens
  split at rawStrengthens
  · next survives =>
      split
      · next dispatcherSurvives =>
          rw [survives] at dispatcherSurvives
          cases dispatcherSurvives
      · rfl
  · cases rawStrengthens

/-- 1-IH binder totality wrapper: `Term.lam`.  The body's IH supplies
universal-strengthening totality; we instantiate it at the lifted
strengthening with derived domain/codomain witnesses. -/
theorem isAggregatorTotal_lam {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyTotal : IsAggregatorTotal body) :
    IsAggregatorTotal
      (Term.lam (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- Extract domainSuccess + codomainSuccess from typeStrengthens.
  dsimp only [partialStrengthenTyped?]
  -- typeStrengthens: (Ty.arrow domain codomain).partialStrengthen? back = some _
  -- which unfolds to Option.mapTwo of the children.
  obtain ⟨targetDomainType, targetCodomainType, domainSuccess,
    codomainSuccess, _arrowEq⟩ := Option.mapTwo_eq_some typeStrengthens
  -- rawStrengthens: (RawTerm.lam bodyRaw).partialStrengthen? back = some _
  -- which unfolds to a match on body's raw strengthening through .lift.
  dsimp only [RawTerm.partialStrengthen?, RawTerm.partialRename?] at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetBodyRaw bodyRawSuccess =>
    -- Now we apply bodyTotal at the lifted strengthening.
    -- Need codomainType.weaken strengthens through (strengthening.lift _).back
    -- and bodyRaw strengthens through the same.  Both follow from the
    -- domain/codomain children evidence.
    have codomainWeakenLift :
        codomainType.weaken.partialStrengthen?
            (strengthening.lift domainType targetDomainType
              domainSuccess).back =
          some targetCodomainType.weaken := by
      change codomainType.weaken.partialStrengthen? strengthening.back.lift =
        some targetCodomainType.weaken
      rw [Ty.partialStrengthen?_weaken_lift codomainType strengthening.back,
        codomainSuccess]
      rfl
    have bodyRawLiftSuccess :
        bodyRaw.partialStrengthen?
            (strengthening.lift domainType targetDomainType
              domainSuccess).back =
          some targetBodyRaw := bodyRawSuccess
    have bodyTotalCall :=
      bodyTotal
        (strengthening.lift domainType targetDomainType domainSuccess)
        codomainWeakenLift bodyRawLiftSuccess
    -- The dispatcher splits on domain, codomain, body; we discharge each
    -- failure branch as impossible.
    split
    · next domainFails =>
        rw [domainSuccess] at domainFails; cases domainFails
    · next targetDomainAgain domainSucceedsAgain =>
        rw [domainSuccess] at domainSucceedsAgain
        cases domainSucceedsAgain
        split
        · next codomainFails =>
            rw [codomainSuccess] at codomainFails; cases codomainFails
        · next _ _ =>
            split
            · next bodyFails =>
                -- bodyFails contradicts bodyTotalCall via isSome.
                rw [bodyFails] at bodyTotalCall
                cases bodyTotalCall
            · rfl

/-- 1-IH binder totality wrapper: `Term.lamPi`.  Dependent lambda;
the codomain lives inside the binder, so the lifted strengthening
already strengthens it (no double weakening). -/
theorem isAggregatorTotal_lamPi {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (bodyTotal : IsAggregatorTotal body) :
    IsAggregatorTotal
      (Term.lamPi (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  dsimp only [partialStrengthenTyped?]
  -- typeStrengthens: (Ty.piTy domain codomain).partialStrengthen? back = some _
  -- piTy strengthens via Option.mapTwo (domain..back) (codomain..back.lift) Ty.piTy
  obtain ⟨targetDomainType, targetCodomainType, domainSuccess,
    codomainLiftSuccess, _piEq⟩ := Option.mapTwo_eq_some typeStrengthens
  dsimp only [RawTerm.partialStrengthen?, RawTerm.partialRename?] at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetBodyRaw bodyRawSuccess =>
    -- codomainLiftSuccess already gives us what we need.
    have codomainSuccessAtLift :
        codomainType.partialStrengthen?
            (strengthening.lift domainType targetDomainType
              domainSuccess).back =
          some targetCodomainType := codomainLiftSuccess
    have bodyRawLiftSuccess :
        bodyRaw.partialStrengthen?
            (strengthening.lift domainType targetDomainType
              domainSuccess).back =
          some targetBodyRaw := bodyRawSuccess
    have bodyTotalCall :=
      bodyTotal
        (strengthening.lift domainType targetDomainType domainSuccess)
        codomainSuccessAtLift bodyRawLiftSuccess
    split
    · next domainFails =>
        rw [domainSuccess] at domainFails; cases domainFails
    · next targetDomainAgain domainSucceedsAgain =>
        rw [domainSuccess] at domainSucceedsAgain
        cases domainSucceedsAgain
        split
        · next bodyFails =>
            rw [bodyFails] at bodyTotalCall
            cases bodyTotalCall
        · rfl

/-- 1-IH binder totality wrapper: `Term.pathLam`.  Cubical path
lambda; the body binds an interval slot, with carrier weakened. -/
theorem isAggregatorTotal_pathLam {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyTotal : IsAggregatorTotal body) :
    IsAggregatorTotal
      (Term.pathLam (context := sourceCtx) modeIsUnivalent carrierType
        leftEndpoint rightEndpoint body) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  dsimp only [partialStrengthenTyped?]
  -- typeStrengthens for Ty.path: Option.mapThree (carrier..) (left..) (right..) Ty.path
  obtain ⟨targetCarrierType, targetLeftEndpoint, targetRightEndpoint,
    carrierSuccess, leftSuccess, rightSuccess, _pathEq⟩ :=
    Option.mapThree_eq_some typeStrengthens
  dsimp only [RawTerm.partialStrengthen?, RawTerm.partialRename?] at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetBodyRaw bodyRawSuccess =>
    have carrierWeakenLift :
        carrierType.weaken.partialStrengthen?
            (strengthening.lift Ty.interval Ty.interval rfl).back =
          some targetCarrierType.weaken := by
      change carrierType.weaken.partialStrengthen? strengthening.back.lift =
        some targetCarrierType.weaken
      rw [Ty.partialStrengthen?_weaken_lift carrierType strengthening.back,
        carrierSuccess]
      rfl
    have bodyRawLiftSuccess :
        bodyRaw.partialStrengthen?
            (strengthening.lift Ty.interval Ty.interval rfl).back =
          some targetBodyRaw := bodyRawSuccess
    have bodyTotalCall :=
      bodyTotal (strengthening.lift Ty.interval Ty.interval rfl)
        carrierWeakenLift bodyRawLiftSuccess
    split
    · next carrierFails =>
        rw [carrierSuccess] at carrierFails; cases carrierFails
    · next targetCarrierAgain carrierSucceedsAgain =>
        rw [carrierSuccess] at carrierSucceedsAgain
        cases carrierSucceedsAgain
        split
        · next leftFails =>
            rw [leftSuccess] at leftFails; cases leftFails
        · next targetLeftAgain leftSucceedsAgain =>
            rw [leftSuccess] at leftSucceedsAgain
            cases leftSucceedsAgain
            split
            · next rightFails =>
                rw [rightSuccess] at rightFails; cases rightFails
            · next targetRightAgain rightSucceedsAgain =>
                rw [rightSuccess] at rightSucceedsAgain
                cases rightSucceedsAgain
                split
                · next bodyFails =>
                    rw [bodyFails] at bodyTotalCall
                    cases bodyTotalCall
                · rfl

end Term

end LeanFX2
