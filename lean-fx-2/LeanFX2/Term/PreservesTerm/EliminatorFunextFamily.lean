import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Term.Inversion

/-! # LeanFX2.Term.PreservesTerm.EliminatorFunextFamily

Cong-only lifts for four schematic-payload HoTT-special ctors whose
raw-cascade companion rules consume RAW steps directly (no typed-IH
parameter on the schematic payload) and whose typed cong rules exist
in `Reduction/ParRed/ParInductive.lean`:

* `Term.funextRefl domainType codomainType applyRaw` — Univalence-β
  rfl-fragment witness for the Π codomain.
* `Term.funextReflAtId domainType codomainType applyRaw` — same
  payload at `Ty.id (Ty.arrow ...) ...` — universe-level identity at
  arrow types.
* `Term.funextIntroHet domainType codomainType applyARaw applyBRaw` —
  heterogeneous-carrier funext-introduction with two raw payloads.
* `Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw
  rightTyRaw proof` — Univalence-β extractor, single typed child
  (`proof`) at `Ty.id (Ty.universe ...) leftTyRaw rightTyRaw`.

## Why these were deferred at "full lift" form

`TwoTyEliminators.lean` lines 333-342 documents a draft attempt at
`lift_full_funextReflAtId` that took a GENERIC source
`Term context someType (RawTerm.lam (RawTerm.refl applyRaw))` and
dispatched via `cases genericTerm` with `all_goals first | nomatch`.
That dispatch surfaced `Term.lam`, `Term.lamPi`, `Term.funextRefl`,
`Term.funextReflAtId`, and `Term.funextIntroHet` arms — multi-ctor
collision at identical (Ty, raw) signatures — and leaked `Quot.sound`
+ `propext` per the per-decl audit gate.  The "indexed-inductive
partial-match trap" (memo `feedback_lean_indexed_partial_match`)
fired on the multi-ctor dispatch.

## Why these lifts ship NOW (this commit)

We sidestep the multi-ctor dispatch entirely by taking the source
term as ALREADY-STRUCTURED `Term.funextRefl ...` / `Term.funextReflAtId
...` / `Term.funextIntroHet ...` / `Term.uaToEquiv ...`.  No generic
`Term context someType someRaw` source.  No `cases genericTerm`
dispatching across multiple Term ctors.  The lift uses
`RawStep.par.lam_inv` (and its companion `refl_inv`) to project the
raw target shape and the inner payload's raw step, then applies the
typed cong rule directly.

This is the SAME pattern as `lift_full_uaIntroHet` and
`lift_full_oeqFunext` in `SchematicValueCtors.lean`: structured source,
no generic dispatch, no axiom leak.

## What this does NOT ship

* The full Universal-source `lift_full_funextRefl` / `lift_full_*`
  with a generic source dispatch.  That headline form remains
  blocked by the dep-elim / multi-ctor collision trap and is
  deferred to the headline `Term.preserves` assembly phase, where
  the OUTER Term induction supplies the source ctor's identity
  before reaching the inner per-ctor lift.
* The `equivApply` lift — `RawStep.par.equivApply_inv` has TWO β
  arms (`uaReflEquivApply` shallow + `uaReflEquivApplyDeep`) that
  are NOT cong-shaped.  Shipping cong-only there would be unsound
  because the β arms admit additional source raws.  Defers to B.3
  β-rule lifts.

## Root status

Zero-axiom; carved out of the deferred 5-ctor blocker list. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-- **Term.funextRefl cong-only lift.**  The source is the structured
`Term.funextRefl domainType codomainType applyRaw`; the raw projection
is `RawTerm.lam (RawTerm.refl applyRaw)`.  The cong rule
`Step.par.funextReflCong` consumes a raw step on `applyRaw` directly
(no typed-IH parameter needed — the inner payload is schematic raw,
not a typed Term child).

Cascade: `RawStep.par.lam_inv` extracts `bodyTarget = RawTerm.refl
applyTarget` plus the inner step; `RawStep.par.refl_inv` then projects
that to `RawStep.par applyRaw applyTarget`.  Apply
`Step.par.funextReflCong`. -/
theorem RawStep.par.lift_funextRefl
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.lam (RawTerm.refl applyRaw) : RawTerm scope)
                  targetRaw) :
    ∃ (targetType : Ty level scope)
      (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.funextRefl (context := context)
                         domainType codomainType applyRaw)
        targetTerm := by
  obtain ⟨bodyTarget, lamEq, bodyStep⟩ := RawStep.par.lam_inv rawStep
  obtain ⟨applyTarget, reflEq, applyStep⟩ := RawStep.par.refl_inv bodyStep
  cases reflEq
  cases lamEq
  refine ⟨funextReflType domainType codomainType applyTarget,
          Term.funextRefl (context := context)
                          domainType codomainType applyTarget, ?_⟩
  exact Step.par.funextReflCong domainType codomainType applyStep

/-- **Term.funextReflAtId cong-only lift.**  Source type is
`Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam (RawTerm.refl
applyRaw)) (RawTerm.lam (RawTerm.refl applyRaw))`; raw form is
`RawTerm.lam (RawTerm.refl applyRaw)`.

The cong rule `Step.par.funextReflAtIdCong` reduces inside `applyRaw`
while keeping the source/target Ty fixed (both endpoints of the Id
type are `RawTerm.lam (RawTerm.refl applyRaw<source/target>)`).  But
the target Ty here MUST track the new applyRaw, so the lift's target
type uses `applyTarget` in both Id endpoints.

Cascade matches `lift_funextRefl`: lam_inv + refl_inv unfold; apply
`funextReflAtIdCong`. -/
theorem RawStep.par.lift_funextReflAtId
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.lam (RawTerm.refl applyRaw) : RawTerm scope)
                  targetRaw) :
    ∃ (targetType : Ty level scope)
      (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.funextReflAtId (context := context)
                             domainType codomainType applyRaw)
        targetTerm := by
  obtain ⟨bodyTarget, lamEq, bodyStep⟩ := RawStep.par.lam_inv rawStep
  obtain ⟨applyTarget, reflEq, applyStep⟩ := RawStep.par.refl_inv bodyStep
  cases reflEq
  cases lamEq
  refine ⟨Ty.id (Ty.arrow domainType codomainType)
                (RawTerm.lam (RawTerm.refl applyTarget))
                (RawTerm.lam (RawTerm.refl applyTarget)),
          Term.funextReflAtId (context := context)
                              domainType codomainType applyTarget, ?_⟩
  exact Step.par.funextReflAtIdCong domainType codomainType applyStep

/-- **Term.funextIntroHet cong-only lift.**  Source type is
`Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam applyARaw)
(RawTerm.lam applyBRaw)`; raw form is
`RawTerm.lam (RawTerm.refl applyARaw)`.

The cong rule `Step.par.funextIntroHetCong` reduces inside BOTH
`applyARaw` and `applyBRaw` simultaneously, but the raw cascade only
projects `applyARaw` (since the raw form is `RawTerm.lam (RawTerm.refl
applyARaw)`).  For the lift's `applyBRaw` step we use `RawStep.par.refl
applyBRaw` (the trivial reflexive step) — `Step.par.funextIntroHetCong`
admits independent par-steps on each side.

Cascade: lam_inv + refl_inv on applyARaw; use `RawStep.par.refl
applyBRaw` for the second arm.  Target type mirrors source with
`applyTarget` in the left applyARaw position; right applyBRaw position
stays fixed. -/
theorem RawStep.par.lift_funextIntroHet
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.lam (RawTerm.refl applyARaw) : RawTerm scope)
                  targetRaw) :
    ∃ (targetType : Ty level scope)
      (targetTerm : Term context targetType targetRaw),
      Step.par
        (Term.funextIntroHet (context := context)
                             domainType codomainType applyARaw applyBRaw)
        targetTerm := by
  obtain ⟨bodyTarget, lamEq, bodyStep⟩ := RawStep.par.lam_inv rawStep
  obtain ⟨applyATarget, reflEq, applyAStep⟩ := RawStep.par.refl_inv bodyStep
  cases reflEq
  cases lamEq
  refine ⟨Ty.id (Ty.arrow domainType codomainType)
                (RawTerm.lam applyATarget) (RawTerm.lam applyBRaw),
          Term.funextIntroHet (context := context)
                              domainType codomainType applyATarget applyBRaw, ?_⟩
  exact Step.par.funextIntroHetCong domainType codomainType
                                    applyAStep (RawStep.par.refl applyBRaw)

/-- **Term.uaToEquiv cong-only lift.**  Source is the structured
`Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw
rightTyRaw proof`; raw projection is `RawTerm.uaToEquiv proofRaw`.

The single typed child `proof` has type
`Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw` —
the cong rule `Step.par.uaToEquivCong` takes a TYPED Step.par on the
proof child and produces a typed Step.par on the wrapper.  This is
the binary-cong style of `lift_recordProj` etc.

Cascade: `RawStep.par.uaToEquiv_inv` projects target = `RawTerm.uaToEquiv
proofTarget` + raw step on proofRaw; we feed the proofRaw step into
the typed proofLift IH to get a typed proof target; then apply
`Step.par.uaToEquivCong`. -/
theorem RawStep.par.lift_uaToEquiv
    (innerLevel : UniverseLevel) (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    (proof :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw)
    (proofLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par proofRaw targetRawIH →
      ∃ proofTarget :
          Term context
            (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
            targetRawIH,
        Step.par proof proofTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.uaToEquiv proofRaw) targetRaw) :
    ∃ targetTerm : Term context (Ty.equiv leftTy rightTy) targetRaw,
      Step.par
        (Term.uaToEquiv (context := context) innerLevel innerLevelLt
                        leftTy rightTy leftTyRaw rightTyRaw proof)
        targetTerm := by
  obtain ⟨proofTargetRaw, eq, proofStep⟩ := RawStep.par.uaToEquiv_inv rawStep
  obtain ⟨proofTarget, proofStepTyped⟩ := proofLift proofStep
  cases eq
  refine ⟨Term.uaToEquiv (context := context) innerLevel innerLevelLt
                          leftTy rightTy leftTyRaw rightTyRaw proofTarget, ?_⟩
  exact Step.par.uaToEquivCong innerLevel innerLevelLt
                                leftTy rightTy leftTyRaw rightTyRaw
                                proofStepTyped

end LeanFX2
