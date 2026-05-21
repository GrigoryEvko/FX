import LeanFX2.Term.TypedInversion
import LeanFX2.Term.StrengtheningImage.ImageUnweaken

/-! # Term/EtaRecognizers

Typed recognizers for eta-shaped term fragments.

This file starts with the lambda eta app-arm recognizer.  It is the
small T12 bridge between:

* `Term.app_inv`, which exposes a concrete `Term.app` arm,
* `Term.weakenInverse_atVarZero`, which recognizes the newest
  variable argument, and
* `Term.weaken_inv_arrow`, which turns a successful unweaken of the
  function side into the canonical weakened function.

The harder disjunctive `lam_inv` theorem can consume this theorem
after it has already selected the `Term.app` branch of the lambda body.
-/

namespace LeanFX2

namespace Term

/-- Recognize the concrete lambda eta app arm.

If an application under `context.cons domainType` has function side in
the weakening image of an arrow `domainType -> codomainType`, and its
argument side is the newest variable, then the app is heterogeneously
equal to the canonical `eta_lam_shape_construct` for the recovered
outer-scope function.

This is intentionally an app-arm recognizer, not the full
`lam_inv_disjunctive` theorem: callers still use `Term.app_inv` to
separate `Term.app` from `Term.appPi`, then use this lemma on the
`Term.app` branch. -/
theorem eta_lam_shape_recognize_app_of_unweaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw : RawTerm scope}
    (functionTerm :
      Term (context.cons domainType)
        (Ty.arrow domainType codomainType).weaken
        functionRaw.weaken)
    (argumentTerm :
      Term (context.cons domainType)
        domainType.weaken
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
    {originalFunction :
      Term context (Ty.arrow domainType codomainType) functionRaw}
    (functionUnweaken :
      Term.unweaken? functionTerm = some originalFunction) :
    HEq (Term.app functionTerm argumentTerm)
        (Term.eta_lam_shape_construct originalFunction) := by
  have functionHEq :
      HEq functionTerm
        (Term.weaken (newType := domainType) originalFunction) :=
    Term.weaken_inv_arrow functionTerm functionUnweaken
  obtain ⟨_, argumentHEq⟩ :=
    Term.weakenInverse_atVarZero
      (context := context)
      (newType := domainType)
      (weakenedTerm := argumentTerm)
  dsimp only [Term.eta_lam_shape_construct]
  cases functionHEq
  cases argumentHEq
  rfl

/-- Dependent-Pi eta body constructor at the exact `appPi` result type.

Unlike the non-dependent lambda body, the Pi codomain under weakened
function type is renamed by `RawRenaming.weaken.lift`: the Pi-bound
slot remains fixed while the outer context shifts.  This constructor
keeps that exact index instead of forcing a stronger codomain cast. -/
def eta_lamPi_shape_body_construct
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw : RawTerm scope}
    (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw) :
    Term (context.cons domainType)
      ((codomainType.rename RawRenaming.weaken.lift).subst0
        domainType.weaken
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
      (RawTerm.app functionRaw.weaken
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) :=
  Term.appPi
    (codomainType := codomainType.rename RawRenaming.weaken.lift)
    (Term.weaken (newType := domainType) functionTerm)
    (Term.var (context := context.cons domainType)
      ⟨0, Nat.zero_lt_succ scope⟩)

/-- Recognize the concrete dependent-Pi eta appPi arm.

If a dependent application under `context.cons domainType` has function
side in the weakening image of a Pi term, and its argument side is the
newest variable, then the application is heterogeneously equal to the
canonical eta body for the recovered outer-scope function. -/
theorem eta_lamPi_shape_recognize_appPi_of_unweaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw : RawTerm scope}
    (functionTerm :
      Term (context.cons domainType)
        (Ty.piTy domainType codomainType).weaken
        functionRaw.weaken)
    (argumentTerm :
      Term (context.cons domainType)
        domainType.weaken
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
    {originalFunction :
      Term context (Ty.piTy domainType codomainType) functionRaw}
    (functionUnweaken :
      Term.unweaken? functionTerm = some originalFunction) :
    HEq (Term.appPi functionTerm argumentTerm)
        (Term.eta_lamPi_shape_body_construct originalFunction) := by
  have functionHEq :
      HEq functionTerm
        (Term.weaken (newType := domainType) originalFunction) :=
    Term.weaken_inv_pi functionTerm functionUnweaken
  obtain ⟨_, argumentHEq⟩ :=
    Term.weakenInverse_atVarZero
      (context := context)
      (newType := domainType)
      (weakenedTerm := argumentTerm)
  dsimp only [Term.eta_lamPi_shape_body_construct]
  cases functionHEq
  cases argumentHEq
  exact HEq.rfl

/-- Sigma eta constructor: rebuild a pair from its projections. -/
def eta_pair_shape_construct
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Term context (Ty.sigmaTy firstType secondType)
      (RawTerm.pair (RawTerm.fst pairRaw) (RawTerm.snd pairRaw)) :=
  Term.pair (Term.fst pairTerm) (Term.snd pairTerm)

/-- Recognize the concrete Sigma eta pair arm once both projections have
been identified. -/
theorem eta_pair_shape_recognize_projections
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (firstProjection :
      Term context firstType (RawTerm.fst pairRaw))
    (secondProjection :
      Term context (secondType.subst0 firstType (RawTerm.fst pairRaw))
        (RawTerm.snd pairRaw))
    (firstProjectionHEq :
      HEq firstProjection (Term.fst pairTerm))
    (secondProjectionHEq :
      HEq secondProjection (Term.snd pairTerm)) :
    HEq (Term.pair firstProjection secondProjection)
        (Term.eta_pair_shape_construct pairTerm) := by
  cases firstProjectionHEq
  cases secondProjectionHEq
  rfl

/-- Single-field record eta constructor: rebuild a record from its
projection. -/
def eta_record_shape_construct
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw) :
    Term context (Ty.record singleFieldType)
      (RawTerm.recordIntro (RawTerm.recordProj recordRaw)) :=
  Term.recordIntro (Term.recordProj recordValue)

/-- Recognize the concrete single-field record eta arm once the field
projection has been identified. -/
theorem eta_record_shape_recognize_projection
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw)
    (fieldProjection :
      Term context singleFieldType (RawTerm.recordProj recordRaw))
    (fieldProjectionHEq :
      HEq fieldProjection (Term.recordProj recordValue)) :
    HEq (Term.recordIntro fieldProjection)
        (Term.eta_record_shape_construct recordValue) := by
  cases fieldProjectionHEq
  rfl

/-- Generic modal eta constructor for the current `modIntro`/`modElim`
typed core. -/
def eta_modal_shape_construct
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {modalRaw : RawTerm scope}
    (modalTerm : Term context innerType modalRaw) :
    Term context innerType
      (RawTerm.modIntro (RawTerm.modElim modalRaw)) :=
  Term.modIntro (Term.modElim modalTerm)

/-- Recognize the concrete generic modal eta arm once the eliminated
modal payload has been identified. -/
theorem eta_modal_shape_recognize_elim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {modalRaw : RawTerm scope}
    (modalTerm : Term context innerType modalRaw)
    (eliminatedTerm :
      Term context innerType (RawTerm.modElim modalRaw))
    (eliminatedTermHEq :
      HEq eliminatedTerm (Term.modElim modalTerm)) :
    HEq (Term.modIntro eliminatedTerm)
        (Term.eta_modal_shape_construct modalTerm) := by
  cases eliminatedTermHEq
  rfl

/-- Refinement eta constructor with an explicit proof payload.

The refined term supplies the underlying value through `refineElim`.
The proof payload is not recoverable from the refined value, so callers
provide the proof term that appears in the eta-shaped introduction. -/
def eta_refine_shape_construct
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw proofRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (predicateProof : Term context Ty.unit proofRaw) :
    Term context (Ty.refine baseType predicate)
      (RawTerm.refineIntro (RawTerm.refineElim refinedRaw) proofRaw) :=
  Term.refineIntro predicate (Term.refineElim refinedValue) predicateProof

/-- Recognize the concrete refinement eta arm once both the eliminated
base value and explicit proof payload have been identified. -/
theorem eta_refine_shape_recognize_elim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw proofRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (predicateProof : Term context Ty.unit proofRaw)
    (baseProjection :
      Term context baseType (RawTerm.refineElim refinedRaw))
    (proofProjection : Term context Ty.unit proofRaw)
    (baseProjectionHEq :
      HEq baseProjection (Term.refineElim refinedValue))
    (proofProjectionHEq :
      HEq proofProjection predicateProof) :
    HEq (Term.refineIntro predicate baseProjection proofProjection)
        (Term.eta_refine_shape_construct refinedValue predicateProof) := by
  cases baseProjectionHEq
  cases proofProjectionHEq
  rfl

/-- Codata eta constructor for the current unfold/dest typed core.

The present core has `codataUnfold` and `codataDest`, but no typed
projection that recovers an unfold state and transition from an
arbitrary codata value.  The honest recognizer therefore works at the
intro payload boundary: once callers have identified the state and
transition payloads, the eta-shaped codata value is canonical. -/
def eta_codata_shape_construct
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw) :
    Term context (Ty.codata stateType outputType)
      (RawTerm.codataUnfold stateRaw transitionRaw) :=
  Term.codataUnfold initialState transition

/-- Recognize the concrete codata eta intro arm once both unfold
payloads have been identified. -/
theorem eta_codata_shape_recognize_unfold
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw)
    (observedState : Term context stateType stateRaw)
    (observedTransition :
      Term context (Ty.arrow stateType outputType) transitionRaw)
    (stateHEq : HEq observedState initialState)
    (transitionHEq : HEq observedTransition transition) :
    HEq (Term.codataUnfold observedState observedTransition)
        (Term.eta_codata_shape_construct initialState transition) := by
  cases stateHEq
  cases transitionHEq
  rfl

/-- Equivalence eta constructor for the current `equivIntroHet`
typed core.

The equivalence introduction carries computational forward/backward
maps plus proof payloads.  There is currently no inverse-projection
term constructor, so the recognizer is payload-explicit just like the
refinement recognizer above. -/
def eta_equiv_shape_construct
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw) :
    Term context (Ty.equiv carrierA carrierB)
      (RawTerm.equivIntro forwardRaw backwardRaw) :=
  Term.equivIntroHet forward backward leftInv rightInv

/-- Recognize the concrete equivalence eta intro arm once all explicit
payloads have been identified. -/
theorem eta_equiv_shape_recognize_intro
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw)
    (observedForward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (observedBackward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (observedLeftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (observedRightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw)
    (forwardHEq : HEq observedForward forward)
    (backwardHEq : HEq observedBackward backward)
    (leftInvHEq : HEq observedLeftInv leftInv)
    (rightInvHEq : HEq observedRightInv rightInv) :
    HEq
      (Term.equivIntroHet observedForward observedBackward
        observedLeftInv observedRightInv)
      (Term.eta_equiv_shape_construct forward backward leftInv rightInv) := by
  cases forwardHEq
  cases backwardHEq
  cases leftInvHEq
  cases rightInvHEq
  rfl

/-- Unit eta constructor. -/
def eta_unit_shape_construct
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    Term context Ty.unit RawTerm.unit :=
  Term.unit

/-- Recognize the unique typed unit eta shape. -/
theorem eta_unit_shape_recognize
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (unitValue : Term context Ty.unit RawTerm.unit) :
    HEq unitValue (Term.eta_unit_shape_construct (context := context)) := by
  suffices key :
      ∀ {genericType : Ty level scope}
        (genericTerm : Term context genericType RawTerm.unit),
        HEq genericTerm (Term.eta_unit_shape_construct (context := context)) by
    exact key unitValue
  intro genericType genericTerm
  cases genericTerm
  rfl

/-- Recognize the concrete path eta application arm.

If a path application under an interval binder has path side in the
weakening image of a path term, and its interval argument is the newest
variable, then the application is heterogeneously equal to the
canonical `eta_path_shape_construct` for the recovered outer-scope
path. -/
theorem eta_path_shape_recognize_app_of_unweaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint pathRaw : RawTerm scope}
    (pathTerm :
      Term (context.cons Ty.interval)
        (Ty.path carrierType leftEndpoint rightEndpoint).weaken
        pathRaw.weaken)
    (intervalTerm :
      Term (context.cons Ty.interval)
        Ty.interval
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
    {originalPath :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    (pathUnweaken :
      Term.unweaken? pathTerm = some originalPath) :
    HEq (Term.pathApp modeIsUnivalent pathTerm intervalTerm)
        (Term.eta_path_shape_construct modeIsUnivalent originalPath) := by
  have pathHEq :
      HEq pathTerm
        (Term.weaken (newType := Ty.interval) originalPath) :=
    Term.weaken_inv_path pathTerm pathUnweaken
  obtain ⟨_, intervalHEq⟩ :=
    Term.weakenInverse_atVarZero
      (context := context)
      (newType := Ty.interval)
      (weakenedTerm := intervalTerm)
  dsimp only [Term.eta_path_shape_construct]
  cases pathHEq
  cases intervalHEq
  rfl

end Term

end LeanFX2
