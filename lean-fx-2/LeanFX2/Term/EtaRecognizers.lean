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
  unfold Term.eta_lam_shape_construct
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
  unfold Term.eta_lamPi_shape_body_construct
  cases functionHEq
  cases argumentHEq
  exact HEq.rfl

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
  unfold Term.eta_path_shape_construct
  cases pathHEq
  cases intervalHEq
  rfl

end Term

end LeanFX2
