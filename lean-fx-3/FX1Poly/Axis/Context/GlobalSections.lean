import FX1Poly.Axis.Context.ComprehensionCategory
import FX1Poly.Axis.Term.Core.RawTermFreeVars

/-! # context-18 — global sections / flat: the points functor and the flat-modality no-go

`context-18` builds the GLOBAL-SECTIONS functor at the context base and proves the base-level OBSTRUCTION to
internalizing the flat modality.  In a presheaf model the flat comonad `♭ = Disc ∘ Γ` arises from `Disc ⊣ Γ`
(discrete / constant ⊣ global-sections); crisp / spatial type theory (Shulman's real-cohesive HoTT) is what
makes `♭` usable, and Licata–Orton–Pitts–Spitters 2018 USES `♭` plus the tininess of the interval to
internalize the universe.

What is genuinely CONTEXT-SIDE — and all this rung claims — is the global-sections FUNCTOR `Γ` plus the
ELEMENTARY no-go that makes `♭` a NON-TRIVIAL modality: not every substitution is global, so `Γ` loses
information and cannot be a no-op / cannot be internalized as an ordinary base operation.  This is the
obstruction that crisp type theory exists to handle (Shulman) and on which the LOPS18 universe construction
is later built — it is NOT itself LOPS18's universe-fibrancy no-go, which is `×type` (the universe + tininess,
deferred).

## What is genuinely CONTEXT-SIDE (shipped here, zero-axiom)

The global-sections functor `Γ = Hom_fx(−, 0)` is REPRESENTABLE at scope `0` — the INITIAL object of
`fxBaseSubstCategory` (`context-5`/`context-6`), equivalently the TERMINAL object of the substitution category
`𝒞 = fxBaseSubstCategory^op`.  So `Γ(scope) = Hom_fx(scope, 0) = Hom_𝒞(terminal, scope) = SubstVec 0 scope`
is the (non-empty) POINTS / closed-environment functor `Hom_𝒞(terminal, −)` — each of the `scope` variables
sent to a CLOSED term.  That, plus the CRISP / global substitutions (closed image) and the flat no-go, are
pure base-category facts:

  * **`globalSections` / `globalSectionsReindex` (+ `_id` / `_comp`)** — `Γ = Hom(−, 0)` as a representable
    presheaf on `fxBaseSubstCategory`: reindexing a global point along a substitution (precompose), with the
    two functor laws (`identity_compose`, `compose_assoc`).  VARIANCE (the lesson of `context-10`):
    `fxBaseSubstCategory = 𝒞^op`, so `Hom_fx(−, 0)` is the representable PRESHEAF on `fxBaseSubstCategory`,
    equivalently the COVARIANT points functor `Γ : 𝒞 → Set`.
  * **`globalSections_empty_subsingleton`** — `Γ(empty) ≅ 1`: the global sections of the empty context is a
    single point (the empty closed environment), exactly `Γ` of the terminal presheaf.
  * **`IsGlobalSubst`** — the CRISP / global substitutions: those sending EVERY variable to a CLOSED term
    (`freeVars` of every image is empty).  These are the "constant" maps — the base shadow of crisp
    variables.  Every closed environment (a map into `0`) is crisp (`isGlobalSubst_of_target_zero`).
  * **★ `not_isGlobalSubst_identity_succ` / `isGlobalSubst_identity_iff`** — THE FLAT NO-GO (`♭` is
    non-trivial), context-side: the IDENTITY substitution on a NON-EMPTY context is NOT crisp (`id` sends
    `var 0` to the OPEN `var 0`), so `IsGlobalSubst (id scope) ↔ scope = 0`.  Global sections are therefore a
    PROPER subclass — `Γ` genuinely loses the open variables — so `♭` cannot be a no-op / cannot be
    internalized as an ordinary (non-crisp) base operation.  (At the type level this is the non-invertibility
    of the counit `♭A → A`, `×type`.)  The machine-checked obstruction that MOTIVATES crisp / modal type
    theory; LOPS18's universe no-go is the `×type` application built on this discipline.
  * **★ `isDiscreteContext_iff_empty`** — the DISCRETE-context characterization: the ONLY context all of whose
    substitutions are crisp is the EMPTY one (`IsDiscreteContext scope ↔ scope = 0`).  At the bare base (no
    type information) the only context with no open-variable structure is the empty one — so the discrete
    fragment is degenerate here, confirming `♭ = Disc ∘ Γ` genuinely lives at the TYPE / presheaf level
    (where discreteness is a property of the TYPES, `×type`), not the base.

## Deferred (honestly NOT context-side)

  * The flat comonad `♭A` on TYPES, and the sharp monad `#A`, are operations on the TYPE presheaf — `×type`
    (the type fibration over the base) → `fib-1` / the type axis.  (`Disc` itself collapses to the empty
    context, `isDiscreteContext_iff_empty` — so `♭` genuinely lives on the type / presheaf level.)
  * Crisp / spatial type theory proper — crisp variables `x :: A`, the modal eliminator, crisp-`J` — is a
    MODE-axis object (`♭` is a modality) → `mode-axis` / `fib-3`.
  * The LOPS18 POSITIVE result (internalizing the universe via tininess + the amazing right adjoint `√`)
    needs transpension (`mode-11`) + `×type` → `TRANSP` / `fib`.

Zero external dependencies.  Raw Lean 4 + Init only.  No `funext` (the no-go is via `RawVarSet.contains`,
decidable membership; the empty-point subsingleton is via `SubstVec.ext` over the vacuous `Fin 0`).
-/

namespace FX1Poly.Axis

open FX1Poly.Core

/-! ## The global-sections (points) functor `Γ = Hom(−, 0)` -/

/-- **The global sections / points of a context** — `Γ(scope) = Hom_fx(scope, 0) = SubstVec 0 scope`: the
CLOSED ENVIRONMENTS of `scope` (each variable sent to a CLOSED term).  Representable at scope `0` — the
INITIAL object of `fxBaseSubstCategory` (`context-5`/`context-6`), equivalently the TERMINAL object of
`𝒞 = fxBaseSubstCategory^op` — so this is the points functor `Hom_𝒞(terminal, −)` (non-empty: closed-term
tuples for non-empty `scope`; a single point for `scope = 0`). -/
@[reducible] def globalSections (scope : Nat) : Type := SubstVec 0 scope

/-- **Reindexing a global point** — `Γ` is a presheaf on `fxBaseSubstCategory`: a substitution
`f : a ⟶ b` pulls a global point of `b` back to a global point of `a` by precomposition.  (Contravariant on
`fxBaseSubstCategory = 𝒞^op`, i.e. the covariant points functor on `𝒞`.) -/
def globalSectionsReindex {sourceScope targetScope : Nat}
    (substitution : SubstVec targetScope sourceScope) (point : globalSections targetScope) :
    globalSections sourceScope :=
  substitution.compose point

/-- `Γ` preserves identities: reindexing along the identity is the identity. -/
theorem globalSectionsReindex_id {scope : Nat} (point : globalSections scope) :
    globalSectionsReindex (SubstVec.identity scope) point = point :=
  SubstVec.identity_compose point

/-- `Γ` preserves composition (presheaf functoriality): reindexing along a composite is the composite of
reindexings. -/
theorem globalSectionsReindex_comp {scopeA scopeB scopeC : Nat}
    (firstSubst : SubstVec scopeB scopeA) (secondSubst : SubstVec scopeC scopeB)
    (point : globalSections scopeC) :
    globalSectionsReindex (firstSubst.compose secondSubst) point
      = globalSectionsReindex firstSubst (globalSectionsReindex secondSubst point) :=
  SubstVec.compose_assoc firstSubst secondSubst point

/-- **`Γ` of the empty context is a point** — `Γ(0) ≅ 1`.  The global sections of the empty context is the
unique empty closed environment (any two agree on the vacuous `Fin 0` of variables).  This is `Γ` applied to
the terminal presheaf. -/
theorem globalSections_empty_subsingleton (firstPoint secondPoint : globalSections 0) :
    firstPoint = secondPoint :=
  SubstVec.ext firstPoint secondPoint (fun index => absurd index.isLt (Nat.not_lt_zero index.val))

/-! ## The crisp / global substitutions (the constant maps) -/

/-- **A crisp / global substitution** sends EVERY variable to a CLOSED term — no image term has any free
variable (the closed-image characterization).  These are the "constant" substitutions, the base shadow of
crisp variables in spatial type theory.  (Equivalence with "factors through the initial object `0`" needs the
closed-terms-are-`RawTerm 0`-images bijection, not shipped; closed-image is taken as primitive here.) -/
def IsGlobalSubst {targetScope sourceScope : Nat} (substitution : SubstVec targetScope sourceScope) : Prop :=
  ∀ (index : Fin sourceScope) (position : Fin targetScope),
    ¬ RawVarSet.contains (RawTerm.freeVars (substitution.lookup index)) position

/-- **Every closed environment is crisp.**  A substitution into the empty context (`SubstVec 0 source`, a
global point) is vacuously global — there are no positions (`Fin 0`) for an image term to depend on.  So the
global POINTS are exactly the crisp maps into `0`. -/
theorem isGlobalSubst_of_target_zero {sourceScope : Nat} (substitution : SubstVec 0 sourceScope) :
    IsGlobalSubst substitution :=
  fun _index position _contains => absurd position.isLt (Nat.not_lt_zero position.val)

/-- The identity on the empty context is crisp (vacuously — no variables). -/
theorem isGlobalSubst_identity_zero : IsGlobalSubst (SubstVec.identity 0) :=
  isGlobalSubst_of_target_zero (SubstVec.identity 0)

/-! ## The flat no-go: the identity on a non-empty context is not crisp (♭ is non-trivial) -/

/-- ★ **The flat no-go (context-side): `♭` is non-trivial.**  The IDENTITY substitution on a NON-EMPTY
context is NOT crisp: its `0`-th entry is `var 0` (`identity_lookup`), an OPEN variable whose `freeVars`
CONTAINS position `0` (`freeVars_var_self_smoke`), contradicting crispness.  So the global / crisp maps are a
PROPER subclass — `Γ` drops the open variables.  Interpretation (the `×type` payoff): the counit `♭A → A` is
not invertible, so `♭` cannot be a no-op / cannot be internalized as an ordinary (non-crisp) base operation —
the obstruction that motivates crisp / modal type theory (and underlies the LOPS18 universe construction). -/
theorem not_isGlobalSubst_identity_succ (scope : Nat) :
    ¬ IsGlobalSubst (SubstVec.identity (scope + 1)) := by
  intro isCrisp
  have notContainsZero :=
    isCrisp ⟨0, Nat.succ_pos scope⟩ ⟨0, Nat.succ_pos scope⟩
  rw [SubstVec.identity_lookup] at notContainsZero
  exact notContainsZero (RawTerm.freeVars_var_self_smoke ⟨0, Nat.succ_pos scope⟩)

/-- **The identity is crisp exactly on the empty context** — `IsGlobalSubst (id scope) ↔ scope = 0`.  The
sharp dividing line: only the empty context's identity is global; every non-empty context has an open
identity, so global sections collapse to a no-op only there. -/
theorem isGlobalSubst_identity_iff (scope : Nat) :
    IsGlobalSubst (SubstVec.identity scope) ↔ scope = 0 := by
  constructor
  · intro isCrisp
    cases scope with
    | zero => rfl
    | succ predecessor => exact absurd isCrisp (not_isGlobalSubst_identity_succ predecessor)
  · intro scopeIsZero
    subst scopeIsZero
    exact isGlobalSubst_identity_zero

/-! ## Discrete contexts: only the empty context is purely global (Disc degenerates) -/

/-- **A discrete / constant context** is one all of whose substitutions are crisp — every map INTO it sends
every variable to a CLOSED term.  The base shadow of discreteness: a context with no open-variable structure
(at the bare base only the empty context; genuine discreteness is a property of the TYPES, `×type`). -/
def IsDiscreteContext (scope : Nat) : Prop :=
  ∀ {sourceScope : Nat} (substitution : SubstVec scope sourceScope), IsGlobalSubst substitution

/-- The empty context is discrete (vacuously — every map into it lands in `Fin 0`, no free positions). -/
theorem isDiscreteContext_zero : IsDiscreteContext 0 :=
  fun substitution => isGlobalSubst_of_target_zero substitution

/-- A non-empty context is NOT discrete — its own identity is a non-crisp map into it. -/
theorem not_isDiscreteContext_succ (scope : Nat) :
    ¬ IsDiscreteContext (scope + 1) := by
  intro isDiscrete
  exact not_isGlobalSubst_identity_succ scope (isDiscrete (SubstVec.identity (scope + 1)))

/-- ★ **Only the empty context is discrete** — `IsDiscreteContext scope ↔ scope = 0`.  At the bare base there
is no non-trivial purely-global context (every non-empty scope has an open identity).  So the discrete
fragment is degenerate HERE — genuine discreteness is a property of the TYPES (`×type`) — confirming
`♭ = Disc ∘ Γ` lives at the type / presheaf level, not the base. -/
theorem isDiscreteContext_iff_empty (scope : Nat) :
    IsDiscreteContext scope ↔ scope = 0 := by
  constructor
  · intro isDiscrete
    cases scope with
    | zero => rfl
    | succ predecessor => exact (not_isDiscreteContext_succ predecessor isDiscrete).elim
  · intro scopeIsZero
    subst scopeIsZero
    exact isDiscreteContext_zero

/-! ## The global-sections structure, assembled -/

/-- **The FX context base's global-sections / flat data**, gathered as one citable object: the points
functor `Γ = Hom(−, 0)` (functoriality), `Γ` of the empty context is a point, the crisp substitutions with
closed environments crisp, and ★ the flat no-go (the identity is crisp iff the context is empty — `♭` is
non-trivial).  The flat comonad on TYPES, the sharp monad, crisp-`J`, and the internal universe are honest
deferrals (see the module docstring). -/
structure FxGlobalSections where
  /-- `Γ` preserves identities. -/
  reindexId : ∀ {scope : Nat} (point : globalSections scope),
      globalSectionsReindex (SubstVec.identity scope) point = point
  /-- `Γ` preserves composition (presheaf functoriality). -/
  reindexComp : ∀ {scopeA scopeB scopeC : Nat} (firstSubst : SubstVec scopeB scopeA)
      (secondSubst : SubstVec scopeC scopeB) (point : globalSections scopeC),
      globalSectionsReindex (firstSubst.compose secondSubst) point
        = globalSectionsReindex firstSubst (globalSectionsReindex secondSubst point)
  /-- `Γ` of the empty context is a point. -/
  emptyContextIsPoint : ∀ (firstPoint secondPoint : globalSections 0), firstPoint = secondPoint
  /-- Every closed environment (global point) is crisp. -/
  globalPointsAreCrisp : ∀ {sourceScope : Nat} (substitution : SubstVec 0 sourceScope),
      IsGlobalSubst substitution
  /-- ★ The flat no-go (`♭` non-trivial): the identity is crisp iff the context is empty. -/
  identityCrispIffEmpty : ∀ (scope : Nat),
      IsGlobalSubst (SubstVec.identity scope) ↔ scope = 0
  /-- ★ Only the empty context is discrete — `Disc` collapses, so `♭` is genuinely type-level. -/
  discreteIffEmpty : ∀ (scope : Nat), IsDiscreteContext scope ↔ scope = 0

/-- ★ The FX context base HAS the global-sections / flat data — the witness wiring the points functor, the
empty-context point, the crisp-substitution facts, the flat no-go (`♭` non-trivial), and the
discrete-context characterization (`Disc` collapses). -/
def fxGlobalSections : FxGlobalSections where
  reindexId := fun point => globalSectionsReindex_id point
  reindexComp := fun firstSubst secondSubst point =>
    globalSectionsReindex_comp firstSubst secondSubst point
  emptyContextIsPoint := fun firstPoint secondPoint =>
    globalSections_empty_subsingleton firstPoint secondPoint
  globalPointsAreCrisp := fun substitution => isGlobalSubst_of_target_zero substitution
  identityCrispIffEmpty := fun scope => isGlobalSubst_identity_iff scope
  discreteIffEmpty := fun scope => isDiscreteContext_iff_empty scope

/-- **Honesty marker.**  The flat comonad `♭A` on TYPES is NOT shipped at `context-18`: it is an operation
on the type presheaf (`×type → fib-1` / the type axis), and crisp-`J` / the modal eliminator is a MODE-axis
object.  `context-18` ships only the context-side global-sections functor + crisp maps + the flat no-go. -/
def fxGlobalSections_hasFlatTypeModality : Bool := false

/-! ## Smoke: a non-empty context has an open (non-crisp) identity -/

/-- Smoke: the identity on the one-variable context is NOT crisp (the canonical witness of the no-go). -/
theorem fxGlobalSections_open_identity_smoke :
    ¬ IsGlobalSubst (SubstVec.identity 1) :=
  not_isGlobalSubst_identity_succ 0

end FX1Poly.Axis
