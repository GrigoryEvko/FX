import FX1Poly.Tier0.Context.ComprehensionCategory
import FX1Poly.Tier0.Term.Core.RawTermFreeVars

/-! # context-18 — global sections / flat: the points functor and the LOPS18 no-go

`context-18` internalizes the GLOBAL-SECTIONS modality at the context base.  In a presheaf model of type
theory the flat comonad `♭ = Disc ∘ Γ` arises from the adjunction `Disc ⊣ Γ` (discrete / constant ⊣
global-sections), and crisp / spatial type theory (Licata–Shulman, Shulman's real-cohesive HoTT) is what
makes `♭` usable.  Licata–Orton–Pitts–Spitters 2018 ("Internal Universes in Models of HoTT") shows the
universe CAN be internalized using `♭` plus the TININESS of the interval — resolving the classical
OBSTRUCTION (the "no-go") that a univalent universe is not a naive internal type.

## What is genuinely CONTEXT-SIDE (shipped here, zero-axiom)

The global-sections functor `Γ = Hom(−, 0)` is REPRESENTABLE at the INITIAL object (scope `0`, the empty
context, `context-5`/`context-6`).  Its value `Γ(scope) = Hom_fx(scope, 0) = SubstVec 0 scope` is the set
of CLOSED ENVIRONMENTS / global POINTS of the context (each of the `scope` variables sent to a CLOSED
term).  That, plus the CRISP / global substitutions (those sending every variable to a closed term) and the
LOPS18 NO-GO, are pure base-category facts:

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
  * **★ `not_isGlobalSubst_identity_succ` / `isGlobalSubst_identity_iff`** — THE LOPS18 NO-GO, context-side:
    the IDENTITY substitution on a NON-EMPTY context is NOT crisp (`id` sends `var 0` to the OPEN `var 0`),
    so `IsGlobalSubst (id scope) ↔ scope = 0`.  Hence the flat counit `♭X → X` is NOT invertible — global
    sections genuinely LOSE the open variables — and `♭` cannot be an ordinary (non-crisp) base operation.
    This is the machine-checked obstruction that MOTIVATES crisp / modal type theory.

## Deferred (honestly NOT context-side)

  * The flat comonad `♭A` on TYPES, and the sharp monad `#A`, are operations on the TYPE presheaf — `×type`
    (the type fibration over the base) → `fib-1` / the type axis.
  * `Disc : Set → 𝒞` is DEGENERATE at the base (`Disc` of a finite set is a coproduct of copies of the
    initial object `0`, which collapses to `0` by `context-3`), confirming `♭` lives on the TYPE / presheaf
    level, not the base — only `Γ` and the crisp maps are base-side.
  * Crisp / spatial type theory proper — crisp variables `x :: A`, the modal eliminator, crisp-`J` — is a
    MODE-axis object (`♭` is a modality) → `mode-axis` / `fib-3`.
  * The LOPS18 POSITIVE result (internalizing the universe via tininess + the amazing right adjoint `√`)
    needs transpension (`mode-11`) + `×type` → `TRANSP` / `fib`.

Zero external dependencies.  Raw Lean 4 + Init only.  No `funext` (the no-go is via `RawVarSet.contains`,
decidable membership; the empty-point subsingleton is via `SubstVec.ext` over the vacuous `Fin 0`).
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The global-sections (points) functor `Γ = Hom(−, 0)` -/

/-- **The global sections / points of a context** — `Γ(scope) = Hom_fx(scope, 0) = SubstVec 0 scope`: the
CLOSED ENVIRONMENTS of `scope` (each variable sent to a CLOSED term).  Representable at the INITIAL object
`0` (the empty context, `context-5`/`context-6`).  For a non-empty `scope` this is non-degenerate (the
tuples of closed terms); for `scope = 0` it is a single point. -/
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
variable.  These are the "constant" substitutions: the base shadow of crisp variables in spatial type
theory, and the maps that factor through the global-sections (closed) fragment. -/
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

/-! ## The LOPS18 no-go: the identity on a non-empty context is not crisp -/

/-- ★ **The LOPS18 no-go (context-side).**  The IDENTITY substitution on a NON-EMPTY context is NOT crisp:
its `0`-th entry is `var 0` (`identity_lookup`), an OPEN variable whose `freeVars` CONTAINS position `0`
(`freeVars_var_self_smoke`), contradicting crispness.  Interpretation: the flat counit `♭X → X` is not
invertible — passing to global sections genuinely DROPS the open variables — so the flat modality cannot be
internalized as an ordinary (non-crisp) base operation.  This is the obstruction that motivates crisp /
modal type theory. -/
theorem not_isGlobalSubst_identity_succ (scope : Nat) :
    ¬ IsGlobalSubst (SubstVec.identity (scope + 1)) := by
  intro isCrisp
  have notContainsZero :=
    isCrisp ⟨0, Nat.succ_pos scope⟩ ⟨0, Nat.succ_pos scope⟩
  rw [SubstVec.identity_lookup] at notContainsZero
  exact notContainsZero (RawTerm.freeVars_var_self_smoke ⟨0, Nat.succ_pos scope⟩)

/-- **The identity is crisp exactly on the empty context** — `IsGlobalSubst (id scope) ↔ scope = 0`.  The
sharp dividing line: only the empty context's identity is global; every non-empty context has an open
identity.  The flat counit is an isomorphism only at the empty context. -/
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

/-! ## The global-sections structure, assembled -/

/-- **The FX context base's global-sections / flat data**, gathered as one citable object: the points
functor `Γ = Hom(−, 0)` (functoriality), `Γ` of the empty context is a point, the crisp substitutions with
closed environments crisp, and ★ the LOPS18 no-go (the identity is crisp iff the context is empty).  The
flat comonad on TYPES, the sharp monad, crisp-`J`, and the internal universe are honest deferrals (see the
module docstring). -/
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
  /-- ★ The LOPS18 no-go: the identity is crisp iff the context is empty. -/
  identityCrispIffEmpty : ∀ (scope : Nat),
      IsGlobalSubst (SubstVec.identity scope) ↔ scope = 0

/-- ★ The FX context base HAS the global-sections / flat data — the witness wiring the points functor, the
empty-context point, the crisp-substitution facts, and the LOPS18 no-go. -/
def fxGlobalSections : FxGlobalSections where
  reindexId := fun point => globalSectionsReindex_id point
  reindexComp := fun firstSubst secondSubst point =>
    globalSectionsReindex_comp firstSubst secondSubst point
  emptyContextIsPoint := fun firstPoint secondPoint =>
    globalSections_empty_subsingleton firstPoint secondPoint
  globalPointsAreCrisp := fun substitution => isGlobalSubst_of_target_zero substitution
  identityCrispIffEmpty := fun scope => isGlobalSubst_identity_iff scope

/-- **Honesty marker.**  The flat comonad `♭A` on TYPES is NOT shipped at `context-18`: it is an operation
on the type presheaf (`×type → fib-1` / the type axis), and crisp-`J` / the modal eliminator is a MODE-axis
object.  `context-18` ships only the context-side global-sections functor + crisp maps + the LOPS18 no-go. -/
def fxGlobalSections_hasFlatTypeModality : Bool := false

/-! ## Smoke: a non-empty context has an open (non-crisp) identity -/

/-- Smoke: the identity on the one-variable context is NOT crisp (the canonical witness of the no-go). -/
theorem fxGlobalSections_open_identity_smoke :
    ¬ IsGlobalSubst (SubstVec.identity 1) :=
  not_isGlobalSubst_identity_succ 0

end FX1Poly.Tier0
