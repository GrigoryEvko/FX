import FX1Poly.Tier0.Context.ComprehensionSigma
import FX1Poly.Tier0.Context.RenamingInclusion
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstWeakening
import FX1Poly.Tier0.Context.Instances.Renaming.FxBaseRenamingVecCategory

/-! # The earned CwF comprehension laws (`context-1`, the full LEFT/Σ leg)

`ComprehensionSigma.lean` gathered the comprehension v/p-laws + universal property + the
Beck–Chevalley substitution-stability square.  This file earns the rest of the genuine
CwF comprehension theory that the prose ("subcategory", "comprehension", "Σ") reaches for —
all PROVED, all pure Tier-0 (`RawTerm` / `RenamingVec` / `SubstVec` live in `Tier0`; nothing
outside the axis is imported).

## What lands here (all zero-axiom)

### Faithfulness — earning the `⊂`
  * `RenamingVec.toSubstVec_injective` — distinct renamings include to distinct substitutions
    (the variable cells differ, by the inductive's own `injection`).
  * `RawFunctor.IsFaithful` + `renamingInclusion_faithful` — the inclusion is a FAITHFUL
    functor, so "renaming ⊂ substitution" is a genuine subcategory embedding, not merely a
    functor.

### Comprehension η / surjective pairing
  * `SubstVec.identity_succ_eq_cons` — `id_{n+1} = ⟨q, p⟩`, i.e. the identity on an extended
    context is the pairing of the zeroth variable with the display map.  The fourth CwF
    comprehension law (the η/surjective-pairing law), absent from `ComprehensionSigma`.

### The lift functor + display-map naturality (Beck–Chevalley for the display map)
  * `SubstVec.lift` — the de Bruijn lift `σ⁺ = ⟨q, σ ∘ p⟩` of a substitution under a binder.
  * `SubstVec.weakening_compose_lift` — `p ∘ σ⁺ = σ ∘ p`, the display map's naturality square
    (the genuine Beck–Chevalley square for the display projection, distinct from the
    comprehension-stability `cons_compose`).

### Comprehension as a genuine bijection (the representability iso χ)
  * `SubstVec.comprehensionForward` / `comprehensionBackward` — the maps of the χ iso, the
    forward map built from the CATEGORICAL projections (display map + zeroth variable), NOT
    from the definitional pair.
  * `SubstVec.comprehensionIso : Bijection (SubstVec target (source+1)) (RawTerm target ×
    SubstVec target source)` — both round-trips PROVED (one is the universal property, the
    other is the v/p-laws).  This upgrades "uniqueness" (`cons_unique`) to a full bijection.

### The inclusion preserves the display structure (it is a CwF/display morphism)
  * `RenamingVec.weakening_toSubstVec` — the inclusion sends the renaming display map to the
    substitution display map.  With identity-preservation (`toSubstVec_identity`) and
    functoriality (`toSubstVec_compose`), the renaming RMC includes into the substitution
    category as a faithful, display-preserving functor.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0
open FX1Poly.Polygraph

open FX1Poly.Core FX1Poly.Tier0.Syntax

universe u

/-- The variable cell at an index — the term `var i`. -/
@[reducible] def SubstVec.varCell {scope : Nat} (index : Fin scope) : RawTerm scope :=
  RawTerm.mkGen .gen_var index .childNil

/-! ## Faithfulness — earning the `⊂` -/

/-- **The renaming inclusion is injective on morphisms.**  Two renamings whose variable-term
inclusions agree are equal: at each index the variable cells `var (r₁.lookup i)` and
`var (r₂.lookup i)` agree, so by the `RawTerm` constructor's injectivity the indices agree,
and `ext` finishes.  This is the FAITHFULNESS that makes "renaming ⊂ substitution" a genuine
subcategory embedding rather than just a functor. -/
theorem RenamingVec.toSubstVec_injective {target source : Nat}
    (firstRenaming secondRenaming : RenamingVec target source)
    (inclusionsAgree : firstRenaming.toSubstVec = secondRenaming.toSubstVec) :
    firstRenaming = secondRenaming :=
  RenamingVec.ext firstRenaming secondRenaming (fun index => by
    have cellsAgree :
        RawTerm.mkGen .gen_var (firstRenaming.lookup index) .childNil
          = RawTerm.mkGen .gen_var (secondRenaming.lookup index) .childNil := by
      rw [← RenamingVec.toSubstVec_lookup, ← RenamingVec.toSubstVec_lookup, inclusionsAgree]
    -- the variable cells agree, so by the `RawTerm` constructor's injectivity the indices agree
    injection cellsAgree)

/-- A functor is FAITHFUL when its morphism map is injective. -/
def _root_.FX1Poly.Polygraph.RawFunctor.IsFaithful {sourceCategory targetCategory : RawCategory.{u, u}}
    (functor : RawFunctor sourceCategory targetCategory) : Prop :=
  ∀ {objectA objectB : sourceCategory.Object}
    (morphismF morphismG : sourceCategory.Morphism objectA objectB),
    functor.mapMorphism morphismF = functor.mapMorphism morphismG → morphismF = morphismG

/-- ★ **The renaming ⊂ substitution inclusion is faithful.**  Its morphism map is
`toSubstVec`, injective by `toSubstVec_injective`.  This earns the subcategory claim: the
renaming RMC is a genuine subcategory of the substitution category, not merely the image of a
functor. -/
theorem renamingInclusion_faithful : RawFunctor.IsFaithful renamingInclusion :=
  fun firstRenaming secondRenaming inclusionsAgree =>
    RenamingVec.toSubstVec_injective firstRenaming secondRenaming inclusionsAgree

/-! ## Comprehension η / surjective pairing -/

/-- **The comprehension η-law (surjective pairing).**  The identity substitution on an
extended context is the pairing of the zeroth variable (the `q`-projection) with the display
map (the `p`-projection): `id_{Γ.A} = ⟨q, p⟩`.  The fourth CwF comprehension law — together
with `cons` (existence), the v/p-laws (`ComprehensionSigma`), and the universal property, it
completes the comprehension structure. -/
theorem SubstVec.identity_succ_eq_cons (scope : Nat) :
    SubstVec.identity (scope + 1) =
      SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos scope⟩) (SubstVec.weakening scope) :=
  SubstVec.ext _ _ (fun index =>
    match index with
    | ⟨0, _⟩ => by
        rw [SubstVec.identity_lookup, SubstVec.cons_lookup_zero]
    | ⟨_position + 1, _isLt⟩ => by
        rw [SubstVec.identity_lookup, SubstVec.cons_lookup_succ, SubstVec.weakening_lookup]
        exact congrArg (RawTerm.mkGen Generator.gen_var · RawTermChildren.childNil) (Fin.ext rfl))

/-! ## The lift functor + display-map naturality -/

/-- **The de Bruijn lift of a substitution under a binder** — `σ⁺ = ⟨q, σ ∘ p⟩`.  Sends the
freshly-bound variable 0 to itself and weakens `σ`'s images past it.  The action of
context-extension on morphisms (the comprehension functor's morphism part). -/
def SubstVec.lift {sourceScope targetScope : Nat} (sigma : SubstVec targetScope sourceScope) :
    SubstVec (targetScope + 1) (sourceScope + 1) :=
  SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos targetScope⟩)
    (sigma.compose (SubstVec.weakening targetScope))

/-- **Display-map naturality (Beck–Chevalley for the display map).**  The display map `p` is
natural in the context: weakening then lifting equals substituting then weakening,
`p ∘ σ⁺ = σ ∘ p`.  This is the genuine naturality square of the display projection — distinct
from the comprehension-stability square `cons_compose` (which is naturality of the *extension*
`⟨σ,t⟩`).  It holds by the p-law: the display map cancels the lift's variable-0 head. -/
theorem SubstVec.weakening_compose_lift {sourceScope targetScope : Nat}
    (sigma : SubstVec targetScope sourceScope) :
    (SubstVec.weakening sourceScope).compose sigma.lift =
      sigma.compose (SubstVec.weakening targetScope) :=
  SubstVec.weakening_compose_cons (SubstVec.varCell ⟨0, Nat.succ_pos targetScope⟩)
    (sigma.compose (SubstVec.weakening targetScope))

/-! ## Comprehension as a genuine bijection (the representability iso χ) -/

/-- A two-sided inverse pair — a bijection. -/
structure Bijection (carrierLeft carrierRight : Type) where
  /-- The forward map. -/
  forward : carrierLeft → carrierRight
  /-- The backward map. -/
  backward : carrierRight → carrierLeft
  /-- `backward ∘ forward = id`. -/
  backward_forward : ∀ leftValue, backward (forward leftValue) = leftValue
  /-- `forward ∘ backward = id`. -/
  forward_backward : ∀ rightValue, forward (backward rightValue) = rightValue

/-- The forward map of the comprehension iso, built from the CATEGORICAL projections: the
zeroth-variable lookup (the `q`-projection) paired with the display-map composite (the
`p`-projection).  NOT the definitional `(·.1, ·.2)` — it goes through `weakening` and `lookup`. -/
def SubstVec.comprehensionForward {target source : Nat}
    (vec : SubstVec target (source + 1)) : RawTerm target × SubstVec target source :=
  (vec.lookup ⟨0, Nat.succ_pos source⟩, (SubstVec.weakening source).compose vec)

/-- The backward map of the comprehension iso — the extension `cons`. -/
def SubstVec.comprehensionBackward {target source : Nat}
    (pair : RawTerm target × SubstVec target source) : SubstVec target (source + 1) :=
  SubstVec.cons pair.1 pair.2

/-- `backward ∘ forward = id` — this IS the comprehension universal property: the projections
of any morphism recover it via `cons`. -/
theorem SubstVec.comprehensionBackward_forward {target source : Nat}
    (vec : SubstVec target (source + 1)) :
    SubstVec.comprehensionBackward (SubstVec.comprehensionForward vec) = vec :=
  (SubstVec.cons_unique (vec.lookup ⟨0, Nat.succ_pos source⟩)
    ((SubstVec.weakening source).compose vec) vec rfl rfl).symm

/-- `forward ∘ backward = id` — the v-law (zeroth lookup recovers the head) and the p-law
(display projects to the tail) say the projections of an extension are the original pair. -/
theorem SubstVec.comprehensionForward_backward {target source : Nat}
    (pair : RawTerm target × SubstVec target source) :
    SubstVec.comprehensionForward (SubstVec.comprehensionBackward pair) = pair := by
  show ((SubstVec.cons pair.1 pair.2).lookup ⟨0, Nat.succ_pos source⟩,
        (SubstVec.weakening source).compose (SubstVec.cons pair.1 pair.2)) = pair
  rw [SubstVec.cons_lookup_zero, SubstVec.weakening_compose_cons]

/-- ★ **The comprehension representability bijection** — `Sub(Δ, Γ.A) ≅ Sub(Δ, Γ) × Tm(Δ, A)`
in its untyped (scope-level) form.  Both round-trips are proved (the universal property one
way, the v/p-laws the other).  This upgrades the `cons_unique` uniqueness statement to a full
bijection: comprehension is a genuine representing object, not merely unique. -/
def SubstVec.comprehensionIso {target source : Nat} :
    Bijection (SubstVec target (source + 1)) (RawTerm target × SubstVec target source) where
  forward := SubstVec.comprehensionForward
  backward := SubstVec.comprehensionBackward
  backward_forward := SubstVec.comprehensionBackward_forward
  forward_backward := SubstVec.comprehensionForward_backward

/-! ## The inclusion preserves the display structure -/

/-- ★ **The inclusion preserves the display map.**  The renaming display map `weakening`,
included into substitutions, IS the substitution display map: both send variable `i` to
`var (i+1)` (the renaming via `shiftImage`, the substitution via `Fin.succ`, defeq).  With
identity-preservation (`toSubstVec_identity`) and functoriality (`toSubstVec_compose`), the
renaming RMC includes into the substitution category as a faithful, DISPLAY-PRESERVING
functor — a morphism of comprehension structures. -/
theorem RenamingVec.weakening_toSubstVec (scope : Nat) :
    (RenamingVec.weakening scope).toSubstVec = SubstVec.weakening scope :=
  SubstVec.ext _ _ (fun index => by
    rw [RenamingVec.toSubstVec_lookup, RenamingVec.weakening_lookup, SubstVec.weakening_lookup]
    exact congrArg (RawTerm.mkGen Generator.gen_var · RawTermChildren.childNil) (Fin.ext rfl))

end FX1Poly.Tier0
