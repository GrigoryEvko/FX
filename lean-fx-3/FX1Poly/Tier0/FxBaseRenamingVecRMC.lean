import FX1Poly.Tier0.FxBaseRenamingVecTryTabulate
import FX1Poly.Tier0.FxBaseRenamingVecPreimage
import FX1Poly.Tier0.FxBaseRenamingVecIsomorphism

/-! # FX1Poly/Tier0/FxBaseRenamingVecRMC
    — ★ the complete `RepresentableMapCategory` over the extensional renaming base

This file CLOSES the `fxBaseRMC` track (SN-084 / SN-085 / SN-085a, #210): it assembles
`fxBaseRenamingVecRMC : RepresentableMapCategory` — the first GENUINE (non-degenerate, data-morphism, extensional)
representable map category for FX, the substrate the entire Tier-0 CwR / sconing ladder plugs into.

The representable-map class is the categorical ISOMORPHISMS of `fxBaseRenamingVecCategory` (the right class: their
pullbacks exist generically via `IsIsomorphism.pullbackAlong`).  The only missing piece was `memberDecidable` —
deciding whether a `RenamingVec` is a finite bijection.  This file supplies the decider, PIGEONHOLE-FREE:

  * `tryInverse forward := tryTabulate (findPreimage forward)` — the candidate inverse: `tabulate` of the partial
    preimage function, `some backward` exactly when `forward` is surjective.
  * `tryInverse_rightInverse` (+ `_composed`) — the candidate is a RIGHT inverse by construction (`findPreimage`
    soundness + `tryTabulate` soundness): `∀ j, forward.lookup (backward.lookup j) = j`.
  * `tryInverse_none_notSurjective` — failure exhibits an unhit target index (`tryTabulate` + `findPreimage`
    completeness).
  * `isIsomorphism_inverse_rightInverse` — extracts the pointwise right-inverse from any `IsIsomorphism` witness
    (its `leftInverse`, bridged through `_compose_eq` / `_identity_eq` + `lookup_compose` + `identity_lookup`).
  * `tryInverse_unique` — INVERSE UNIQUENESS by pure function-algebra: `backward = backward ∘ id = backward ∘
    (forward ∘ g) = (backward ∘ forward) ∘ g = id ∘ g = g` (using the right-inverse-by-construction + the witness's
    two-sided laws + the category laws).  NO cardinality / pigeonhole.
  * `decideIsCategoricalIsomorphism` — the decider: `tryInverse = none ⟹ isFalse` (a hypothetical iso's inverse
    supplies a preimage of the unhit index, contradiction); `tryInverse = some backward ⟹` decide the LEFT inverse
    via `decEq (forward.compose backward) (identity source)` — `isTrue ⟹` `isomorphismOfLookupInverse`; `isFalse ⟹
    isFalse` by inverse-uniqueness (`backward = g ⟹ forward.compose backward = forward.compose g = id`).
  * `fxBaseRenamingVecRepresentableMaps` — the `MorphismClass` (member = `IsCategoricalIsomorphism`,
    memberDecidable = the decider).
  * `fxBaseRenamingVecRMC` — the assembled `RepresentableMapCategory`: the three CwR axioms wire directly to the
    shipped `isCategoricalIsomorphism_{pullback,identity,compose}` content lemmas.

## Zero-axiom verification

The decider rests entirely on the shipped zero-axiom substrate (`tabulate` / `tryTabulate` / `findPreimage` and
their soundness/completeness, `decEq`, `isomorphismOfLookupInverse`, the iso-class CwR-axiom content).  The new
proofs are category-law algebra (`compose_assoc` / `identity_compose` / `compose_identity` + the `_compose_eq` /
`_identity_eq` defeq bridges + `lookup_compose` / `identity_lookup`), `congrArg` (type-ascribed to force beta),
and `Option`/structural reasoning.  No `funext`, no `Fin.cases`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- The candidate inverse: `tabulate` of the (partial) preimage function.  `some backward` iff `forward` is
surjective. -/
def RenamingVec.tryInverse {target source : Nat} (forward : RenamingVec target source) :
    Option (RenamingVec source target) :=
  RenamingVec.tryTabulate (fun targetIndex => RenamingVec.findPreimage forward targetIndex)

/-- When the candidate exists, it is a right-inverse section (pointwise): `forward ∘ backward = id` on targets. -/
theorem RenamingVec.tryInverse_rightInverse {target source : Nat}
    (forward : RenamingVec target source) (backward : RenamingVec source target)
    (hInv : RenamingVec.tryInverse forward = some backward) :
    ∀ (targetIndex : Fin target), forward.lookup (backward.lookup targetIndex) = targetIndex := by
  intro targetIndex
  have key := RenamingVec.tryTabulate_lookup
    (fun targetIndex => RenamingVec.findPreimage forward targetIndex) backward hInv targetIndex
  exact RenamingVec.findPreimage_some forward targetIndex (backward.lookup targetIndex) key

/-- The composed-equality form of the right inverse (via `ext`): `backward.compose forward = identity target`. -/
theorem RenamingVec.tryInverse_rightInverse_composed {target source : Nat}
    (forward : RenamingVec target source) (backward : RenamingVec source target)
    (hInv : RenamingVec.tryInverse forward = some backward) :
    backward.compose forward = RenamingVec.identity target :=
  RenamingVec.ext _ _ (fun targetIndex => by
    rw [lookup_compose, RenamingVec.tryInverse_rightInverse forward backward hInv, identity_lookup])

/-- When the candidate fails, `forward` is not surjective: some target index is unhit. -/
theorem RenamingVec.tryInverse_none_notSurjective {target source : Nat}
    (forward : RenamingVec target source) (hNone : RenamingVec.tryInverse forward = none) :
    ∃ (targetIndex : Fin target), ∀ (sourceIndex : Fin source), forward.lookup sourceIndex ≠ targetIndex := by
  have ⟨targetIndex, hUnhit⟩ := RenamingVec.tryTabulate_none
    (fun targetIndex => RenamingVec.findPreimage forward targetIndex) hNone
  exact ⟨targetIndex, RenamingVec.findPreimage_none forward targetIndex hUnhit⟩

/-- A categorical isomorphism's inverse is a right inverse of `forward` (pointwise), extracted from
`witness.leftInverse`. -/
theorem RenamingVec.isIsomorphism_inverse_rightInverse {target source : Nat}
    {forward : RenamingVec target source}
    (witness : IsIsomorphism fxBaseRenamingVecCategory forward) :
    ∀ (targetIndex : Fin target), forward.lookup (witness.inverse.lookup targetIndex) = targetIndex := by
  intro targetIndex
  have pointwise : (fxBaseRenamingVecCategory.compose witness.inverse forward).lookup targetIndex
      = (fxBaseRenamingVecCategory.identity target).lookup targetIndex :=
    congrArg (fun morphism => RenamingVec.lookup morphism targetIndex) witness.leftInverse
  rw [fxBaseRenamingVecCategory_compose_eq, fxBaseRenamingVecCategory_identity_eq,
    lookup_compose, identity_lookup] at pointwise
  exact pointwise

/-- **Inverse uniqueness** — the candidate inverse equals any categorical iso's inverse, by pure function-algebra
(no cardinality): `backward = backward ∘ id = backward ∘ (forward ∘ g) = (backward ∘ forward) ∘ g = id ∘ g = g`. -/
theorem RenamingVec.tryInverse_unique {target source : Nat}
    {forward : RenamingVec target source} (backward : RenamingVec source target)
    (hInv : RenamingVec.tryInverse forward = some backward)
    (witness : IsIsomorphism fxBaseRenamingVecCategory forward) :
    backward = witness.inverse := by
  have rightInv : forward.compose witness.inverse = RenamingVec.identity source := by
    have key : fxBaseRenamingVecCategory.compose forward witness.inverse
        = fxBaseRenamingVecCategory.identity source := witness.rightInverse
    rw [fxBaseRenamingVecCategory_compose_eq, fxBaseRenamingVecCategory_identity_eq] at key
    exact key
  have leftInv : backward.compose forward = RenamingVec.identity target :=
    RenamingVec.tryInverse_rightInverse_composed forward backward hInv
  calc backward
      = backward.compose (RenamingVec.identity source) := (RenamingVec.compose_identity backward).symm
    _ = backward.compose (forward.compose witness.inverse) := by rw [← rightInv]
    _ = (backward.compose forward).compose witness.inverse :=
        (RenamingVec.compose_assoc backward forward witness.inverse).symm
    _ = (RenamingVec.identity target).compose witness.inverse := by rw [leftInv]
    _ = witness.inverse := RenamingVec.identity_compose witness.inverse

/-- **THE finite-bijectivity decider** — a renaming is a categorical isomorphism iff its preimage-tabulated
candidate is a two-sided inverse.  Pigeonhole-free: the right inverse is by construction, the left inverse is
decided by `decEq`, and the `isFalse` branch uses inverse uniqueness. -/
def RenamingVec.decideIsCategoricalIsomorphism {target source : Nat}
    (forward : RenamingVec target source) :
    Decidable (RenamingVec.IsCategoricalIsomorphism forward) :=
  match hInv : RenamingVec.tryInverse forward with
  | none =>
      isFalse (fun ⟨witness⟩ => by
        have ⟨targetIndex, hUnhit⟩ := RenamingVec.tryInverse_none_notSurjective forward hInv
        exact hUnhit (witness.inverse.lookup targetIndex)
          (RenamingVec.isIsomorphism_inverse_rightInverse witness targetIndex))
  | some backward =>
      match RenamingVec.decEq (forward.compose backward) (RenamingVec.identity source) with
      | isTrue leftInvEq =>
          isTrue ⟨RenamingVec.isomorphismOfLookupInverse forward backward
            (fun sourceIndex => by
              have key : (forward.compose backward).lookup sourceIndex
                  = (RenamingVec.identity source).lookup sourceIndex :=
                congrArg (fun morphism => RenamingVec.lookup morphism sourceIndex) leftInvEq
              rw [lookup_compose, identity_lookup] at key
              exact key)
            (RenamingVec.tryInverse_rightInverse forward backward hInv)⟩
      | isFalse leftInvNeq =>
          isFalse (fun ⟨witness⟩ =>
            leftInvNeq (by
              rw [RenamingVec.tryInverse_unique backward hInv witness]
              have key : fxBaseRenamingVecCategory.compose forward witness.inverse
                  = fxBaseRenamingVecCategory.identity source := witness.rightInverse
              rw [fxBaseRenamingVecCategory_compose_eq, fxBaseRenamingVecCategory_identity_eq] at key
              exact key))

/-- The representable-map class: the categorical isomorphisms, decidable by the finite-bijectivity decider. -/
def fxBaseRenamingVecRepresentableMaps : MorphismClass fxBaseRenamingVecCategory where
  member := fun morphism => RenamingVec.IsCategoricalIsomorphism morphism
  memberDecidable := fun morphism => RenamingVec.decideIsCategoricalIsomorphism morphism

/-- **★ The complete `RepresentableMapCategory` over the extensional renaming base.**  Objects are scopes,
morphisms are `RenamingVec` renamings, representable maps are the categorical isomorphisms (decidable via the
finite-bijectivity decider).  The three CwR axioms wire to the shipped iso-class content lemmas
(`isCategoricalIsomorphism_{pullback,identity,compose}`).  The first genuine — non-degenerate, data-morphism,
extensional — CwR for FX; the substrate the Tier-0 sconing ladder plugs into. -/
def fxBaseRenamingVecRMC : RepresentableMapCategory.{0, 0} where
  underlying := fxBaseRenamingVecCategory
  representableMaps := fxBaseRenamingVecRepresentableMaps
  closedUnderPullback := fun morphismF morphismG memberF =>
    RenamingVec.isCategoricalIsomorphism_pullback morphismF morphismG memberF
  isomorphismsRepresentable := fun _morphism iso => ⟨iso⟩
  closedUnderComposition := fun morphismF morphismG memberF memberG =>
    RenamingVec.isCategoricalIsomorphism_compose morphismF morphismG memberF memberG

end FX1Poly.Tier0
