import FX1Poly.Tier0.FxBaseRenamingVecCategory
import FX1Poly.Tier0.IsomorphismCategorical

/-! # FX1Poly/Tier0/FxBaseRenamingVecIsomorphism
    — the categorical isomorphisms of the extensional renaming base: the iso-class CwR-axiom CONTENT

`FxBaseRenamingVecCategory.lean` built `fxBaseRenamingVecCategory`, the EXTENSIONAL data-morphism renaming
`RawCategory` (with `RenamingVec.ext` / `_faithful`).  `IsomorphismCategorical.lean` proved the three generic,
base-independent CwR facts for the isomorphism class of ANY `RawCategory` (`IsIsomorphism.identity` / `.comp` /
`.pullbackAlong`).  This file is the bridge: it builds the CONCRETE categorical isomorphisms of
`fxBaseRenamingVecCategory` and assembles the three iso-class CwR-axiom CONTENTS over them.

## Why this needs the EXTENSIONAL base

A categorical isomorphism's inverse laws are MORPHISM equalities (`compose inverse forward = identity`).  Over the
function-morphism renaming category those are function equalities (`funext` ⟹ `Quot.sound`); over the
indexed-inductive `RenamingTo` base their `ext`-reduction leaks `propext`.  Over `fxBaseRenamingVecCategory` the
inverse laws reduce — via `RenamingVec.ext` — to POINTWISE `lookup` equalities, discharged by `lookup_compose` +
`identity_lookup`, zero-axiom.  So the ext-powered iso constructor `isomorphismOfLookupInverse` is the direct
payoff of the extensional base: it is the lemma that makes a zero-axiom iso-class RMC over genuine renamings
possible at all.

## What lands here (all zero-axiom)

  * `RenamingVec.isomorphismOfLookupInverse` — **the ext-powered iso constructor**: a forward renaming, a backward
    renaming, and the two pointwise round-trips (`backward ∘ forward = id`, `forward ∘ backward = id` on lookups)
    assemble an `IsIsomorphism fxBaseRenamingVecCategory forward`, the inverse laws discharged by `ext`.
  * `RenamingVec.swapTwo` / `swapTwo_involutive` / `swapTwoIsIsomorphism` — a concrete NON-IDENTITY iso (the
    variable-0/1 swap on scope 2, self-inverse): the non-vacuity witness that the iso class is strictly larger
    than `{identity}` and the constructor handles real permutations.
  * `RenamingVec.IsCategoricalIsomorphism` — the iso representable-class membership predicate
    (`Nonempty (IsIsomorphism …)`).
  * `isCategoricalIsomorphism_identity` / `_compose` / `_pullback` — **the three iso-class CwR-axiom CONTENTS**:
    the class contains the identity, is closed under composition (generic `IsIsomorphism.comp`), and is closed
    under pullback (generic `IsIsomorphism.pullbackAlong`, the right projection being the identity).  Witnesses
    extracted from `Nonempty` by Prop-matching — no `Classical.choice`.

## Honest scope boundary — what is NOT yet here

This is the iso-class CwR-axiom CONTENT, not yet the `RepresentableMapCategory` RECORD.  Assembling the record
needs a `MorphismClass` over `fxBaseRenamingVecCategory`, whose `memberDecidable` field demands deciding
`Nonempty (IsIsomorphism … morphism)` — i.e. whether a `RenamingVec` is a finite bijection (a permutation).  That
decision (and the `iso ⟹ source = target` cardinality lemma it rests on) is a genuinely separate Init-only
finite-combinatorics sub-problem, `propext`-risky through `Fin`-quantifier decidability; it is the ONLY piece
between this file and the full `fxBaseRenamingVecRMC : RepresentableMapCategory`.  The iso class is the right
representable class for the renaming base precisely because its pullbacks exist GENERICALLY (`pullbackAlong` pulls
back an iso along any map); a broader class would need genuine renaming-category pullbacks, which do not exist for
non-isos.

## Zero-axiom verification

The constructor's inverse laws go through `RenamingVec.ext` + `lookup_compose`/`identity_lookup` (bridged to the
category projections by the `_compose_eq`/`_identity_eq` defeq samples); `swapTwo_involutive` matches `Fin 2`
structurally (`⟨0,_⟩`/`⟨1,_⟩`/absurd `⟨_+2,_⟩`), no `Fin.cases`; the three closure contents cite the generic
`IsomorphismCategorical` facts, extracting `Nonempty` witnesses by Prop-matching.  No `funext`, no `Classical`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- **The ext-powered categorical-iso constructor.**  A forward renaming, a backward renaming, and the two
pointwise round-trips assemble an `IsIsomorphism fxBaseRenamingVecCategory forward`.  The inverse laws are vector
equalities discharged by `RenamingVec.ext` — the direct payoff of the extensional base.  The category's
`compose`/`identity` projections are bridged to the `RenamingVec` operations via the `_compose_eq` / `_identity_eq`
defeq samples so `lookup_compose` / `identity_lookup` apply. -/
def RenamingVec.isomorphismOfLookupInverse {sourceScope targetScope : Nat}
    (forward : RenamingVec targetScope sourceScope) (backward : RenamingVec sourceScope targetScope)
    (forwardThenBackward : ∀ index, backward.lookup (forward.lookup index) = index)
    (backwardThenForward : ∀ index, forward.lookup (backward.lookup index) = index) :
    IsIsomorphism fxBaseRenamingVecCategory forward where
  inverse := backward
  leftInverse := RenamingVec.ext _ _ (fun index => by
    rw [fxBaseRenamingVecCategory_compose_eq, fxBaseRenamingVecCategory_identity_eq,
      lookup_compose, backwardThenForward, identity_lookup])
  rightInverse := RenamingVec.ext _ _ (fun index => by
    rw [fxBaseRenamingVecCategory_compose_eq, fxBaseRenamingVecCategory_identity_eq,
      lookup_compose, forwardThenBackward, identity_lookup])

/-- The variable-0/1 swap on scope 2 (head image is variable 1, tail image is variable 0). -/
def RenamingVec.swapTwo : RenamingVec 2 2 :=
  (⟨1, Nat.le.refl⟩, ⟨0, Nat.succ_pos 1⟩, PUnit.unit)

/-- The swap is self-inverse: applying its lookup twice is the identity on `Fin 2` (matched structurally —
`⟨0,_⟩`/`⟨1,_⟩` compute, `⟨_+2,_⟩` is absurd — so no `Fin.cases` propext leak). -/
theorem RenamingVec.swapTwo_involutive :
    ∀ index : Fin 2, RenamingVec.swapTwo.lookup (RenamingVec.swapTwo.lookup index) = index
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨position + 2, isLt⟩ =>
      absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)) (Nat.not_lt_zero position)

/-- **A concrete NON-IDENTITY categorical isomorphism** — the swap, self-inverse via the ext-powered constructor.
The non-vacuity witness: the iso class strictly contains more than the identity, and `isomorphismOfLookupInverse`
handles real permutations. -/
def RenamingVec.swapTwoIsIsomorphism :=
  RenamingVec.isomorphismOfLookupInverse RenamingVec.swapTwo RenamingVec.swapTwo
    RenamingVec.swapTwo_involutive RenamingVec.swapTwo_involutive

/-- **The iso representable-class membership predicate** for `fxBaseRenamingVecCategory`: a morphism is
representable iff it is a categorical isomorphism. -/
def RenamingVec.IsCategoricalIsomorphism {sourceScope targetScope : Nat}
    (morphism : RenamingVec targetScope sourceScope) : Prop :=
  Nonempty (IsIsomorphism fxBaseRenamingVecCategory morphism)

/-- **CwR-axiom content (identity).**  The identity morphism is representable (a categorical isomorphism). -/
theorem RenamingVec.isCategoricalIsomorphism_identity (scope : Nat) :
    RenamingVec.IsCategoricalIsomorphism (fxBaseRenamingVecCategory.identity scope) :=
  ⟨IsIsomorphism.identity (category := fxBaseRenamingVecCategory) scope⟩

/-- **CwR-axiom content (closed under composition).**  The composite of two representable maps is representable —
via the generic `IsIsomorphism.comp`, witnesses extracted by Prop-matching (no choice). -/
theorem RenamingVec.isCategoricalIsomorphism_compose {scopeA scopeB scopeC : Nat}
    (firstMorphism : RenamingVec scopeB scopeA) (secondMorphism : RenamingVec scopeC scopeB)
    (firstIso : RenamingVec.IsCategoricalIsomorphism firstMorphism)
    (secondIso : RenamingVec.IsCategoricalIsomorphism secondMorphism) :
    RenamingVec.IsCategoricalIsomorphism (fxBaseRenamingVecCategory.compose firstMorphism secondMorphism) :=
  match firstIso, secondIso with
  | ⟨isoFirst⟩, ⟨isoSecond⟩ => ⟨IsIsomorphism.comp isoFirst isoSecond⟩

/-- **CwR-axiom content (closed under pullback).**  A representable map pulls back along any morphism, the pullback
square's right projection again representable — via the generic `IsIsomorphism.pullbackAlong` (apex the domain of
the other leg, right projection the identity, itself representable). -/
theorem RenamingVec.isCategoricalIsomorphism_pullback {scopeA scopeB scopeC : Nat}
    (morphismF : fxBaseRenamingVecCategory.Morphism scopeA scopeC)
    (morphismG : fxBaseRenamingVecCategory.Morphism scopeB scopeC)
    (isoF : RenamingVec.IsCategoricalIsomorphism morphismF) :
    ∃ (square : PullbackSquare fxBaseRenamingVecCategory morphismF morphismG),
      RenamingVec.IsCategoricalIsomorphism square.projectionRight :=
  match isoF with
  | ⟨witness⟩ => ⟨witness.pullbackAlong, RenamingVec.isCategoricalIsomorphism_identity scopeB⟩

end FX1Poly.Tier0
