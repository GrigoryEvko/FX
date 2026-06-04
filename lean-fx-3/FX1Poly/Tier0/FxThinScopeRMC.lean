import FX1Poly.Tier0.RepresentableMapCategory

/-! # FX1Poly/Tier0/FxThinScopeRMC
    — the first concrete zero-axiom `RepresentableMapCategory` for FX (toward SN-084/085)

`RepresentableMapCategory.lean` ships the Uemura CwR interface (`RawCategory`, `MorphismClass`,
`PullbackSquare`, `IsIsomorphism`, `RepresentableMapCategory`) but with NO concrete inhabitant —
every structure is an obligation shape.  `FxRenamingCategory.lean` built the first concrete
`RawCategory` (the renaming category) and `IsomorphismCategorical.lean` proved the generic
CwR-axiom lemmas for the isomorphism class of ANY category.  The open question those left was:
is the full `RepresentableMapCategory` interface — category PLUS the three CwR closure axioms —
inhabitable at all at zero axioms?  This file answers YES, with a genuine (non-vacuous) instance.

## Why the renaming category is the WRONG base for a zero-axiom RMC

The renaming category's morphisms are functions (`RawRenaming source target = Fin source ->
Fin target`).  Every CwR axiom phrases a MORPHISM EQUALITY: `PullbackSquare.commutes` and
`.isUniversal` are equalities of composites, and `IsIsomorphism.leftInverse`/`rightInverse` equate
a composite with the identity.  For function morphisms those are FUNCTION equalities — provable
only by `funext`, which pulls `Quot.sound`.  So although the renaming category is itself a genuine
zero-axiom `RawCategory` (its three laws happen to hold by `rfl` via definitional eta), it cannot
host a zero-axiom `RepresentableMapCategory`: the first non-identity pullback or inverse drags in
`funext`.  The full renaming/substitution CwR (`fxBaseRMC` proper) therefore needs a DATA-morphism
base (renamings reified as vectors), a larger refactor deferred to a later task.

## The escape: a THIN (preorder) base, where every morphism equality is free

In a thin category a morphism `a -> b` is a PROOF (`PLift (a <= b)`), so proof irrelevance —
definitional in Lean 4's kernel, NOT an axiom — makes every parallel pair of morphisms equal by
`rfl`.  Every CwR equality obligation then discharges for free, with no `funext`.  This file builds
`thinScopeCategory`, the scope-inclusion preorder (objects are scopes `Nat`; a morphism `a -> b`
witnesses `a <= b`, i.e. scope `a` embeds into scope `b`), and equips it with a genuine
representable-map class.

The mathematical content is NOT vacuous: it lives in the pullback.  Pullbacks in a poset are
MEETS, so `closedUnderPullback` genuinely constructs the greatest common sub-scope and proves its
universal property.  Because the core `Nat.min` lemmas leak `propext`, this file hand-rolls a
propext-free meet (`meetScopes`) and proves its four facts by structural induction.

## Honest scope boundary

This is the THIN scope-inclusion CwR: degenerate (at most one morphism per object pair), with the
representable maps taken to be the equal-scope (isomorphism) class.  It is a legitimate, complete,
zero-axiom `RepresentableMapCategory` — the FIRST concrete inhabitant of the Tier-0 interface,
establishing that the interface is satisfiable.  It is NOT the full renaming/substitution CwR the
PolyCell vision ultimately wants (that is `fxBaseRMC` proper, awaiting the data-morphism base).

## What lands here (all zero-axiom)

  * `meetScopes` + `meetScopes_le_left` / `meetScopes_le_right` / `le_meetScopes` /
    `meetScopes_eq_right_of_le` — a propext-free structural meet and its universal-property facts.
  * `thinScopeCategory` — the scope-inclusion preorder as a `RawCategory`.
  * `thinScopeRepresentableMaps` — the equal-scope (iso) class, decidable via `Nat.decEq`.
  * `thinScopeRMC` — the assembled `RepresentableMapCategory`: `closedUnderPullback` via the meet,
    `isomorphismsRepresentable` via antisymmetry, `closedUnderComposition` via transitivity.

## Zero-axiom verification

The meet facts are structural `Nat` inductions over the clean `Nat.le` primitives
(`zero_le`, `succ_le_succ`, `le_of_succ_le_succ`, `not_succ_le_zero`, `le.refl`); the category and
RMC fields are `rfl` (proof irrelevance) plus `Nat.le_antisymm` / `Nat.le_trans` / `Nat.le_of_eq`
(all axiom-free).  No `funext`, no `Nat.min` (which leaks `propext`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- A propext-free structural meet (minimum) on scopes.  The core `Nat.min` and its lemmas leak
`propext`; this structural definition and its facts (below) stay axiom-free. -/
def meetScopes : Nat → Nat → Nat
  | 0, _ => 0
  | _+1, 0 => 0
  | scopeA+1, scopeB+1 => (meetScopes scopeA scopeB) + 1

/-- The meet is below its left component (the left pullback projection's inclusion witness). -/
theorem meetScopes_le_left : ∀ (scopeA scopeB : Nat), meetScopes scopeA scopeB ≤ scopeA
  | 0, _ => Nat.le.refl
  | _+1, 0 => Nat.zero_le _
  | scopeA+1, scopeB+1 => Nat.succ_le_succ (meetScopes_le_left scopeA scopeB)

/-- The meet is below its right component (the right pullback projection's inclusion witness). -/
theorem meetScopes_le_right : ∀ (scopeA scopeB : Nat), meetScopes scopeA scopeB ≤ scopeB
  | 0, _ => Nat.zero_le _
  | _+1, 0 => Nat.le.refl
  | scopeA+1, scopeB+1 => Nat.succ_le_succ (meetScopes_le_right scopeA scopeB)

/-- The meet is the greatest lower bound: any common lower bound factors through it.  This is the
universal property the pullback's `isUniversal` field consumes. -/
theorem le_meetScopes : ∀ (candidate scopeA scopeB : Nat),
    candidate ≤ scopeA → candidate ≤ scopeB → candidate ≤ meetScopes scopeA scopeB
  | 0, _, _, _, _ => Nat.zero_le _
  | _+1, 0, _, inclusionA, _ => absurd inclusionA (Nat.not_succ_le_zero _)
  | _+1, _+1, 0, _, inclusionB => absurd inclusionB (Nat.not_succ_le_zero _)
  | candidate+1, scopeA+1, scopeB+1, inclusionA, inclusionB =>
      Nat.succ_le_succ (le_meetScopes candidate scopeA scopeB
        (Nat.le_of_succ_le_succ inclusionA) (Nat.le_of_succ_le_succ inclusionB))

/-- When the right component is already below the left, the meet equals the right component.  This
witnesses that the pullback of an equal-scope (iso) map has an equal-scope right projection. -/
theorem meetScopes_eq_right_of_le : ∀ (scopeA scopeB : Nat),
    scopeB ≤ scopeA → meetScopes scopeA scopeB = scopeB
  | 0, 0, _ => rfl
  | _+1, 0, _ => rfl
  | 0, _+1, inclusion => absurd inclusion (Nat.not_succ_le_zero _)
  | scopeA+1, scopeB+1, inclusion =>
      congrArg (· + 1) (meetScopes_eq_right_of_le scopeA scopeB (Nat.le_of_succ_le_succ inclusion))

/-- **The thin scope-inclusion category.**  Objects are scopes (`Nat`); a morphism `scopeA ->
scopeB` is a proof that `scopeA <= scopeB` (scope `scopeA` embeds into scope `scopeB`).  Identity
is reflexivity, composition is transitivity; the three category laws hold by proof irrelevance
(`rfl`) — every parallel pair of morphisms is equal because each is a `Prop`-proof.  A genuine
zero-axiom thin `RawCategory`. -/
def thinScopeCategory : RawCategory.{0, 0} where
  Object := Nat
  Morphism := fun scopeA scopeB => PLift (scopeA ≤ scopeB)
  identity := fun scope => PLift.up (Nat.le_refl scope)
  compose := fun inclusionAB inclusionBC => PLift.up (Nat.le_trans inclusionAB.down inclusionBC.down)
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-- **The equal-scope (isomorphism) class.**  In a thin category the isomorphisms `scopeA ->
scopeB` are exactly those with `scopeA = scopeB`; that equality is the representable-map membership
predicate, decidable via `Nat.decEq`. -/
def thinScopeRepresentableMaps : MorphismClass thinScopeCategory where
  member := fun {scopeA scopeB} _inclusion => scopeA = scopeB
  memberDecidable := fun {scopeA scopeB} _inclusion => Nat.decEq scopeA scopeB

/-- **The first concrete zero-axiom `RepresentableMapCategory` for FX.**  The thin scope-inclusion
preorder with the equal-scope (iso) representable-map class.  All three CwR axioms are genuine:

  * `closedUnderPullback` — the pullback of an equal-scope map `inclusionAC` (so `scopeA = scopeC`)
    along any `inclusionBC` is the MEET `meetScopes scopeA scopeB` with its universal property; its
    right projection is itself representable because `scopeB <= scopeA` forces the meet to equal
    `scopeB`.
  * `isomorphismsRepresentable` — every isomorphism has equal source and target (antisymmetry).
  * `closedUnderComposition` — equal-scope maps compose (transitivity of equality).

This establishes that the Tier-0 `RepresentableMapCategory` interface is inhabitable at zero
axioms.  It is the degenerate thin instance, NOT the full renaming/substitution CwR (see the file
header). -/
def thinScopeRMC : RepresentableMapCategory.{0, 0} where
  underlying := thinScopeCategory
  representableMaps := thinScopeRepresentableMaps
  closedUnderPullback := by
    intro scopeA scopeB scopeC inclusionAC inclusionBC memberAC
    have equalityAC : scopeA = scopeC := memberAC
    have inclusionBA := Nat.le_trans inclusionBC.down (Nat.le_of_eq equalityAC.symm)
    refine ⟨{
      pullbackObject := meetScopes scopeA scopeB
      projectionLeft := PLift.up (meetScopes_le_left scopeA scopeB)
      projectionRight := PLift.up (meetScopes_le_right scopeA scopeB)
      commutes := rfl
      isUniversal := by
        intro candidateObject candidateLeft candidateRight _
        exact ⟨PLift.up (le_meetScopes candidateObject scopeA scopeB
          candidateLeft.down candidateRight.down), rfl, rfl⟩
    }, ?_⟩
    exact meetScopes_eq_right_of_le scopeA scopeB inclusionBA
  isomorphismsRepresentable := by
    intro scopeA scopeB inclusion iso
    exact Nat.le_antisymm inclusion.down iso.inverse.down
  closedUnderComposition := by
    intro scopeA scopeB scopeC _ _ memberAB memberBC
    exact memberAB.trans memberBC

end FX1Poly.Tier0
