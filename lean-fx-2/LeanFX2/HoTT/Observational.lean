import LeanFX2.HoTT.Equivalence

/-! # HoTT/Observational — observational equality (HOTT)

Observational equality `OEq` is the canonical equality of
**Higher Observational Type Theory** (HOTT, Altenkirch et al.).
Unlike Martin-Löf identity types where `Eq A x y` is opaque,
`OEq A x y` is **decomposable**: equalities at structured types
reduce to equalities at component types.

Per `fx_design.md` §6 (modality discipline) and §27 (metatheory):
HOTT is one of FX's three foundational layers (alongside MLTT
and cubical), connected by the `Modal/Bridge.lean` (D4.6) and
`Bridge/IdEqType.lean` (D9.4) constructions.

## What ships (Phase 12.A.3 — Day 3 D3.5+ observational core)

* `OEq A x y` — observational equality predicate, an `abbrev`
  over Lean's `Eq` for set-level types (h-sets).  At higher
  truncation levels (h-groupoids, ∞-types), OEq has richer
  structure; v1.0 ships the set-level fragment.
* `OEq.refl / sym / trans` — equivalence-relation laws,
  zero-axiom via Lean's `Eq` constructors
* `OEq.cong` — function congruence: `f x = f x'` when `x = x'`
* `OEq.transport` — transport across observational equality
* `OEq.subst` — substitute equal-by-OEq into a property
* `OEqDecomposeProd` — decomposition for product equalities
  (set-level): pair equality reduces to componentwise equality
* `OEqDecomposeSum` — decomposition for sum-type equalities
  (set-level): equality requires same constructor + payload eq
* `OEqDecomposePiSetWise` — pointwise function equality (set
  level, weaker than full funext — funext is HOTT-internal,
  ships as a definitional rule once `Reduction/Step.lean` D2.6
  lands)
* Set-level UIP (uniqueness of identity proofs): two OEq
  proofs of the same statement are themselves OEq

## Why set level for v1.0

Full observational HOTT requires the OEq computation rules
(funext + univalence DEFINITIONAL) to land in the kernel — task
D2.6 (#1310).  Until those Step rules ship, OEq decomposition
at higher truncations would need `propext`/`funext` axioms.
The set-level fragment is fully zero-axiom because Lean's `Eq`
on h-sets matches OEq pointwise.

When D2.6 lands, OEq becomes a kernel primitive `Ty.oeq` with
the decomposition rules baked in — at that point this meta-
level file becomes a thin wrapper documenting the meta-theorem
"set-level OEq agrees with Lean's Eq".

## Why decomposable

The defining property of HOTT: equalities should COMPUTE on
their structure.  For a product type `A × B`, an equality
`(a₁, b₁) = (a₂, b₂)` should decompose to `a₁ = a₂ ∧ b₁ = b₂`
DEFINITIONALLY.  Standard MLTT identity doesn't have this
property; HOTT's observational equality does.

This decomposability is what makes HOTT compatible with
univalence WITHOUT axioms: the universe equality
`A = B → Equiv A B` decomposes through OEq into a constructive
witness.

## Dependencies

* `HoTT/Equivalence.lean` — Equiv structure for set-level
  OEq-of-types decomposition

## Downstream consumers

* `Modal/Bridge.lean` (D4.6) — observational ↔ univalent
  transfer
* `Bridge/IdEqType.lean` (D9.4) — `Ty.id (Ty.universe lvl) A B
  = Ty.equiv A B` definitional bridge
* `HoTT/Univalence.lean` (D3.6) — ua as zero-axiom theorem
  via OEq decomposition

Zero-axiom verified per declaration via AuditAll. -/

namespace LeanFX2

universe leftLevel rightLevel

/-! ## OEq core: set-level observational equality

For h-sets, `OEq A x y` is `Eq A x y`.  This is propext-clean
because Lean's `Eq` ctors (Eq.refl) and eliminators (Eq.subst,
Eq.mpr) don't introduce axioms.  Higher-truncation OEq (with
non-trivial path coherences) requires HOTT's kernel primitives;
v1.0 ships the set-level fragment. -/

/-- Observational equality at the set level.  An `abbrev` over
Lean's `Eq` so the `OEq.refl/sym/trans` laws are exactly Lean's
`Eq.refl/symm/trans` (zero axioms — direct constructor use). -/
@[reducible] def OEq {alpha : Sort leftLevel} (firstValue secondValue : alpha) : Prop :=
  firstValue = secondValue

namespace OEq

/-! ## Equivalence-relation laws -/

/-- Reflexivity. -/
theorem refl {alpha : Sort leftLevel} (someValue : alpha) :
    OEq someValue someValue :=
  Eq.refl someValue

/-- Symmetry. -/
theorem sym {alpha : Sort leftLevel}
    {firstValue secondValue : alpha}
    (someEquality : OEq firstValue secondValue) :
    OEq secondValue firstValue :=
  Eq.symm someEquality

/-- Transitivity. -/
theorem trans {alpha : Sort leftLevel}
    {firstValue secondValue thirdValue : alpha}
    (firstEquality : OEq firstValue secondValue)
    (secondEquality : OEq secondValue thirdValue) :
    OEq firstValue thirdValue :=
  Eq.trans firstEquality secondEquality

/-! ## Function congruence and transport -/

/-- Function congruence: `f x = f x'` when `x = x'`.  This is
`Eq.congrArg` from Lean's stdlib, but we re-export under
`OEq.cong` to keep the meta-theory in one namespace. -/
theorem cong {alpha : Sort leftLevel} {beta : Sort rightLevel}
    (someFn : alpha → beta)
    {firstValue secondValue : alpha}
    (someEquality : OEq firstValue secondValue) :
    OEq (someFn firstValue) (someFn secondValue) :=
  congrArg someFn someEquality

/-- Transport across observational equality.  Given a property
`P : alpha → Prop` and an equality `x = y`, transport carries
`P x` to `P y`.  This is exactly `Eq.subst` re-exported. -/
theorem transport {alpha : Sort leftLevel}
    {someProperty : alpha → Prop}
    {firstValue secondValue : alpha}
    (someEquality : OEq firstValue secondValue)
    (firstHolds : someProperty firstValue) :
    someProperty secondValue :=
  someEquality ▸ firstHolds

/-- Substitution: if two values are observationally equal, any
property that holds for one holds for the other.  Same content
as `transport` but with the binders flipped, useful when the
property comes from context. -/
theorem subst {alpha : Sort leftLevel}
    (someProperty : alpha → Prop)
    {firstValue secondValue : alpha}
    (someEquality : OEq firstValue secondValue) :
    someProperty firstValue → someProperty secondValue :=
  fun firstHolds => someEquality ▸ firstHolds

/-! ## Two-argument congruence -/

/-- Binary function congruence: `f x₁ y₁ = f x₂ y₂` when both
`x₁ = x₂` and `y₁ = y₂`.  Built from successive single-argument
congruences via `cong`. -/
theorem cong2 {alpha : Sort leftLevel} {beta : Sort rightLevel}
    {gamma : Sort leftLevel}
    (someFn : alpha → beta → gamma)
    {firstX secondX : alpha} {firstY secondY : beta}
    (xEquality : OEq firstX secondX)
    (yEquality : OEq firstY secondY) :
    OEq (someFn firstX firstY) (someFn secondX secondY) := by
  rw [xEquality, yEquality]

end OEq

/-! ## Decomposition rules for structured types

The defining property of observational equality: equalities at
structured types reduce to equalities at component types.  At
the set level, these are theorems (not definitional rules) —
provable via Lean's `Eq` machinery. -/

/-! ### Product decomposition -/

namespace OEqDecomposeProd

/-- Forward: pair equality implies componentwise equality.
Constrained to `Type` (not `Sort`) since `Prod` lives at `Type`. -/
theorem to_components {alpha : Type leftLevel} {beta : Type rightLevel}
    {firstX secondX : alpha} {firstY secondY : beta}
    (someEquality : OEq (firstX, firstY) (secondX, secondY)) :
    OEq firstX secondX ∧ OEq firstY secondY := by
  injection someEquality with xEq yEq
  exact ⟨xEq, yEq⟩

/-- Reverse: componentwise equality implies pair equality.  Set
level: discharged by congruence on `Prod.mk`. -/
theorem from_components {alpha : Type leftLevel} {beta : Type rightLevel}
    {firstX secondX : alpha} {firstY secondY : beta}
    (xEquality : OEq firstX secondX) (yEquality : OEq firstY secondY) :
    OEq (firstX, firstY) (secondX, secondY) := by
  rw [xEquality, yEquality]

end OEqDecomposeProd

/-! ### Sum decomposition -/

namespace OEqDecomposeSum

/-- Sum equality of `inl`-tagged values reduces to component
equality.  Constrained to `Type` (Sum lives at Type, not Sort). -/
theorem inl_components {alpha : Type leftLevel} {beta : Type rightLevel}
    {firstX secondX : alpha}
    (someEquality :
      OEq (Sum.inl firstX : Sum alpha beta) (Sum.inl secondX)) :
    OEq firstX secondX := by
  injection someEquality

/-- Sum equality of `inr`-tagged values reduces to component
equality. -/
theorem inr_components {alpha : Type leftLevel} {beta : Type rightLevel}
    {firstY secondY : beta}
    (someEquality :
      OEq (Sum.inr firstY : Sum alpha beta) (Sum.inr secondY)) :
    OEq firstY secondY := by
  injection someEquality

/-- Cross-tag sum equality is impossible: `inl x ≠ inr y`.
Discharged via `Sum.noConfusion` with explicit motive. -/
theorem inl_inr_impossible {alpha : Type leftLevel} {beta : Type rightLevel}
    {someX : alpha} {someY : beta}
    (impossibleEq :
      OEq (Sum.inl someX : Sum alpha beta) (Sum.inr someY)) :
    False := by
  cases impossibleEq

end OEqDecomposeSum

/-! ### Pointwise function equality (set-level)

Full function extensionality `(∀ x, f x = g x) → f = g` is
`funext`, a propext-class axiom barred under our zero-axiom
doctrine.  At HOTT-set level once D2.6 lands, funext becomes
DEFINITIONAL (a Step rule), not an axiom.

This file ships the WEAKER direction: equal functions ARE
pointwise equal — no axiom needed. -/

namespace OEqDecomposePiSetWise

/-- Forward: function equality implies pointwise equality.
Zero-axiom (Eq.subst on `f x` for arbitrary `x`). -/
theorem to_pointwise
    {alpha : Sort leftLevel} {beta : alpha → Sort rightLevel}
    {firstFn secondFn : ∀ (someValue : alpha), beta someValue}
    (functionEquality : OEq firstFn secondFn) :
    ∀ (someValue : alpha), OEq (firstFn someValue) (secondFn someValue) :=
  fun someValue => functionEquality ▸ rfl

/-! The reverse direction (`(∀ x, f x = g x) → f = g`) is
**funext**, which is a propext-class axiom in MLTT.  Under
our zero-axiom doctrine, we do NOT discharge it as a theorem
in this file.  Instead:

* For HOTT semantics: funext lands as a DEFINITIONAL Step rule
  in D2.6 (Reduction/Step.lean: ~15 HOTT OEq reduction rules).
  At that point, `funext` becomes provable as a theorem inside
  the kernel — not an axiom of Lean meta-theory.
* For cubical semantics: funext is provable from `Path` (PathP
  along `i ↦ alpha`) — ships in `Cubical/PathLemmas.lean` (D3.7).
* For everything else: this is the FUNEXT GAP that motivates
  our HOTT/cubical commitment.

The pointwise→function direction lives nowhere in this file. -/

end OEqDecomposePiSetWise

/-! ## UIP at set level

Uniqueness of identity proofs (UIP): for an h-set `alpha` and
two values `x y : alpha`, any two proofs of `x = y` are
themselves equal.

This is true at SET LEVEL by definition (sets are 0-truncated
types where any two parallel paths are equal).  At higher
truncation levels (h-groupoid, h-2-groupoid, ...) UIP fails —
that's the point of HoTT's Univalent Foundations.

Lean's built-in `Eq` is propositional (any two `a = b` proofs
are themselves equal by definition of Prop), so UIP is
`rfl` for proofs typed at `Prop`.  This is the SUBSINGLETON
property of `Prop` in Lean's foundation. -/

namespace OEqUIP

/-- UIP at the set level: any two proofs of an OEq are equal
as propositions.  Holds because `OEq A x y : Prop` and Prop is
a subsingleton (any two proofs of the same Prop are equal,
constructively in Lean). -/
theorem uip_set {alpha : Sort leftLevel} {firstValue secondValue : alpha}
    (firstProof secondProof : OEq firstValue secondValue) :
    firstProof = secondProof := by
  rfl

end OEqUIP

/-! ## OEq for type equivalences (set-level connection to Equiv)

Per the HOTT principle "equality of types is equivalence of
types": the bridge `Ty.id Type A B = Equiv A B` would make this
DEFINITIONAL.  At the meta-level (this file), we ship the
WEAKER set-level connection: a type equality gives an
equivalence (the canonical one). -/

namespace OEqType

/-- Type equality refines to type equivalence (the canonical
direction).  At HOTT-with-univalence, the converse also holds
(univalence axiom — but as a theorem, since D2.6's HOTT rules
make it definitional).

Marked `def` because the result `Equiv alpha beta` is `Type`,
not `Prop` — the distinction matters for Lean kernel-level
type-checking. -/
def to_equiv {alpha beta : Type leftLevel}
    (typeEquality : OEq alpha beta) :
    Equiv alpha beta :=
  typeEquality ▸ Equiv.refl alpha

end OEqType

/-! ## Smoke samples -/

/-- OEq is reflexive. -/
example : OEq (42 : Nat) 42 := OEq.refl 42

/-- Pair equality decomposes to componentwise. -/
example
    {firstX secondX : Nat} {firstY secondY : Nat}
    (xEquality : OEq firstX secondX) (yEquality : OEq firstY secondY) :
    OEq (firstX, firstY) (secondX, secondY) :=
  LeanFX2.OEqDecomposeProd.from_components xEquality yEquality

/-- Sum.inl injectivity at the OEq level. -/
example {firstValue secondValue : Nat}
    (someEquality :
      OEq (Sum.inl firstValue : Sum Nat String) (Sum.inl secondValue)) :
    OEq firstValue secondValue :=
  OEqDecomposeSum.inl_components someEquality

/-- Function equality implies pointwise equality (set-level). -/
example
    {firstFn secondFn : Nat → Nat}
    (functionEquality : OEq firstFn secondFn) (someValue : Nat) :
    OEq (firstFn someValue) (secondFn someValue) :=
  OEqDecomposePiSetWise.to_pointwise functionEquality someValue

/-- UIP at set level: two `42 = 42` proofs are themselves equal. -/
example (firstProof secondProof : OEq (42 : Nat) 42) :
    firstProof = secondProof :=
  OEqUIP.uip_set firstProof secondProof

/-- A type equality gives a canonical equivalence. -/
example (typeEquality : OEq Nat Nat) : Equiv Nat Nat :=
  OEqType.to_equiv typeEquality

end LeanFX2
