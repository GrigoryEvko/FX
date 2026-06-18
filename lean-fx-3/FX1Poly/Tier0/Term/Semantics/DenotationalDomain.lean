/-! # Tier0/Term — denotational semantics: the domain-theoretic fixpoint core (term-21)

The first of the term-axis SEMANTICS rungs (`term-21..25`).  Denotational semantics interprets a program as
a point of a DOMAIN (a directed-complete pointed partial order), with recursion denoted by the LEAST
FIXPOINT of a continuous functional — the Kleene fixpoint `⊔ₙ fⁿ(⊥)`.  This file ships that genuine core
(each piece zero-axiom, Init-only):

  * **`PointedDcpo`** — a pointed ω-CPO interface: a partial order (`Below`, refl/trans/antisymm) with a
    least element `bottom` and least upper bounds `sup` of ω-chains (`sup_isUpperBound` / `sup_isLeast`).
  * **`Continuous`** (= `Monotone` + sup-preservation) — Scott-continuous endofunctions, the denotations of
    `λ`-definable functionals.
  * **`kleeneFixpoint`** = `sup (fⁿ ⊥)` with **`kleeneFixpoint_isFixpoint`** (★ — a continuous `f` fixes it)
    and **`kleeneFixpoint_isLeast`** (★ — it is BELOW every other fixpoint).  This is the LEAST-FIXPOINT
    theorem: recursion = least fixpoint, the foundation of denotational semantics.
  * **`trivialDomain`** + **`trivialDomain_kleeneFixpoint_eq`** — a concrete pointed-DCPO witness (the
    one-point domain) on which the fixpoint computes.

The kernel's signature already RESERVES the syntactic counterparts — `gen_scottContinuous` (183) and
`gen_fixedPoint` (184); this file is the semantic side those reserved generators denote into.

## Honest scope

Shipped: the pointed-DCPO / continuity interface + the Kleene least-fixpoint theorem + a concrete domain
witness.  DEFERRED (the rest of `term-21..25`, omnibus `fxTerm_hasDenotationalAdequacy = false`): the D∞
REFLEXIVE OBJECT (the bilimit solution of `D ≅ [D → D]` — the model of the untyped `λ`-calculus), COHERENCE
SPACES / stable maps, and computational ADEQUACY (the denotation is `⊥` iff the term diverges — faithfulness
of meaning to operational behaviour), all of which need substantial further domain theory and a denotation
function for the actual term calculus.

## Zero-axiom verification

`iterate` is structural Nat recursion; `iterate_isChain` / `kleeneFixpoint_isLeast` are Nat induction using
`Monotone` + `bottom_below`; `kleeneFixpoint_isFixpoint` chains continuity with `sup_tail` (a chain and its
tail have the same sup, by `below_antisymm` of the two lub bounds); the witness is the one-point order.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditTier0TermDenotationalDomain.lean`.
-/

namespace FX1Poly.Core

/-! ## The pointed ω-CPO interface -/

/-- A **pointed directed-complete partial order** (ω-CPO): a partial order with a least element and least
upper bounds of ω-chains.  The denotational-semantics domain. -/
structure PointedDcpo where
  /-- The carrier of denotations. -/
  Carrier : Type
  /-- The information order `⊑`. -/
  Below : Carrier → Carrier → Prop
  /-- Reflexivity. -/
  below_refl : ∀ point, Below point point
  /-- Transitivity. -/
  below_trans : ∀ {first second third}, Below first second → Below second third → Below first third
  /-- Antisymmetry. -/
  below_antisymm : ∀ {first second}, Below first second → Below second first → first = second
  /-- The least element. -/
  bottom : Carrier
  /-- `bottom` is below everything. -/
  bottom_below : ∀ point, Below bottom point
  /-- The least upper bound of an `ω`-sequence. -/
  sup : (Nat → Carrier) → Carrier
  /-- `sup` is an upper bound of an ascending chain. -/
  sup_isUpperBound : ∀ (sequence : Nat → Carrier),
    (∀ index, Below (sequence index) (sequence (index + 1))) →
    ∀ index, Below (sequence index) (sup sequence)
  /-- `sup` is the LEAST upper bound of an ascending chain. -/
  sup_isLeast : ∀ (sequence : Nat → Carrier),
    (∀ index, Below (sequence index) (sequence (index + 1))) →
    ∀ upperBound, (∀ index, Below (sequence index) upperBound) → Below (sup sequence) upperBound

/-- An ascending `ω`-CHAIN: each element is below the next. -/
def PointedDcpo.IsChain (domain : PointedDcpo) (sequence : Nat → domain.Carrier) : Prop :=
  ∀ index, domain.Below (sequence index) (sequence (index + 1))

/-- A **monotone** endofunction: order-preserving. -/
def PointedDcpo.Monotone (domain : PointedDcpo) (transform : domain.Carrier → domain.Carrier) : Prop :=
  ∀ {first second}, domain.Below first second → domain.Below (transform first) (transform second)

/-- A **Scott-continuous** endofunction: monotone and preserving sups of chains — the denotation of a
`λ`-definable functional. -/
def PointedDcpo.Continuous (domain : PointedDcpo) (transform : domain.Carrier → domain.Carrier) : Prop :=
  domain.Monotone transform ∧
    ∀ (sequence : Nat → domain.Carrier), domain.IsChain sequence →
      transform (domain.sup sequence) = domain.sup (fun index => transform (sequence index))

/-! ## The iteration chain and its sup -/

/-- The iterates `fⁿ(⊥)` of an endofunction from the bottom element. -/
def PointedDcpo.iterate (domain : PointedDcpo) (transform : domain.Carrier → domain.Carrier) :
    Nat → domain.Carrier
  | 0 => domain.bottom
  | index + 1 => transform (domain.iterate transform index)

/-- The iterates form an ascending chain when the function is monotone. -/
theorem PointedDcpo.iterate_isChain (domain : PointedDcpo)
    (transform : domain.Carrier → domain.Carrier) (monotone : domain.Monotone transform) :
    domain.IsChain (domain.iterate transform) := by
  intro index
  induction index with
  | zero => exact domain.bottom_below _
  | succ previous inductionHypothesis => exact monotone inductionHypothesis

/-- A chain and its tail have the SAME sup (the extra first element adds no information). -/
theorem PointedDcpo.sup_tail (domain : PointedDcpo) (sequence : Nat → domain.Carrier)
    (chain : domain.IsChain sequence) :
    domain.sup (fun index => sequence (index + 1)) = domain.sup sequence := by
  have tailChain : domain.IsChain (fun index => sequence (index + 1)) :=
    fun index => chain (index + 1)
  apply domain.below_antisymm
  · apply domain.sup_isLeast _ tailChain
    intro index
    exact domain.sup_isUpperBound sequence chain (index + 1)
  · apply domain.sup_isLeast _ chain
    intro index
    exact domain.below_trans (chain index) (domain.sup_isUpperBound _ tailChain index)

/-! ## The Kleene least fixpoint -/

/-- The **Kleene fixpoint** `⊔ₙ fⁿ(⊥)` — the denotation of recursion. -/
def PointedDcpo.kleeneFixpoint (domain : PointedDcpo) (transform : domain.Carrier → domain.Carrier) :
    domain.Carrier :=
  domain.sup (domain.iterate transform)

/-- ★ **The Kleene fixpoint IS a fixpoint** of a continuous function: `f (⊔ₙ fⁿ⊥) = ⊔ₙ fⁿ⊥` (continuity
pushes `f` through the sup, then the shifted chain has the same sup). -/
theorem PointedDcpo.kleeneFixpoint_isFixpoint (domain : PointedDcpo)
    (transform : domain.Carrier → domain.Carrier) (continuous : domain.Continuous transform) :
    transform (domain.kleeneFixpoint transform) = domain.kleeneFixpoint transform := by
  obtain ⟨monotone, preservesSup⟩ := continuous
  have chain := domain.iterate_isChain transform monotone
  show transform (domain.sup (domain.iterate transform)) = domain.sup (domain.iterate transform)
  rw [preservesSup (domain.iterate transform) chain]
  exact domain.sup_tail (domain.iterate transform) chain

/-- ★ **The Kleene fixpoint is the LEAST fixpoint**: it is below every other fixpoint (the iterates are all
below it, by induction using `bottom_below` and monotonicity through the fixpoint equation). -/
theorem PointedDcpo.kleeneFixpoint_isLeast (domain : PointedDcpo)
    (transform : domain.Carrier → domain.Carrier) (monotone : domain.Monotone transform)
    (point : domain.Carrier) (isFixpoint : transform point = point) :
    domain.Below (domain.kleeneFixpoint transform) point := by
  apply domain.sup_isLeast _ (domain.iterate_isChain transform monotone)
  intro index
  induction index with
  | zero => exact domain.bottom_below point
  | succ previous inductionHypothesis =>
      have stepBelow : domain.Below (transform (domain.iterate transform previous)) (transform point) :=
        monotone inductionHypothesis
      rw [isFixpoint] at stepBelow
      exact stepBelow

/-- A continuous function is monotone (the first component of continuity). -/
theorem PointedDcpo.continuous_isMonotone (domain : PointedDcpo)
    {transform : domain.Carrier → domain.Carrier} (continuous : domain.Continuous transform) :
    domain.Monotone transform :=
  continuous.1

/-- ★ **Park induction** (fixpoint induction): the Kleene fixpoint is the least PRE-fixpoint — below every
`point` with `f point ⊑ point`.  This is the genuine induction principle for recursion (`kleeneFixpoint_isLeast`
is the special case `f point = point`), the workhorse for reasoning about recursive denotations. -/
theorem PointedDcpo.kleeneFixpoint_isLeastPrefixpoint (domain : PointedDcpo)
    (transform : domain.Carrier → domain.Carrier) (monotone : domain.Monotone transform)
    (point : domain.Carrier) (prefixpoint : domain.Below (transform point) point) :
    domain.Below (domain.kleeneFixpoint transform) point := by
  apply domain.sup_isLeast _ (domain.iterate_isChain transform monotone)
  intro index
  induction index with
  | zero => exact domain.bottom_below point
  | succ previous inductionHypothesis =>
      exact domain.below_trans (monotone inductionHypothesis) prefixpoint

/-- ★ **The fixpoint operator is MONOTONE**: a pointwise-larger continuous functional has a larger least
fixpoint (`f ⊑ g pointwise ⟹ fix f ⊑ fix g`).  The semantic monotonicity of recursion. -/
theorem PointedDcpo.kleeneFixpoint_monotone (domain : PointedDcpo)
    (lowerTransform upperTransform : domain.Carrier → domain.Carrier)
    (lowerMonotone : domain.Monotone lowerTransform)
    (upperContinuous : domain.Continuous upperTransform)
    (pointwiseBelow : ∀ value, domain.Below (lowerTransform value) (upperTransform value)) :
    domain.Below (domain.kleeneFixpoint lowerTransform) (domain.kleeneFixpoint upperTransform) := by
  have upperFixpoint := domain.kleeneFixpoint_isFixpoint upperTransform upperContinuous
  apply domain.sup_isLeast _ (domain.iterate_isChain lowerTransform lowerMonotone)
  intro index
  induction index with
  | zero => exact domain.bottom_below _
  | succ previous inductionHypothesis =>
      have throughUpper :
          domain.Below (lowerTransform (domain.iterate lowerTransform previous))
            (upperTransform (domain.kleeneFixpoint upperTransform)) :=
        domain.below_trans (lowerMonotone inductionHypothesis)
          (pointwiseBelow (domain.kleeneFixpoint upperTransform))
      rw [upperFixpoint] at throughUpper
      exact throughUpper

/-! ## A concrete domain witness — the one-point domain -/

/-- The **one-point domain**: a concrete pointed DCPO (the trivial denotational model). -/
def trivialDomain : PointedDcpo where
  Carrier := Unit
  Below := fun _ _ => True
  below_refl := fun _ => trivial
  below_trans := fun _ _ => trivial
  below_antisymm := fun {first second} _ _ => by cases first; cases second; rfl
  bottom := ()
  bottom_below := fun _ => trivial
  sup := fun _ => ()
  sup_isUpperBound := fun _ _ _ => trivial
  sup_isLeast := fun _ _ _ _ => trivial

/-- The Kleene fixpoint computes on the one-point domain. -/
theorem trivialDomain_kleeneFixpoint_eq (transform : trivialDomain.Carrier → trivialDomain.Carrier) :
    trivialDomain.kleeneFixpoint transform = () := rfl

end FX1Poly.Core
