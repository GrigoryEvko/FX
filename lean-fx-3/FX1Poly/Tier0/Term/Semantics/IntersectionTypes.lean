/-! # Tier0/Term — intersection types: BCD subtyping + the filter model (term-22)

The second term-axis SEMANTICS rung.  Intersection types (Coppo-Dezani; Barendregt-Coppo-Dezani) assign a
λ-term a CONJUNCTION of types; their two landmark facts are the NORMALIZATION CHARACTERIZATION (a term is
typeable iff it normalizes) and the FILTER MODEL (filters of intersection types form a domain that models
the untyped λ-calculus).  This file ships the genuine algebraic + filter core (each piece zero-axiom):

  * **`IntersectionType`** (`omega` ⊤ / `atom` / `arrow` / `inter` ∩) and the **BCD subtyping** preorder
    `Subtype` with: `omega` is the TOP (`omega_isTop`), `∩` is the greatest lower bound
    (`inter_isGreatestLowerBound` — `interLeft`/`interRight` + `leInter`), arrow is contra/covariant.  So
    intersection types form a MEET-SEMILATTICE WITH TOP up to subtype-equivalence (`inter_commutative` /
    `inter_idempotent` derived).
  * **`IsFilter`** (contains `ω`, upward-closed under `≤`, `∩`-closed) with the LEAST filter `omegaFilter`
    (`omegaFilter_isLeast`) and the order-reversing **`principalFilter`** embedding of types
    (`principalFilter_antitone`).
  * **The filter model is ω-COMPLETE** (`filterSup` via filter generation, with `filterSup_isUpperBound` /
    `filterSup_isLeast` ★): filters under inclusion form a pointed ω-complete PREORDER — the filter model's
    domain substrate, the order-theoretic twin of `term-21`'s `PointedDcpo`.

## Honest scope

Shipped: the BCD intersection-type algebra (meet-semilattice + top) + filters + the least filter + the
order-reversing principal embedding + the ω-complete filter PREORDER (lub `filterSup`).  DEFERRED: (1) the
ANTISYMMETRIC poset quotient making the filter preorder a genuine `PointedDcpo` — filter equality from mutual
inclusion is PREDICATE EXTENSIONALITY (`propext` + `funext`), which the zero-axiom kernel forbids, so the
domain proper lives only up to the preorder here; (2) the λ-APPLICATION structure of the filter model (the
reflexive object `F ≅ [F → F]`, needing the arrow-distributes-over-`∩` BCD rule); (3) the NORMALIZATION
CHARACTERIZATION `typeable ⟺ normalizing` (a reducibility argument one way, subject expansion the other) —
the `term-22` capstone, in the omnibus `fxTerm_hasDenotationalAdequacy = false`.

## Zero-axiom verification

`Subtype` / `GeneratedFilter` are ordinary inductives; the lattice laws are their constructors plus short
`Subtype.trans` chains; `filterSup_isLeast` is induction on `GeneratedFilter` into a `Prop` motive (no
antisymmetry, hence no `funext`/`propext`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTier0TermIntersectionTypes.lean`.
-/

namespace FX1Poly.Core

/-! ## Intersection types and BCD subtyping -/

/-- **Intersection types**: top `omega`, atoms, arrows, and intersections `∩`. -/
inductive IntersectionType where
  /-- The universal type `ω` (every term has it). -/
  | omega
  /-- A type atom. -/
  | atom (index : Nat)
  /-- A function type `domain → codomain`. -/
  | arrow (domain codomain : IntersectionType)
  /-- An intersection `left ∩ right`. -/
  | inter (left right : IntersectionType)

/-- **BCD subtyping** `≤`: a preorder in which `omega` is the top and `inter` is the greatest lower bound,
with arrows contravariant in the domain and covariant in the codomain. -/
inductive Subtype : IntersectionType → IntersectionType → Prop where
  /-- Reflexivity. -/
  | refl (subject : IntersectionType) : Subtype subject subject
  /-- Transitivity. -/
  | trans {lower middle upper : IntersectionType} :
      Subtype lower middle → Subtype middle upper → Subtype lower upper
  /-- `omega` is the top. -/
  | omegaTop (subject : IntersectionType) : Subtype subject IntersectionType.omega
  /-- An intersection is below its left component. -/
  | interLeft (left right : IntersectionType) : Subtype (IntersectionType.inter left right) left
  /-- An intersection is below its right component. -/
  | interRight (left right : IntersectionType) : Subtype (IntersectionType.inter left right) right
  /-- A common lower bound is below the intersection. -/
  | leInter {lowerBound left right : IntersectionType} :
      Subtype lowerBound left → Subtype lowerBound right →
      Subtype lowerBound (IntersectionType.inter left right)
  /-- Arrows: contravariant domain, covariant codomain. -/
  | arrowMono {domain domain' codomain codomain' : IntersectionType} :
      Subtype domain' domain → Subtype codomain codomain' →
      Subtype (IntersectionType.arrow domain codomain) (IntersectionType.arrow domain' codomain')
  /-- BCD: the top is itself a function type (`ω ≤ ω → ω`). -/
  | arrowOmega :
      Subtype IntersectionType.omega (IntersectionType.arrow IntersectionType.omega IntersectionType.omega)
  /-- BCD: arrows distribute over intersection on the codomain. -/
  | arrowDistributes (domain codomainLeft codomainRight : IntersectionType) :
      Subtype
        (IntersectionType.inter (IntersectionType.arrow domain codomainLeft)
          (IntersectionType.arrow domain codomainRight))
        (IntersectionType.arrow domain (IntersectionType.inter codomainLeft codomainRight))

/-- `omega` is the TOP of the subtype order. -/
theorem omega_isTop (subject : IntersectionType) : Subtype subject IntersectionType.omega :=
  Subtype.omegaTop subject

/-- ★ **`∩` is the GREATEST LOWER BOUND**: below both components, and above every common lower bound. -/
theorem inter_isGreatestLowerBound (left right : IntersectionType) :
    Subtype (IntersectionType.inter left right) left
      ∧ Subtype (IntersectionType.inter left right) right
      ∧ ∀ lowerBound, Subtype lowerBound left → Subtype lowerBound right →
          Subtype lowerBound (IntersectionType.inter left right) :=
  ⟨Subtype.interLeft left right, Subtype.interRight left right,
   fun _ belowLeft belowRight => Subtype.leInter belowLeft belowRight⟩

/-- Intersection is commutative up to subtype-equivalence (one direction; the other is symmetric). -/
theorem inter_commutative (left right : IntersectionType) :
    Subtype (IntersectionType.inter left right) (IntersectionType.inter right left) :=
  Subtype.leInter (Subtype.interRight left right) (Subtype.interLeft left right)

/-- Intersection is idempotent up to subtype-equivalence: `τ ≤ τ ∩ τ` (the reverse is `interLeft`). -/
theorem inter_idempotent (subject : IntersectionType) :
    Subtype subject (IntersectionType.inter subject subject) :=
  Subtype.leInter (Subtype.refl subject) (Subtype.refl subject)

/-- BCD: the top is a function type — `ω ≤ ω → ω` (so every term, having type `ω`, is a function). -/
theorem omega_isArrow :
    Subtype IntersectionType.omega (IntersectionType.arrow IntersectionType.omega IntersectionType.omega) :=
  Subtype.arrowOmega

/-- ★ BCD: arrows DISTRIBUTE over intersection — `(σ→τ) ∩ (σ→ρ) ≤ σ → (τ ∩ ρ)`.  The type-theoretic
arrow/intersection interaction that makes `Subtype` genuine BCD subtyping (and powers the filter
λ-model). -/
theorem arrow_distributesOverInter (domain codomainLeft codomainRight : IntersectionType) :
    Subtype
      (IntersectionType.inter (IntersectionType.arrow domain codomainLeft)
        (IntersectionType.arrow domain codomainRight))
      (IntersectionType.arrow domain (IntersectionType.inter codomainLeft codomainRight)) :=
  Subtype.arrowDistributes domain codomainLeft codomainRight

/-! ## Filters -/

/-- A **filter** of intersection types: contains `omega`, is upward-closed under `≤`, and is closed under
`∩` — the points of the filter model. -/
structure IsFilter (member : IntersectionType → Prop) : Prop where
  /-- A filter contains the top. -/
  hasOmega : member IntersectionType.omega
  /-- A filter is upward-closed under subtyping. -/
  upwardClosed : ∀ {smaller larger : IntersectionType}, member smaller → Subtype smaller larger → member larger
  /-- A filter is closed under intersection. -/
  interClosed : ∀ {first second : IntersectionType},
    member first → member second → member (IntersectionType.inter first second)

/-- The **principal filter** of a type: everything above it. -/
def principalFilter (base : IntersectionType) : IntersectionType → Prop :=
  fun candidate => Subtype base candidate

/-- A principal filter is a filter. -/
theorem principalFilter_isFilter (base : IntersectionType) : IsFilter (principalFilter base) where
  hasOmega := Subtype.omegaTop base
  upwardClosed := fun baseBelow candidateBelow => Subtype.trans baseBelow candidateBelow
  interClosed := fun baseBelowFirst baseBelowSecond => Subtype.leInter baseBelowFirst baseBelowSecond

/-- The **least filter** `↑ω` — the principal filter of the top type. -/
def omegaFilter : IntersectionType → Prop := principalFilter IntersectionType.omega

/-- The omega filter is a filter. -/
theorem omegaFilter_isFilter : IsFilter omegaFilter := principalFilter_isFilter IntersectionType.omega

/-- ★ **The omega filter is the LEAST filter**: every filter contains it. -/
theorem omegaFilter_isLeast (member : IntersectionType → Prop) (isFilter : IsFilter member) :
    ∀ candidate, omegaFilter candidate → member candidate :=
  fun _ omegaBelow => isFilter.upwardClosed isFilter.hasOmega omegaBelow

/-- The principal-filter embedding is ORDER-REVERSING: a larger type yields a smaller filter. -/
theorem principalFilter_antitone {base base' : IntersectionType} (baseBelow : Subtype base base') :
    ∀ candidate, principalFilter base' candidate → principalFilter base candidate :=
  fun _ base'Below => Subtype.trans baseBelow base'Below

/-! ## The filter model is ω-complete (the domain preorder) -/

/-- Inclusion order on filters (`⊆`) — the information order of the filter model. -/
def FilterBelow (lower upper : IntersectionType → Prop) : Prop :=
  ∀ candidate, lower candidate → upper candidate

/-- `FilterBelow` is reflexive. -/
theorem filterBelow_refl (member : IntersectionType → Prop) : FilterBelow member member :=
  fun _ memberHolds => memberHolds

/-- `FilterBelow` is transitive. -/
theorem filterBelow_trans {lower middle upper : IntersectionType → Prop}
    (lowerBelow : FilterBelow lower middle) (middleBelow : FilterBelow middle upper) :
    FilterBelow lower upper :=
  fun candidate lowerHolds => middleBelow candidate (lowerBelow candidate lowerHolds)

/-- The **filter generated by a base set**: the smallest filter containing it (always a filter, by
construction). -/
inductive GeneratedFilter (base : IntersectionType → Prop) : IntersectionType → Prop where
  /-- It contains the top. -/
  | omega : GeneratedFilter base IntersectionType.omega
  /-- It contains the base set. -/
  | mem {subject : IntersectionType} : base subject → GeneratedFilter base subject
  /-- It is upward-closed. -/
  | upward {smaller larger : IntersectionType} :
      GeneratedFilter base smaller → Subtype smaller larger → GeneratedFilter base larger
  /-- It is intersection-closed. -/
  | interIntro {first second : IntersectionType} :
      GeneratedFilter base first → GeneratedFilter base second →
      GeneratedFilter base (IntersectionType.inter first second)

/-- A generated filter is a filter. -/
theorem generatedFilter_isFilter (base : IntersectionType → Prop) : IsFilter (GeneratedFilter base) where
  hasOmega := GeneratedFilter.omega
  upwardClosed := fun generated subtyping => GeneratedFilter.upward generated subtyping
  interClosed := fun generatedFirst generatedSecond => GeneratedFilter.interIntro generatedFirst generatedSecond

/-- Filter generation is MONOTONE in its base set. -/
theorem generatedFilter_monotone {base extendedBase : IntersectionType → Prop}
    (subset : ∀ candidate, base candidate → extendedBase candidate) :
    ∀ candidate, GeneratedFilter base candidate → GeneratedFilter extendedBase candidate := by
  intro candidate generated
  induction generated with
  | omega => exact GeneratedFilter.omega
  | mem baseHolds => exact GeneratedFilter.mem (subset _ baseHolds)
  | upward _generated subtyping inductionHypothesis => exact GeneratedFilter.upward inductionHypothesis subtyping
  | interIntro _first _second inductionFirst inductionSecond =>
      exact GeneratedFilter.interIntro inductionFirst inductionSecond

/-! ## Filter application — the λ-model operation -/

/-- **Filter application** (the filter λ-model's application): `function · argument` collects every result
`τ` such that some `σ` in the argument has `σ → τ` in the function, closed up to a filter. -/
def filterApply (function argument : IntersectionType → Prop) : IntersectionType → Prop :=
  GeneratedFilter
    (fun result => ∃ input, argument input ∧ function (IntersectionType.arrow input result))

/-- The application of two filters is a filter. -/
theorem filterApply_isFilter (function argument : IntersectionType → Prop) :
    IsFilter (filterApply function argument) :=
  generatedFilter_isFilter _

/-- ★ Filter application is MONOTONE in both arguments — the model's application is order-preserving. -/
theorem filterApply_monotone {function extendedFunction argument extendedArgument : IntersectionType → Prop}
    (functionSubset : ∀ candidate, function candidate → extendedFunction candidate)
    (argumentSubset : ∀ candidate, argument candidate → extendedArgument candidate) :
    ∀ candidate, filterApply function argument candidate → filterApply extendedFunction extendedArgument candidate := by
  apply generatedFilter_monotone
  intro result base
  obtain ⟨input, argumentHolds, functionHolds⟩ := base
  exact ⟨input, argumentSubset _ argumentHolds, functionSubset _ functionHolds⟩

/-- The **sup of a sequence of filters**: the filter generated by their union — the least upper bound. -/
def filterSup (sequence : Nat → IntersectionType → Prop) : IntersectionType → Prop :=
  GeneratedFilter (fun candidate => ∃ index, sequence index candidate)

/-- ★ The filter sup is an UPPER BOUND of the sequence. -/
theorem filterSup_isUpperBound (sequence : Nat → IntersectionType → Prop) (index : Nat) :
    FilterBelow (sequence index) (filterSup sequence) :=
  fun _ memberHolds => GeneratedFilter.mem ⟨index, memberHolds⟩

/-- ★ The filter sup is the LEAST upper bound: any filter above every element is above the sup.  Hence the
filter model is ω-complete (a pointed ω-complete preorder, with `omegaFilter` the bottom). -/
theorem filterSup_isLeast (sequence : Nat → IntersectionType → Prop)
    (upperBound : IntersectionType → Prop) (isFilter : IsFilter upperBound)
    (isAbove : ∀ index, FilterBelow (sequence index) upperBound) :
    FilterBelow (filterSup sequence) upperBound := by
  intro candidate generated
  induction generated with
  | omega => exact isFilter.hasOmega
  | mem baseHolds =>
      obtain ⟨index, sequenceHolds⟩ := baseHolds
      exact isAbove index _ sequenceHolds
  | upward _generated subtyping inductionHypothesis =>
      exact isFilter.upwardClosed inductionHypothesis subtyping
  | interIntro _generatedFirst _generatedSecond inductionFirst inductionSecond =>
      exact isFilter.interClosed inductionFirst inductionSecond

end FX1Poly.Core
