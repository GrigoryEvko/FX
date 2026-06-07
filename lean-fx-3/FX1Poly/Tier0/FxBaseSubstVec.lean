import FX1Poly.Core.RawTermSubstDefs

/-! # FX1Poly/Tier0/FxBaseSubstVec
    — the EXTENSIONAL substitution representation: the first brick of the TERM-CARRYING CwR base

The Tier-0 sconing-transfer ladder (SN-086 Tm↠Ty display map, SN-088 Uemura bijection, SN-091 Π/Σ/universe
lift, SN-093..096 the BKS extraction ledgers) needs a CwR base whose objects carry TYPES and morphisms carry
TERMS — the SYNTACTIC category of contexts-and-substitutions.  The renaming base `fxBaseRenamingVecCategory`
(closed by SN-084/085/085a) is purely structural: its morphisms are variable renamings, which carry no term
content, so the sconing ladder dead-ends there.  This file is the FIRST brick of the term-carrying replacement.

The existing substitution type is `RawTermSubst source target := Fin source → RawTerm target` — FUNCTION-typed.
A category over it cannot prove morphism EXTENSIONALITY (`(∀ i, s1 i = s2 i) → s1 = s2`) zero-axiom: that IS
`funext`, which leaks `Quot.sound`.  This is the EXACT trap the `RenamingVec` arc solved for renamings (the
indexed/function renaming could not prove lookup-extensionality; the product-recursive `RenamingVec` could, via
definitional product eta).  `SubstVec` is the substitution analogue: the same length-`source` tuple, but of
`RawTerm target` payloads, reified as a PRODUCT recursion (`SubstVec target 0 = PUnit`,
`SubstVec target (source+1) = RawTerm target × SubstVec target source`).  Products have definitional eta, so
`ext` falls out of a clean structural induction with NO `funext` — the lemma the CwR pullback rung will need.

## What lands here (all zero-axiom)

  * `SubstVec target source` — a substitution `source ⟶ target` reified as a product-recursive vector of
    `RawTerm target` (NOT a function).
  * `SubstVec.lookup` (+ `lookup_zero` / `lookup_succ`) — the substitution function the vector denotes.
  * **`SubstVec.ext` — substitution extensionality, for free.**  Two vectors with equal lookups are equal, by
    induction on `source` with product eta at every successor step.  THE lemma the function-typed `RawTermSubst`
    cannot prove zero-axiom.
  * `SubstVec.tabulate` — build a `SubstVec` from any function `Fin source → RawTerm target` (i.e. from a
    `RawTermSubst`).  The reverse of `lookup`.
  * `SubstVec.lookup_tabulate` — `(tabulate f).lookup index = f index` (the function round-trips through
    `tabulate`, stated POINTWISE — the function-equality form would need `funext`).
  * `SubstVec.tabulate_lookup` — `tabulate vec.lookup = vec` (the vector round-trips, via `ext`, zero-axiom).
  * `SubstVec.toRawTermSubst` (+ `toRawTermSubst_tabulate`) — the bridge: a `SubstVec` IS a `RawTermSubst` (its
    `lookup` is exactly the function form).  Together with `tabulate` this exhibits the iso
    `SubstVec ≅ RawTermSubst` — the extensional and function representations agree, with the vec→function→vec
    round-trip zero-axiom (the point: `SubstVec` adds the extensionality `RawTermSubst`-as-functions lacks).

## Honest scope boundary

This is the SUBSTRATE only — the extensional substitution representation + its bridge to `RawTermSubst`.  It is
NOT yet the substitution CATEGORY: that needs the identity substitution, substitution COMPOSITION (harder than
renaming composition — it requires the `RawTerm.subst` action and the substitution lemmas, which exist but must
be lifted onto `SubstVec`), and the three category laws via `ext`.  The assembled `RawCategory`, the
representable-map class, the CwR axioms, and the sconing instances are the LATER bricks of this multi-firing arc
(the term-carrying analogue of the 6-firing `RenamingVec` arc).  Like that arc, every brick stays green and
zero-axiom.

## Relationship to `RawTermSubst` (additive, no deletion)

Purely additive: `RawTermSubst` and its function-based substitution algebra are retained untouched.  `SubstVec`
is the strictly-more-capable sibling (same substitution content via `lookup` / `tabulate`, plus extensionality).

## Zero-axiom verification

A product-recursive term-tuple plus structural-induction proofs ported near-verbatim from the `RenamingVec`
substrate.  `ext` uses `PUnit` proof irrelevance at the base and `Prod.ext` (definitional product eta) at each
successor; the round-trips are structural induction over `source` + index.  No `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-- A substitution `source ⟶ target` reified as a PRODUCT-recursive vector (NOT a function): the length-`source`
tuple of `RawTerm target` images.  Because products have definitional eta, this gets substitution-extensionality
for free, unlike the function-typed `RawTermSubst`. -/
def SubstVec (target : Nat) : Nat → Type
  | 0 => PUnit
  | source + 1 => RawTerm target × SubstVec target source

/-- The substitution function the vector denotes. -/
def SubstVec.lookup {target : Nat} :
    {source : Nat} → SubstVec target source → Fin source → RawTerm target
  | 0, _vec, index => index.elim0
  | _source + 1, vec, ⟨0, _⟩ => vec.1
  | _source + 1, vec, ⟨position + 1, isLt⟩ => vec.2.lookup ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- Looking up the freshly-bound variable 0 returns the head image. -/
theorem SubstVec.lookup_zero {target source : Nat} (vec : SubstVec target (source + 1))
    (isLt : 0 < source + 1) : vec.lookup ⟨0, isLt⟩ = vec.1 := rfl

/-- Looking up a successor variable recurses into the tail. -/
theorem SubstVec.lookup_succ {target source : Nat} (vec : SubstVec target (source + 1))
    (position : Nat) (isLt : position + 1 < source + 1) :
    vec.lookup ⟨position + 1, isLt⟩ = vec.2.lookup ⟨position, Nat.lt_of_succ_lt_succ isLt⟩ := rfl

/-- **Substitution-extensionality, for free.**  Two vectors with the same lookup are equal — by induction on
`source`, with product eta at every successor step (the `nil` case is `PUnit` proof irrelevance).  This is the
exact lemma the function-typed `RawTermSubst` cannot prove zero-axiom (it would be `funext`). -/
theorem SubstVec.ext {target : Nat} :
    {source : Nat} → (vecA vecB : SubstVec target source) →
      (∀ index : Fin source, vecA.lookup index = vecB.lookup index) → vecA = vecB
  | 0, PUnit.unit, PUnit.unit, _ => rfl
  | source + 1, vecA, vecB, pointwise => by
      have headEqual : vecA.1 = vecB.1 := pointwise ⟨0, Nat.succ_pos source⟩
      have tailEqual : vecA.2 = vecB.2 :=
        SubstVec.ext vecA.2 vecB.2
          (fun index => pointwise ⟨index.val + 1, Nat.succ_lt_succ index.isLt⟩)
      exact Prod.ext headEqual tailEqual

/-- Build a `SubstVec` from any function `Fin source → RawTerm target` (i.e. from a `RawTermSubst`) — the reverse
of `lookup`. -/
def SubstVec.tabulate {target : Nat} :
    {source : Nat} → (Fin source → RawTerm target) → SubstVec target source
  | 0, _imageOf => PUnit.unit
  | _source + 1, imageOf =>
      (imageOf ⟨0, Nat.succ_pos _⟩,
        SubstVec.tabulate (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩))

/-- The tabulated vector looks up to the original function (POINTWISE — the function-equality form would need
`funext`). -/
theorem SubstVec.lookup_tabulate {target : Nat} :
    {source : Nat} → (imageOf : Fin source → RawTerm target) → (index : Fin source) →
      (SubstVec.tabulate imageOf).lookup index = imageOf index
  | 0, _imageOf, index => index.elim0
  | _source + 1, _imageOf, ⟨0, _⟩ => rfl
  | _source + 1, imageOf, ⟨position + 1, isLt⟩ =>
      SubstVec.lookup_tabulate
        (fun position => imageOf ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩)
        ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- Tabulating a vector's own lookup returns the vector — the vec round-trip, via `ext` (zero-axiom; the point of
`SubstVec` is exactly the extensionality the function form lacks). -/
theorem SubstVec.tabulate_lookup {target source : Nat} (vec : SubstVec target source) :
    SubstVec.tabulate vec.lookup = vec :=
  SubstVec.ext _ _ (fun index => SubstVec.lookup_tabulate vec.lookup index)

/-- **The bridge: a `SubstVec` IS a `RawTermSubst`.**  Its `lookup` is exactly the function form of the
substitution. -/
def SubstVec.toRawTermSubst {target source : Nat} (vec : SubstVec target source) :
    RawTermSubst source target :=
  vec.lookup

/-- The bridge round-trips with `tabulate` (pointwise): the `RawTermSubst` of a tabulated function is that
function. -/
theorem SubstVec.toRawTermSubst_tabulate {target source : Nat}
    (someSubst : RawTermSubst source target) (index : Fin source) :
    (SubstVec.tabulate someSubst).toRawTermSubst index = someSubst index :=
  SubstVec.lookup_tabulate someSubst index

end FX1Poly.Tier0
