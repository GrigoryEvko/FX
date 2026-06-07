import FX1Poly.Tier0.RepresentableMapCategory

/-! # FX1Poly/Tier0/FxBaseRenamingVecCategory
    — the EXTENSIONAL data-morphism renaming category: the renaming base that finally proves lookup-extensionality

`FxBaseRenamingCategory.lean` reified a renaming `source ⟶ target` as the indexed inductive
`RenamingTo target source` (a length-`source` vector of `Fin target` images).  That base is a genuine zero-axiom
`RawCategory` whose laws are structural (no `funext`), but its docstring flags one trap it must AVOID:

> The one trap — `RenamingTo` lookup-extensionality (`r.lookup ≐ s.lookup → r = s`) — is AVOIDED: it requires a
> simultaneous two-renaming indexed match, which leaks `propext` through the impossible-case equation lemmas …

Lookup-extensionality is not a luxury — it is the load-bearing lemma the Tier-0 CwR pullback needs (the pullback's
universal property is proved by exhibiting two mediating morphisms with equal lookups and concluding they are
equal).  The indexed-inductive base cannot supply it zero-axiom, so the CwR ladder over `RenamingTo` dead-ends at
the pullback rung.

This file builds the base that CAN: `RenamingVec target source`, the SAME length-`source` tuple of `Fin target`
images, but reified as a PRODUCT recursion (`RenamingVec target 0 = PUnit`,
`RenamingVec target (source+1) = Fin target × RenamingVec target source`) rather than an indexed inductive.
Products have DEFINITIONAL eta, so `ext` falls out of a clean structural induction with NO impossible-case
equation lemmas and NO `propext` — the exact lemma `RenamingTo` could not prove.  Everything else (`lookup`,
`mapImages`, `compose`, `identity`, the three category laws, the display/weakening map) ports across unchanged,
and the category `fxBaseRenamingVecCategory` is again a genuine zero-axiom `RawCategory`.

## What lands here (all zero-axiom)

  * `RenamingVec target source` — the renaming reified as a PRODUCT-recursive vector (`PUnit` / `Fin target × …`).
  * `RenamingVec.lookup` (+ `lookup_zero` / `lookup_succ`) — the variable-reindexing function it denotes.
  * **`RenamingVec.ext` — lookup-extensionality, for free.**  Two vectors with equal lookups are equal, by
    induction on `source` with product eta at every successor step.  THE lemma `RenamingTo` could not prove.
  * `RenamingVec.mapImages` / `lookup_mapImages` / `compose` / `lookup_compose` — the structural algebra and the
    faithful-reification bridge (`lookup` carries composition to function composition pointwise).
  * `RenamingVec.identity` (+ `identity_lookup`) and the three category laws `compose_assoc` / `identity_compose`
    / `compose_identity` — here proved DIRECTLY via `ext` (pointwise through `lookup_compose` + `identity_lookup`),
    a route the extensional base makes trivial.
  * `RenamingVec.weakening` (+ `weakening_lookup` / `identity_succ_eq`) — the display / context-projection
    morphism `scope ⟶ scope+1`, the representable-map candidate for the eventual CwR class.
  * **`RenamingVec.weakening_unique`** — the display map is UNIQUELY characterized by its action (`lookup =
    shiftImage`).  An `ext`-powered uniqueness the `RenamingTo` base cannot state; the shape the CwR
    representable-map axioms need (canonical display morphisms are unique).
  * `fxBaseRenamingVecCategory` — the assembled `RawCategory`; `_identity_eq` / `_compose_eq` the defeq samples,
    and **`fxBaseRenamingVecCategory_faithful`** the category-level restatement of `ext` (lookup determines the
    morphism — the reification onto the function-morphism world is faithful, zero-axiom).

## Relationship to `FxBaseRenamingCategory` (additive, no deletion)

This is PURELY ADDITIVE: `RenamingTo` and `fxBaseRenamingCategory` are retained untouched.  `RenamingVec` is the
strictly-more-capable sibling (same morphism content, plus extensionality).  Consolidating the CwR pipeline onto
`RenamingVec` and retiring `RenamingTo` is a deletion, deferred to an explicit decision; both bases coexist for
now, with this one carrying the extensional content the pullback rung requires.

## Honest scope boundary

This lands the EXTENSIONAL `underlying`-category base of `fxBaseRMC` — a genuine zero-axiom `RawCategory` whose
morphisms carry real renaming content AND whose lookup determines the morphism (`ext` / faithfulness).  It is NOT
yet the full `RepresentableMapCategory`: that still needs (a) the representable-map class (the display maps
`weakening` are the candidates) and (b) the three CwR axioms over THIS base.  The pullback construction — the rung
`RenamingTo` could not reach for want of `ext` — is now POSSIBLE here; it is the next task, deferred.

## Zero-axiom verification

A product-recursive morphism family plus structural-induction proofs.  `ext` uses `PUnit` proof irrelevance at the
base and `Prod.ext` (definitional product eta) at each successor — no impossible-case equation lemma, no
`propext`.  The category laws go through `ext` pointwise (`lookup_compose` + `identity_lookup`), avoiding the
fusion gymnastics the non-extensional base needed.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- A renaming `source ⟶ target` reified as a PRODUCT-recursive vector (NOT an indexed inductive): the
length-`source` tuple of `Fin target` images.  Because products have DEFINITIONAL eta, this foundation gets
lookup-extensionality for free, unlike the indexed inductive `RenamingTo`. -/
def RenamingVec (target : Nat) : Nat → Type
  | 0 => PUnit
  | source + 1 => Fin target × RenamingVec target source

/-- The variable-reindexing function the vector denotes. -/
def RenamingVec.lookup {target : Nat} :
    {source : Nat} → RenamingVec target source → Fin source → Fin target
  | 0, _vec, index => index.elim0
  | _source + 1, vec, ⟨0, _⟩ => vec.1
  | _source + 1, vec, ⟨position + 1, isLt⟩ => vec.2.lookup ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- Looking up the freshly-bound variable 0 returns the head image. -/
theorem RenamingVec.lookup_zero {target source : Nat} (vec : RenamingVec target (source + 1))
    (isLt : 0 < source + 1) : vec.lookup ⟨0, isLt⟩ = vec.1 := rfl

/-- Looking up a successor variable recurses into the tail. -/
theorem RenamingVec.lookup_succ {target source : Nat} (vec : RenamingVec target (source + 1))
    (position : Nat) (isLt : position + 1 < source + 1) :
    vec.lookup ⟨position + 1, isLt⟩ = vec.2.lookup ⟨position, Nat.lt_of_succ_lt_succ isLt⟩ := rfl

/-- **Lookup-extensionality, for free.**  Two vectors with the same lookup are equal — by induction on `source`,
with product eta at every successor step (the `nil` case is `PUnit` proof irrelevance).  This is the exact lemma
the indexed-inductive `RenamingTo` could NOT prove zero-axiom. -/
theorem RenamingVec.ext {target : Nat} :
    {source : Nat} → (vecA vecB : RenamingVec target source) →
      (∀ index : Fin source, vecA.lookup index = vecB.lookup index) → vecA = vecB
  | 0, PUnit.unit, PUnit.unit, _ => rfl
  | source + 1, vecA, vecB, pointwise => by
      have headEqual : vecA.1 = vecB.1 := pointwise ⟨0, Nat.succ_pos source⟩
      have tailEqual : vecA.2 = vecB.2 :=
        RenamingVec.ext vecA.2 vecB.2
          (fun index => pointwise ⟨index.val + 1, Nat.succ_lt_succ index.isLt⟩)
      exact Prod.ext headEqual tailEqual

/-- Post-compose every stored image with `mapping` (the functorial action on the target). -/
def RenamingVec.mapImages {target targetNext : Nat} (mapping : Fin target → Fin targetNext) :
    {source : Nat} → RenamingVec target source → RenamingVec targetNext source
  | 0, _vec => PUnit.unit
  | _source + 1, vec => (mapping vec.1, mapImages mapping vec.2)

/-- Looking up through a remapped renaming is the remap of the lookup. -/
theorem RenamingVec.lookup_mapImages {target targetNext : Nat} (mapping : Fin target → Fin targetNext) :
    {source : Nat} → (vec : RenamingVec target source) → (index : Fin source) →
      (vec.mapImages mapping).lookup index = mapping (vec.lookup index)
  | 0, _vec, index => index.elim0
  | _source + 1, _vec, ⟨0, _⟩ => rfl
  | _source + 1, vec, ⟨position + 1, isLt⟩ =>
      lookup_mapImages mapping vec.2 ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- Renaming composition (`source ⟶ mid` then `mid ⟶ target`) by mapping the first renaming's images through
the second's lookup. -/
def RenamingVec.compose {sourceScope midScope targetScope : Nat}
    (firstRenaming : RenamingVec midScope sourceScope)
    (secondRenaming : RenamingVec targetScope midScope) : RenamingVec targetScope sourceScope :=
  firstRenaming.mapImages secondRenaming.lookup

/-- **`lookup` is a functor to the function-morphism category.**  The lookup of a composition is the function
composition of the lookups (pointwise) — the faithful-reification bridge from this DATA category onto the
function-renaming world. -/
theorem RenamingVec.lookup_compose {sourceScope midScope targetScope : Nat}
    (firstRenaming : RenamingVec midScope sourceScope)
    (secondRenaming : RenamingVec targetScope midScope) (index : Fin sourceScope) :
    (firstRenaming.compose secondRenaming).lookup index =
      secondRenaming.lookup (firstRenaming.lookup index) :=
  RenamingVec.lookup_mapImages secondRenaming.lookup firstRenaming index

/-- Shift every image up by one (the target-bump used to build the identity recursively). -/
def RenamingVec.shiftImage {scope : Nat} (image : Fin scope) : Fin (scope + 1) :=
  ⟨image.val + 1, Nat.succ_lt_succ image.isLt⟩

/-- The identity data renaming `scope ⟶ scope` (head is variable 0, tail is the shift of the smaller identity). -/
def RenamingVec.identity : (scope : Nat) → RenamingVec scope scope
  | 0 => PUnit.unit
  | scope + 1 => (⟨0, Nat.succ_pos scope⟩, (RenamingVec.identity scope).mapImages RenamingVec.shiftImage)

/-- The identity data renaming looks up to the identity reindexing. -/
theorem RenamingVec.identity_lookup :
    (scope : Nat) → (index : Fin scope) → (RenamingVec.identity scope).lookup index = index
  | _scope + 1, ⟨0, _⟩ => rfl
  | scope + 1, ⟨position + 1, isLt⟩ => by
      show ((RenamingVec.identity scope).mapImages RenamingVec.shiftImage).lookup
          ⟨position, Nat.lt_of_succ_lt_succ isLt⟩ = ⟨position + 1, isLt⟩
      rw [lookup_mapImages, identity_lookup scope ⟨position, Nat.lt_of_succ_lt_succ isLt⟩]
      rfl

/-- **Associativity of renaming composition — via `ext`.**  Both sides have the same lookup at every index (a
pointwise `lookup_compose` chain), so extensionality concludes equality directly — no `mapImages` fusion. -/
theorem RenamingVec.compose_assoc {scopeA scopeB scopeC scopeD : Nat}
    (firstRenaming : RenamingVec scopeB scopeA) (secondRenaming : RenamingVec scopeC scopeB)
    (thirdRenaming : RenamingVec scopeD scopeC) :
    (firstRenaming.compose secondRenaming).compose thirdRenaming =
      firstRenaming.compose (secondRenaming.compose thirdRenaming) :=
  RenamingVec.ext _ _ (fun index =>
    calc ((firstRenaming.compose secondRenaming).compose thirdRenaming).lookup index
        = thirdRenaming.lookup ((firstRenaming.compose secondRenaming).lookup index) :=
          lookup_compose _ _ index
      _ = thirdRenaming.lookup (secondRenaming.lookup (firstRenaming.lookup index)) := by
          rw [lookup_compose]
      _ = (secondRenaming.compose thirdRenaming).lookup (firstRenaming.lookup index) :=
          (lookup_compose _ _ _).symm
      _ = (firstRenaming.compose (secondRenaming.compose thirdRenaming)).lookup index :=
          (lookup_compose _ _ index).symm)

/-- **Left identity law — via `ext`.**  The composition's lookup is `lookup ∘ identity_lookup = lookup`. -/
theorem RenamingVec.identity_compose {targetScope sourceScope : Nat}
    (dataRenaming : RenamingVec targetScope sourceScope) :
    (RenamingVec.identity sourceScope).compose dataRenaming = dataRenaming :=
  RenamingVec.ext _ _ (fun index => by rw [lookup_compose, identity_lookup])

/-- **Right identity law — via `ext`.**  The composition's lookup is `identity_lookup ∘ lookup = lookup`. -/
theorem RenamingVec.compose_identity {sourceScope targetScope : Nat}
    (dataRenaming : RenamingVec targetScope sourceScope) :
    dataRenaming.compose (RenamingVec.identity targetScope) = dataRenaming :=
  RenamingVec.ext _ _ (fun index => by rw [lookup_compose, identity_lookup])

/-- **The display / weakening renaming `scope ⟶ scope + 1`.**  Shifts every variable past the freshly-bound
variable 0 — the canonical context-PROJECTION morphism, the representable-map candidate for the eventual CwR
representable-map class over `fxBaseRenamingVecCategory`. -/
def RenamingVec.weakening (scope : Nat) : RenamingVec (scope + 1) scope :=
  (RenamingVec.identity scope).mapImages RenamingVec.shiftImage

/-- The weakening renaming reindexes every variable to its successor (`shiftImage`). -/
theorem RenamingVec.weakening_lookup (scope : Nat) (index : Fin scope) :
    (RenamingVec.weakening scope).lookup index = RenamingVec.shiftImage index := by
  show ((RenamingVec.identity scope).mapImages RenamingVec.shiftImage).lookup index =
    RenamingVec.shiftImage index
  rw [lookup_mapImages, identity_lookup scope index]

/-- The successor identity decomposes as `(var0, weakening scope)` — the identity keeps the freshly-bound
variable 0 fixed and weakens (shifts) the rest.  Definitional, exhibiting the weakening as the identity's tail. -/
theorem RenamingVec.identity_succ_eq (scope : Nat) :
    RenamingVec.identity (scope + 1) =
      (⟨0, Nat.succ_pos scope⟩, RenamingVec.weakening scope) := rfl

/-- **The display map is UNIQUELY characterized by its action — `ext`-powered.**  Any morphism `scope ⟶ scope+1`
whose lookup is the shift IS the weakening.  This uniqueness is exactly what the CwR representable-map axioms need
(the canonical display morphism is unique); it is unstatable over the non-extensional `RenamingTo` base. -/
theorem RenamingVec.weakening_unique (scope : Nat)
    (candidate : RenamingVec (scope + 1) scope)
    (actsAsShift : ∀ index, candidate.lookup index = RenamingVec.shiftImage index) :
    candidate = RenamingVec.weakening scope :=
  RenamingVec.ext candidate (RenamingVec.weakening scope)
    (fun index => (actsAsShift index).trans (RenamingVec.weakening_lookup scope index).symm)

/-- **The EXTENSIONAL DATA-morphism FX renaming category.**  Objects are scopes (`Nat`), morphisms
`source ⟶ target` are product-recursive renamings (`RenamingVec target source`).  All three category laws hold
via `ext` (pointwise `lookup_compose` / `identity_lookup`).  Unlike the indexed-inductive `fxBaseRenamingCategory`,
this base proves lookup-extensionality (`ext` / `faithful`), so the CwR pullback rung — whose universal property
needs morphism equality from pointwise-equal lookups — becomes provable over it. -/
def fxBaseRenamingVecCategory : RawCategory.{0, 0} where
  Object := Nat
  Morphism := fun sourceScope targetScope => RenamingVec targetScope sourceScope
  identity := fun scope => RenamingVec.identity scope
  compose := fun firstRenaming secondRenaming => firstRenaming.compose secondRenaming
  composeAssoc := fun firstRenaming secondRenaming thirdRenaming =>
    RenamingVec.compose_assoc firstRenaming secondRenaming thirdRenaming
  identityLeft := fun morphism => RenamingVec.identity_compose morphism
  identityRight := fun morphism => RenamingVec.compose_identity morphism

/-- The categorical identity of `fxBaseRenamingVecCategory` IS the identity data renaming. -/
theorem fxBaseRenamingVecCategory_identity_eq {scope : Nat} :
    fxBaseRenamingVecCategory.identity scope = RenamingVec.identity scope := rfl

/-- The categorical composition of `fxBaseRenamingVecCategory` IS data-renaming composition. -/
theorem fxBaseRenamingVecCategory_compose_eq {scopeA scopeB scopeC : Nat}
    (firstRenaming : RenamingVec scopeB scopeA) (secondRenaming : RenamingVec scopeC scopeB) :
    fxBaseRenamingVecCategory.compose firstRenaming secondRenaming =
      firstRenaming.compose secondRenaming := rfl

/-- **The reification onto the function-morphism world is FAITHFUL — `ext` at the category level.**  Two parallel
morphisms with equal lookups are equal.  The function-morphism renaming category has this trivially (its morphisms
ARE functions); the indexed-inductive data base could not prove it zero-axiom; this extensional data base does. -/
theorem fxBaseRenamingVecCategory_faithful {sourceScope targetScope : Nat}
    (firstRenaming secondRenaming : RenamingVec targetScope sourceScope)
    (pointwise : ∀ index, firstRenaming.lookup index = secondRenaming.lookup index) :
    firstRenaming = secondRenaming :=
  RenamingVec.ext firstRenaming secondRenaming pointwise

end FX1Poly.Tier0
