import FX1Poly.Tier0.RepresentableMapCategory

/-! # FX1Poly/Tier0/FxBaseRenamingCategory
    — the DATA-morphism renaming category: the zero-axiom base the function-morphism category cannot be

The function-morphism renaming category `fxRenamingCategory` (`FxRenamingCategory.lean`) is a genuine
`RawCategory`, but it is a DEAD END for the Tier-0 CwR pipeline: its morphisms `source ⟶ target` are bare
functions `Fin source → Fin target`, so EVERY downstream CwR equality (pullback commutes / is universal, the
iso inverse laws, the representable-map closure squares) is a FUNCTION equality, and a function equality needs
`funext`, which pulls `Quot.sound`.  The thin-scope RMC (`FxThinScopeRMC.lean`) escapes this by going degenerate
— a preorder base where morphisms are `Prop`-proofs, so proof irrelevance makes every morphism equality free —
but that throws away the actual renaming content.  Neither base can host the genuine renaming/substitution CwR
zero-axiom.

This file builds the missing base: `fxBaseRenamingCategory`, where a renaming `source ⟶ target` is reified as
DATA — `RenamingTo target source`, the length-`source` vector of `Fin target` images.  Because morphisms are now
an inductive family (a vector), morphism equality is STRUCTURAL: the three category laws hold by induction over
the vector, no `funext` anywhere.  This is the data-morphism base the `FxThinScopeRMC` docstring flagged as
"needs a DATA-morphism base (renamings reified as vectors), a larger refactor deferred" — landed here as the
purely-additive first brick, leaving the existing function-morphism and thin bases untouched.

## What lands here (all zero-axiom)

  * `RenamingTo target source` — a renaming `source ⟶ target` reified as a length-`source` vector of images.
  * `RenamingTo.lookup` — the variable-reindexing FUNCTION (`Fin source → Fin target`) the data renaming denotes;
    the faithful bridge to the function-morphism world (`RawRenaming`).
  * `RenamingTo.mapImages` / `compose` — functorial post-composition on images, and renaming composition built
    from it (`compose r s := r.mapImages s.lookup`).
  * `mapImages_mapImages` (fusion), `lookup_mapImages`, `mapImages_congr`, `mapImages_id` — the structural algebra.
  * `compose_assoc` — associativity, STRUCTURALLY (via fusion + `lookup_mapImages`), not by `funext`.
  * `lookup_compose` — `lookup` is a FUNCTOR to the function category: it carries composition to function
    composition pointwise (the faithful-reification bridge: this data category maps onto `fxRenamingCategory`).
  * `identity` + `identity_lookup` / `identity_compose` / `compose_identity` — the identity renaming and its three
    laws, all by structural induction.
  * `fxBaseRenamingCategory` — the `RawCategory` assembled from the above; `_identity_eq` / `_compose_eq` the
    defeq samples connecting the category fields to the renaming operations.

## Honest scope boundary

This lands the `underlying`-category data-morphism base of `fxBaseRMC` — a complete, genuine, zero-axiom
`RawCategory` whose morphisms carry real renaming content (unlike the thin base) AND whose laws are structural
(unlike the function base).  It is NOT yet the full `RepresentableMapCategory`: that still needs (a) the
representable-map class and (b) the three CwR axioms (closed under pullback with universal property, isomorphisms
representable, closed under composition) over THIS base.  The pullback construction in particular — now expressible
structurally, since morphisms are data — is the next rung, deferred.  So this is the brick that makes a zero-axiom
renaming RMC POSSIBLE; it is not itself that RMC.

## Zero-axiom verification

An inductive morphism family plus structural-induction proofs of the algebra and the three category laws.  The
one trap — `RenamingTo` lookup-extensionality (`r.lookup ≐ s.lookup → r = s`) — is AVOIDED: it requires a
simultaneous two-renaming indexed match, which leaks `propext` through the impossible-case equation lemmas; the
category laws are proved WITHOUT it (`identity_compose` binds the cons subscope via `@RenamingTo.cons _ source …`
rather than matching the `Nat` index as `source + 1`, dodging the cons-index `propext` trap).  No `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- A renaming `source ⟶ target` reified as DATA: the length-`source` vector of images (each a `Fin target`). -/
inductive RenamingTo (target : Nat) : Nat → Type where
  | nil : RenamingTo target 0
  | cons {source : Nat} (image : Fin target) (rest : RenamingTo target source) :
      RenamingTo target (source + 1)

/-- The variable-reindexing function a data renaming represents — the faithful bridge to `RawRenaming`. -/
def RenamingTo.lookup {target : Nat} :
    {source : Nat} → RenamingTo target source → Fin source → Fin target
  | _, .cons image _, ⟨0, _⟩ => image
  | _, .cons _ rest, ⟨index + 1, indexBound⟩ =>
      rest.lookup ⟨index, Nat.lt_of_succ_lt_succ indexBound⟩

/-- Post-compose every stored image with `mapping` (the functorial action on the target). -/
def RenamingTo.mapImages {target targetNext : Nat} (mapping : Fin target → Fin targetNext) :
    {source : Nat} → RenamingTo target source → RenamingTo targetNext source
  | _, .nil => .nil
  | _, .cons image rest => .cons (mapping image) (rest.mapImages mapping)

/-- Renaming composition (`source ⟶ mid` then `mid ⟶ target`) by mapping the first renaming's images through
the second's lookup. -/
def RenamingTo.compose {sourceScope midScope targetScope : Nat}
    (firstRenaming : RenamingTo midScope sourceScope)
    (secondRenaming : RenamingTo targetScope midScope) : RenamingTo targetScope sourceScope :=
  firstRenaming.mapImages secondRenaming.lookup

/-- `mapImages` fusion: two successive image-remaps collapse to one. -/
theorem RenamingTo.mapImages_mapImages {target targetNext targetNextNext : Nat}
    (firstMapping : Fin target → Fin targetNext) (secondMapping : Fin targetNext → Fin targetNextNext) :
    {source : Nat} → (dataRenaming : RenamingTo target source) →
      (dataRenaming.mapImages firstMapping).mapImages secondMapping =
        dataRenaming.mapImages (fun image => secondMapping (firstMapping image))
  | _, .nil => rfl
  | _, .cons _image rest =>
      congrArg (RenamingTo.cons _) (mapImages_mapImages firstMapping secondMapping rest)

/-- Looking up through a remapped renaming is the remap of the lookup. -/
theorem RenamingTo.lookup_mapImages {target targetNext : Nat} (mapping : Fin target → Fin targetNext) :
    {source : Nat} → (dataRenaming : RenamingTo target source) → (index : Fin source) →
      (dataRenaming.mapImages mapping).lookup index = mapping (dataRenaming.lookup index)
  | _, .cons _image _rest, ⟨0, _⟩ => rfl
  | _, .cons _image rest, ⟨index + 1, indexBound⟩ =>
      lookup_mapImages mapping rest ⟨index, Nat.lt_of_succ_lt_succ indexBound⟩

/-- `mapImages` respects pointwise equality of the image mapping. -/
theorem RenamingTo.mapImages_congr {target targetNext : Nat} {firstMapping secondMapping : Fin target → Fin targetNext}
    (pointwise : ∀ image, firstMapping image = secondMapping image) :
    {source : Nat} → (dataRenaming : RenamingTo target source) →
      dataRenaming.mapImages firstMapping = dataRenaming.mapImages secondMapping
  | _, .nil => rfl
  | _, .cons image rest => by
      show RenamingTo.cons (firstMapping image) (rest.mapImages firstMapping) =
        RenamingTo.cons (secondMapping image) (rest.mapImages secondMapping)
      rw [pointwise image, mapImages_congr pointwise rest]

/-- Mapping images through the identity leaves a renaming unchanged. -/
theorem RenamingTo.mapImages_id {target : Nat} :
    {source : Nat} → (dataRenaming : RenamingTo target source) →
      dataRenaming.mapImages (fun image => image) = dataRenaming
  | _, .nil => rfl
  | _, .cons image rest => by
      show RenamingTo.cons image (rest.mapImages (fun image => image)) = RenamingTo.cons image rest
      rw [mapImages_id rest]

/-- **Associativity of renaming composition — STRUCTURALLY, no `funext`.**  Both sides reassociate the three
image-remaps; `mapImages` fusion and `lookup_mapImages` collapse them to the same vector. -/
theorem RenamingTo.compose_assoc {scopeA scopeB scopeC scopeD : Nat}
    (firstRenaming : RenamingTo scopeB scopeA) (secondRenaming : RenamingTo scopeC scopeB)
    (thirdRenaming : RenamingTo scopeD scopeC) :
    (firstRenaming.compose secondRenaming).compose thirdRenaming =
      firstRenaming.compose (secondRenaming.compose thirdRenaming) := by
  show (firstRenaming.mapImages secondRenaming.lookup).mapImages thirdRenaming.lookup =
    firstRenaming.mapImages (secondRenaming.mapImages thirdRenaming.lookup).lookup
  rw [mapImages_mapImages]
  exact RenamingTo.mapImages_congr
    (fun image => (lookup_mapImages thirdRenaming.lookup secondRenaming image).symm) firstRenaming

/-- **`lookup` is a functor to the function-morphism category.**  The lookup of a composition is the function
composition of the lookups (pointwise) — the faithful-reification bridge from this DATA category onto the
function-renaming world `fxRenamingCategory` (`RawRenaming = Fin source → Fin target`). -/
theorem RenamingTo.lookup_compose {sourceScope midScope targetScope : Nat}
    (firstRenaming : RenamingTo midScope sourceScope)
    (secondRenaming : RenamingTo targetScope midScope) (index : Fin sourceScope) :
    (firstRenaming.compose secondRenaming).lookup index =
      secondRenaming.lookup (firstRenaming.lookup index) :=
  RenamingTo.lookup_mapImages secondRenaming.lookup firstRenaming index

/-- Shift every image up by one (the target-bump used to build the identity recursively). -/
def RenamingTo.shiftImage {scope : Nat} (image : Fin scope) : Fin (scope + 1) :=
  ⟨image.val + 1, Nat.succ_lt_succ image.isLt⟩

/-- The identity data renaming `scope ⟶ scope` (head is variable 0, tail is the shift of the smaller identity). -/
def RenamingTo.identity : (scope : Nat) → RenamingTo scope scope
  | 0 => .nil
  | scope + 1 => .cons ⟨0, Nat.succ_pos scope⟩ ((RenamingTo.identity scope).mapImages RenamingTo.shiftImage)

/-- The identity data renaming looks up to the identity reindexing. -/
theorem RenamingTo.identity_lookup :
    (scope : Nat) → (index : Fin scope) → (RenamingTo.identity scope).lookup index = index
  | _ + 1, ⟨0, _⟩ => rfl
  | scope + 1, ⟨index + 1, indexBound⟩ => by
      show ((RenamingTo.identity scope).mapImages RenamingTo.shiftImage).lookup
          ⟨index, Nat.lt_of_succ_lt_succ indexBound⟩ = ⟨index + 1, indexBound⟩
      rw [lookup_mapImages, identity_lookup scope ⟨index, Nat.lt_of_succ_lt_succ indexBound⟩]
      rfl

/-- **Left identity law — structural induction, no `propext`.**  The recursive cons case binds the subscope via
`@RenamingTo.cons _ source …` (NOT a `source + 1` index match), dodging the cons-index `propext` trap; the tail
reconstructs through `mapImages` fusion and the inductive hypothesis. -/
theorem RenamingTo.identity_compose {targetScope : Nat} :
    {sourceScope : Nat} → (dataRenaming : RenamingTo targetScope sourceScope) →
      (RenamingTo.identity sourceScope).compose dataRenaming = dataRenaming
  | _, .nil => rfl
  | _, @RenamingTo.cons _ source headImage restRenaming => by
      show RenamingTo.cons headImage
          (((RenamingTo.identity source).mapImages RenamingTo.shiftImage).mapImages
            (RenamingTo.cons headImage restRenaming).lookup) = RenamingTo.cons headImage restRenaming
      rw [mapImages_mapImages]
      have tailReconstructs : (RenamingTo.identity source).mapImages
          (fun image => (RenamingTo.cons headImage restRenaming).lookup (RenamingTo.shiftImage image)) =
            restRenaming :=
        (RenamingTo.mapImages_congr (fun _image => rfl) (RenamingTo.identity source)).trans
          (RenamingTo.identity_compose restRenaming)
      rw [tailReconstructs]

/-- **Right identity law.**  Composing with the identity remaps every image through the identity lookup, which
is the identity, so `mapImages_congr` + `mapImages_id` recover the renaming. -/
theorem RenamingTo.compose_identity {sourceScope targetScope : Nat}
    (dataRenaming : RenamingTo targetScope sourceScope) :
    dataRenaming.compose (RenamingTo.identity targetScope) = dataRenaming := by
  show dataRenaming.mapImages (RenamingTo.identity targetScope).lookup = dataRenaming
  rw [RenamingTo.mapImages_congr (RenamingTo.identity_lookup targetScope) dataRenaming]
  exact RenamingTo.mapImages_id dataRenaming

/-- **The display / weakening renaming `scope ⟶ scope + 1`.**  Shifts every variable past the freshly-bound
variable 0 — the DATA-morphism analogue of the function-side `RawRenaming.weaken`, built as the shift of the
identity (so it IS the tail of the successor identity).  This is the canonical context-PROJECTION morphism, the
representable-map candidate for an eventual representable-map class over `fxBaseRenamingCategory` (the genuine
display maps, as opposed to the degenerate isomorphism class).  Clean (no lookup-extensionality): its definition
and laws ride entirely on the shipped `mapImages` / `identity` algebra. -/
def RenamingTo.weakening (scope : Nat) : RenamingTo (scope + 1) scope :=
  (RenamingTo.identity scope).mapImages RenamingTo.shiftImage

/-- The weakening renaming reindexes every variable to its successor (`shiftImage`): variable `index` of the
base scope becomes variable `index + 1` of the extended scope. -/
theorem RenamingTo.weakening_lookup (scope : Nat) (index : Fin scope) :
    (RenamingTo.weakening scope).lookup index = RenamingTo.shiftImage index := by
  show ((RenamingTo.identity scope).mapImages RenamingTo.shiftImage).lookup index =
    RenamingTo.shiftImage index
  rw [lookup_mapImages, identity_lookup scope index]

/-- The successor identity decomposes as `cons var0 (weakening scope)` — the identity keeps the freshly-bound
variable 0 fixed and weakens (shifts) the rest.  Definitional, exhibiting the weakening as the identity's tail. -/
theorem RenamingTo.identity_succ_eq (scope : Nat) :
    RenamingTo.identity (scope + 1) =
      .cons ⟨0, Nat.succ_pos scope⟩ (RenamingTo.weakening scope) := rfl

/-- **The DATA-morphism FX renaming category.**  Objects are scopes (`Nat`), morphisms `source ⟶ target` are
reified renamings (`RenamingTo target source`).  All three category laws hold STRUCTURALLY (`compose_assoc` /
`identity_compose` / `compose_identity` by induction over the vector, no `funext`), so — unlike the
function-morphism `fxRenamingCategory` — this base can host a zero-axiom RMC: every future CwR equality over it
is a structural vector equality, not a function equality. -/
def fxBaseRenamingCategory : RawCategory.{0, 0} where
  Object := Nat
  Morphism := fun sourceScope targetScope => RenamingTo targetScope sourceScope
  identity := fun scope => RenamingTo.identity scope
  compose := fun firstRenaming secondRenaming => firstRenaming.compose secondRenaming
  composeAssoc := fun firstRenaming secondRenaming thirdRenaming =>
    RenamingTo.compose_assoc firstRenaming secondRenaming thirdRenaming
  identityLeft := fun morphism => RenamingTo.identity_compose morphism
  identityRight := fun morphism => RenamingTo.compose_identity morphism

/-- The categorical identity of `fxBaseRenamingCategory` IS the identity data renaming. -/
theorem fxBaseRenamingCategory_identity_eq {scope : Nat} :
    fxBaseRenamingCategory.identity scope = RenamingTo.identity scope := rfl

/-- The categorical composition of `fxBaseRenamingCategory` IS data-renaming composition. -/
theorem fxBaseRenamingCategory_compose_eq {scopeA scopeB scopeC : Nat}
    (firstRenaming : RenamingTo scopeB scopeA) (secondRenaming : RenamingTo scopeC scopeB) :
    fxBaseRenamingCategory.compose firstRenaming secondRenaming =
      firstRenaming.compose secondRenaming := rfl

end FX1Poly.Tier0
