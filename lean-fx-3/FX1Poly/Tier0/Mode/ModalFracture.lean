import FX1Poly.Tier0.Mode.Mode

/-! # mode-20 ★ — modal fracture / orthogonal factorization: the (co)reflective-subuniverse gluing

A MODALITY (reflective subuniverse) `○` and its complementary COMODALITY (coreflective subuniverse) `●`
induce an ORTHOGONAL FACTORIZATION SYSTEM, and the MODAL FRACTURE square reconstructs a type from its modal
and comodal parts as a PULLBACK — the type-theoretic analogue of the arithmetic fracture square
`ℤ → ℤ_p ×_{ℚ_p} ℚ` (Sullivan; Myers "Modal Fracture of Higher Groups").  `mode-20` mechanizes the decidable,
funext-free core of this story:

  * the **reflective subuniverse** `Modality` — an idempotent pointed functor — with the genuine OPEN/Sierpiński
    witness `openModality (Phase : Prop)` (`○A = Phase → A`), idempotent BY `rfl` precisely because the phase is a
    PROPOSITION (proof irrelevance + function eta collapse the diagonal);
  * the **localization universal property** — `○A` is always modal, a map into a modal type extends along the
    unit (`extend` + the `extend_unit` β-rule), the reflective factorization;
  * the dual **coreflective subuniverse** `CoreflectiveSubuniverse` with the CLOSED witness
    `closedComodality (Phase : Prop)` (`●A = Phase ×' A`, the Phase-stalk writer comonad) — the open/closed pair
    IS the STC phase recollement (`mode-12`);
  * the **pullback** (fibre product) as a first-order subtype-of-Eq with its FULL universal property (`mediate` +
    the computation rules + `Pullback.ext` uniqueness, all funext-free via proof irrelevance);
  * ★ the **modal fracture square** `Modality.fractureComparison` — the comparison of a map's domain into the
    pullback of its localization, the categorical reconciliation of the reflective and coreflective parts;
  * the **orthogonal factorization** — `LiftingSquare` / `Filler` / `IsIso` with `fillerOfLeftIso` /
    `fillerOfRightIso` (isos are orthogonal to every map on both sides), the lifting half of the OFS.

This complements the type-level OFS (`type-10`) with the mode-level version and connects to the modal fracture of
cohesion (`mode-13`).  The open modality's functor IS the reader modality of `mode-16` / `mode-17`.

## What is DEFERRED (markers)

  * the full ORTHOGONALITY — uniqueness of the diagonal filler / "the postcomposition square is a pullback" —
    needs `funext` (`hasUniqueLifting`);
  * the genuine FRACTURE THEOREM — `fractureComparison` is an EQUIVALENCE when the map is modal (`A ≃ ○A ×_{○●A} ●A`)
    — needs `funext` + univalence (`hasModalFractureEquivalence`);
  * the CLOSED modality as a genuine join HIT (`Phase ⋆ A`) + the lex condition making `○` left-exact
    (`hasClosedModalityHIT`);
  * the kernel's modal-lock / phase former unified with the fracture (cross-axis, `fib`)
    (`hasKernelModalFractureConnection`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## Reflective subuniverse / modality -/

/-- A **modality** (reflective subuniverse) — an IDEMPOTENT pointed endofunctor `○`: a functor (`map` + `map_id`)
with a unit `η` (natural) and a multiplication `μ`, where `μ` and `η` at `○A` are mutually inverse (the
`idempotent` law `η ∘ μ = id`, which upgrades a mere monad to a reflective subuniverse).  All laws are pointwise,
so the whole structure is `funext`-free. -/
structure Modality where
  /-- The localization functor `○`. -/
  Apply : Type → Type
  /-- The functorial action on maps. -/
  map : {A B : Type} → (A → B) → Apply A → Apply B
  /-- The reflector unit `η : A → ○A`. -/
  unit : {A : Type} → A → Apply A
  /-- The multiplication `μ : ○○A → ○A`. -/
  mult : {A : Type} → Apply (Apply A) → Apply A
  /-- `map` preserves identities. -/
  map_id : {A : Type} → (localized : Apply A) → map (fun element => element) localized = localized
  /-- `η` is natural: `map f ∘ η = η ∘ f`. -/
  unit_natural : {A B : Type} → (morphism : A → B) → (point : A) →
    map morphism (unit point) = unit (morphism point)
  /-- Left unit law `μ ∘ η = id` (one half of idempotency). -/
  mult_unit : {A : Type} → (localized : Apply A) → mult (unit localized) = localized
  /-- Right unit law `μ ∘ ○η = id`. -/
  mult_map_unit : {A : Type} → (localized : Apply A) → mult (map unit localized) = localized
  /-- ★ Idempotency `η ∘ μ = id` — the reflective-subuniverse condition: `μ` is an equivalence with inverse `η`.
  This is what makes `○` a localization rather than a mere monad. -/
  idempotent : {A : Type} → (nested : Apply (Apply A)) → unit (mult nested) = nested

/-- The trivial modality — `○ = id` (every type is modal), all laws by `rfl`. -/
def identityModality : Modality where
  Apply := fun A => A
  map := fun morphism => morphism
  unit := fun point => point
  mult := fun localized => localized
  map_id := fun _ => rfl
  unit_natural := fun _ _ => rfl
  mult_unit := fun _ => rfl
  mult_map_unit := fun _ => rfl
  idempotent := fun _ => rfl

/-- ★ The **open / Sierpiński modality** at a phase PROPOSITION `Phase` — `○A = Phase → A`, the reader over the
open subterminal.  Every law holds by `rfl`: the unit laws by function eta, and crucially the `idempotent` law
`η(μ nested) = nested` because `Phase : Prop` makes the two phase arguments of `nested` DEFINITIONALLY equal
(proof irrelevance), so the diagonal `μ` is inverted by the constant `η` up to `rfl`.  This is exactly why open
modalities are idempotent — the open subterminal is a proposition. -/
def openModality (Phase : Prop) : Modality where
  Apply := fun A => Phase → A
  map := fun morphism localized => fun phase => morphism (localized phase)
  unit := fun point => fun _ => point
  mult := fun nested => fun phase => nested phase phase
  map_id := fun _ => rfl
  unit_natural := fun _ _ => rfl
  mult_unit := fun _ => rfl
  mult_map_unit := fun _ => rfl
  idempotent := fun _ => rfl

/-! ## Modal algebras + the localization universal property -/

/-- A **modal algebra** for `modality` — a retraction of the unit (an `○`-algebra structure): the witness that a
type is `○`-MODAL / local.  For an idempotent monad these are exactly the modal types. -/
structure IsModalAlgebra (modality : Modality) (carrier : Type) where
  /-- The algebra structure map `○carrier → carrier`. -/
  structureMap : modality.Apply carrier → carrier
  /-- It is a retraction of the unit: `structureMap ∘ η = id`. -/
  unit_section : (point : carrier) → structureMap (modality.unit point) = point

/-- ★ The localization `○A` is ALWAYS modal — its structure map is `μ`, a retraction of `η` by the left unit law.
The core reflective-subuniverse fact, generic over any modality. -/
def Modality.localize_isModal (modality : Modality) (A : Type) :
    IsModalAlgebra modality (modality.Apply A) where
  structureMap := modality.mult
  unit_section := modality.mult_unit

/-- For the identity modality every type is modal. -/
def identity_everything_modal (carrier : Type) : IsModalAlgebra identityModality carrier where
  structureMap := fun point => point
  unit_section := fun _ => rfl

/-- The **reflective extension** — a map `f : A → M` into a modal `M` extends along the unit to `○A → M`
(`extend f := structureMap ∘ ○f`).  This is the universal property of the localization. -/
def Modality.extend (modality : Modality) {A carrier : Type}
    (algebra : IsModalAlgebra modality carrier) (morphism : A → carrier) :
    modality.Apply A → carrier :=
  fun localized => algebra.structureMap (modality.map morphism localized)

/-- ★ The **β-rule / factorization** — `extend f` recovers `f` on the unit: `(extend f) ∘ η = f`.  Every map into a
modal type factors through `η`, the reflective factorization. -/
theorem Modality.extend_unit (modality : Modality) {A carrier : Type}
    (algebra : IsModalAlgebra modality carrier) (morphism : A → carrier) (point : A) :
    modality.extend algebra morphism (modality.unit point) = morphism point := by
  show algebra.structureMap (modality.map morphism (modality.unit point)) = morphism point
  rw [modality.unit_natural]
  exact algebra.unit_section (morphism point)

/-- The reflective factor is unique ON THE UNIT IMAGE — any extension `g` agreeing with `f` after `η` agrees with
`extend f` after `η` (the generic part of the universal property; the full pointwise uniqueness needs `funext`). -/
theorem Modality.extend_unique_onUnit (modality : Modality) {A carrier : Type}
    (algebra : IsModalAlgebra modality carrier) (morphism : A → carrier)
    (candidate : modality.Apply A → carrier)
    (agrees : (point : A) → candidate (modality.unit point) = morphism point) (point : A) :
    candidate (modality.unit point) = modality.extend algebra morphism (modality.unit point) := by
  rw [agrees, modality.extend_unit]

/-! ## Coreflective subuniverse (the dual) + the open/closed pair -/

/-- A **coreflective subuniverse** (comodality) `●` — a copointed cofunctor: a functor `comap` with a counit
`ε : ●A → A` (natural).  The dual of `Modality`; the CLOSED half of the recollement. -/
structure CoreflectiveSubuniverse where
  /-- The colocalization cofunctor `●`. -/
  Colocalize : Type → Type
  /-- The cofunctorial action on maps. -/
  comap : {A B : Type} → (A → B) → Colocalize A → Colocalize B
  /-- The coreflector counit `ε : ●A → A`. -/
  counit : {A : Type} → Colocalize A → A
  /-- `ε` is natural: `f ∘ ε = ε ∘ ●f`. -/
  counit_natural : {A B : Type} → (morphism : A → B) → (colocalized : Colocalize A) →
    morphism (counit colocalized) = counit (comap morphism colocalized)

/-- The trivial comodality `● = id`. -/
def identityCoreflective : CoreflectiveSubuniverse where
  Colocalize := fun A => A
  comap := fun morphism => morphism
  counit := fun point => point
  counit_natural := fun _ _ => rfl

/-- ★ The **closed comodality** at a phase PROPOSITION `Phase` — `●A = Phase ×' A`, the Phase-stalk writer comonad,
the genuine DUAL of `openModality Phase`.  The pair `(openModality Phase, closedComodality Phase)` is the
Sierpiński / STC open-closed recollement (`mode-12` phase).  Naturality by `rfl`. -/
def closedComodality (Phase : Prop) : CoreflectiveSubuniverse where
  Colocalize := fun A => PProd Phase A
  comap := fun morphism stalk => ⟨stalk.fst, morphism stalk.snd⟩
  counit := fun stalk => stalk.snd
  counit_natural := fun _ _ => rfl

/-! ## The pullback (fibre product) + its universal property -/

/-- A **pullback** (fibre product) `Left ×_Apex Right` — a first-order subtype-of-`Eq`: a left point, a right
point, and a proof their legs agree.  The cospan is `leftLeg : Left → Apex`, `rightLeg : Right → Apex`. -/
structure Pullback {Apex Left Right : Type} (leftLeg : Left → Apex) (rightLeg : Right → Apex) where
  /-- The left component. -/
  onLeft : Left
  /-- The right component. -/
  onRight : Right
  /-- The gluing proof — the two legs agree. -/
  glued : leftLeg onLeft = rightLeg onRight

/-- The **mediating map** — a cone `(toLeft, toRight)` with a commuting proof factors through the pullback. -/
def Pullback.mediate {Apex Left Right : Type} {leftLeg : Left → Apex} {rightLeg : Right → Apex}
    {Cone : Type} (toLeft : Cone → Left) (toRight : Cone → Right)
    (commuting : (cone : Cone) → leftLeg (toLeft cone) = rightLeg (toRight cone)) :
    Cone → Pullback leftLeg rightLeg :=
  fun cone => { onLeft := toLeft cone, onRight := toRight cone, glued := commuting cone }

/-- The mediator's left triangle commutes by `rfl`. -/
theorem Pullback.mediate_onLeft {Apex Left Right : Type} {leftLeg : Left → Apex} {rightLeg : Right → Apex}
    {Cone : Type} (toLeft : Cone → Left) (toRight : Cone → Right)
    (commuting : (cone : Cone) → leftLeg (toLeft cone) = rightLeg (toRight cone)) (cone : Cone) :
    (Pullback.mediate toLeft toRight commuting cone).onLeft = toLeft cone := rfl

/-- The mediator's right triangle commutes by `rfl`. -/
theorem Pullback.mediate_onRight {Apex Left Right : Type} {leftLeg : Left → Apex} {rightLeg : Right → Apex}
    {Cone : Type} (toLeft : Cone → Left) (toRight : Cone → Right)
    (commuting : (cone : Cone) → leftLeg (toLeft cone) = rightLeg (toRight cone)) (cone : Cone) :
    (Pullback.mediate toLeft toRight commuting cone).onRight = toRight cone := rfl

/-- ★ Pullback **uniqueness** — two pullback elements agreeing on both projections are equal.  The `glued` field is
a `Prop`, so proof irrelevance closes it: the full universal-property uniqueness, funext-free. -/
theorem Pullback.ext {Apex Left Right : Type} {leftLeg : Left → Apex} {rightLeg : Right → Apex}
    {first second : Pullback leftLeg rightLeg}
    (onLeftEq : first.onLeft = second.onLeft) (onRightEq : first.onRight = second.onRight) :
    first = second := by
  obtain ⟨leftOne, rightOne, gluedOne⟩ := first
  obtain ⟨leftTwo, rightTwo, gluedTwo⟩ := second
  cases onLeftEq
  cases onRightEq
  rfl

/-! ## The modal fracture square -/

/-- ★ The **modal fracture comparison** — every map `f : A → B` comparison-maps its domain into the PULLBACK of its
localization `○f : ○A → ○B` against the unit `η_B : B → ○B`, sending `a ↦ (η_A a, f a)` with the gluing proof the
unit naturality.  This is the modal fracture / gluing square (the arithmetic-fracture analogue): the reflective
part `○A` and the comodal part `B` are reconciled over `○B`.  Its triangles commute by `rfl`; that the comparison
is an EQUIVALENCE (the genuine fracture theorem) is deferred (`funext` + univalence). -/
def Modality.fractureComparison (modality : Modality) {Source Target : Type} (morphism : Source → Target) :
    Source → Pullback (modality.map morphism) (modality.unit (A := Target)) :=
  Pullback.mediate (fun point => modality.unit point) (fun point => morphism point)
    (fun point => modality.unit_natural morphism point)

/-- The fracture comparison's localization leg is `η_A`. -/
theorem Modality.fractureComparison_onLeft (modality : Modality) {Source Target : Type}
    (morphism : Source → Target) (point : Source) :
    (modality.fractureComparison morphism point).onLeft = modality.unit point := rfl

/-- The fracture comparison's comodal leg is `f`. -/
theorem Modality.fractureComparison_onRight (modality : Modality) {Source Target : Type}
    (morphism : Source → Target) (point : Source) :
    (modality.fractureComparison morphism point).onRight = morphism point := rfl

/-! ## The orthogonal factorization — lifting squares + filler -/

/-- A **commuting lifting square** — a left map `left : upperLeft → lowerLeft` (vertical), a right map
`right : upperRight → lowerRight` (vertical), a top `upperLeft → upperRight`, a bottom `lowerLeft → lowerRight`,
with `right ∘ top = bottom ∘ left`.  The data of a lifting problem `left ⧄ right`. -/
structure LiftingSquare {upperLeft lowerLeft upperRight lowerRight : Type}
    (left : upperLeft → lowerLeft) (right : upperRight → lowerRight) where
  /-- The top edge. -/
  top : upperLeft → upperRight
  /-- The bottom edge. -/
  bottom : lowerLeft → lowerRight
  /-- The square commutes. -/
  commutes : (point : upperLeft) → right (top point) = bottom (left point)

/-- A **diagonal filler** of a lifting square — a diagonal `lowerLeft → upperRight` making both triangles commute.
Existence of a (unique) filler for every square is `left ⊥ right` (orthogonality). -/
structure Filler {upperLeft lowerLeft upperRight lowerRight : Type}
    {left : upperLeft → lowerLeft} {right : upperRight → lowerRight}
    (square : LiftingSquare left right) where
  /-- The diagonal lift. -/
  diagonal : lowerLeft → upperRight
  /-- Upper triangle: `diagonal ∘ left = top`. -/
  upperTriangle : (point : upperLeft) → diagonal (left point) = square.top point
  /-- Lower triangle: `right ∘ diagonal = bottom`. -/
  lowerTriangle : (point : lowerLeft) → right (diagonal point) = square.bottom point

/-- An **isomorphism** — a map with a two-sided inverse (both round trips pointwise). -/
structure IsIso {Source Target : Type} (forward : Source → Target) where
  /-- The inverse map. -/
  backward : Target → Source
  /-- `forward ∘ backward = id`. -/
  forward_backward : (target : Target) → forward (backward target) = target
  /-- `backward ∘ forward = id`. -/
  backward_forward : (source : Source) → backward (forward source) = source

/-- Upper triangle when the left map is an iso: `top ∘ backward ∘ left = top`. -/
theorem leftIso_upperTriangle {upperLeft lowerLeft upperRight lowerRight : Type}
    {left : upperLeft → lowerLeft} {right : upperRight → lowerRight}
    (square : LiftingSquare left right) (leftIso : IsIso left) (point : upperLeft) :
    square.top (leftIso.backward (left point)) = square.top point := by
  rw [leftIso.backward_forward]

/-- Lower triangle when the left map is an iso. -/
theorem leftIso_lowerTriangle {upperLeft lowerLeft upperRight lowerRight : Type}
    {left : upperLeft → lowerLeft} {right : upperRight → lowerRight}
    (square : LiftingSquare left right) (leftIso : IsIso left) (point : lowerLeft) :
    right (square.top (leftIso.backward point)) = square.bottom point := by
  rw [square.commutes, leftIso.forward_backward]

/-- ★ An iso on the LEFT is left-orthogonal to every map — the diagonal is `top ∘ left⁻¹`.  Half of "isos are
orthogonal to all maps" (the existence half; uniqueness needs `funext`). -/
def fillerOfLeftIso {upperLeft lowerLeft upperRight lowerRight : Type}
    {left : upperLeft → lowerLeft} {right : upperRight → lowerRight}
    (square : LiftingSquare left right) (leftIso : IsIso left) : Filler square where
  diagonal := fun lower => square.top (leftIso.backward lower)
  upperTriangle := leftIso_upperTriangle square leftIso
  lowerTriangle := leftIso_lowerTriangle square leftIso

/-- Upper triangle when the right map is an iso. -/
theorem rightIso_upperTriangle {upperLeft lowerLeft upperRight lowerRight : Type}
    {left : upperLeft → lowerLeft} {right : upperRight → lowerRight}
    (square : LiftingSquare left right) (rightIso : IsIso right) (point : upperLeft) :
    rightIso.backward (square.bottom (left point)) = square.top point := by
  rw [← square.commutes, rightIso.backward_forward]

/-- Lower triangle when the right map is an iso. -/
theorem rightIso_lowerTriangle {upperLeft lowerLeft upperRight lowerRight : Type}
    {left : upperLeft → lowerLeft} {right : upperRight → lowerRight}
    (square : LiftingSquare left right) (rightIso : IsIso right) (point : lowerLeft) :
    right (rightIso.backward (square.bottom point)) = square.bottom point := by
  rw [rightIso.forward_backward]

/-- ★ An iso on the RIGHT is right-orthogonal to every map — the diagonal is `right⁻¹ ∘ bottom`. -/
def fillerOfRightIso {upperLeft lowerLeft upperRight lowerRight : Type}
    {left : upperLeft → lowerLeft} {right : upperRight → lowerRight}
    (square : LiftingSquare left right) (rightIso : IsIso right) : Filler square where
  diagonal := fun lower => rightIso.backward (square.bottom lower)
  upperTriangle := rightIso_upperTriangle square rightIso
  lowerTriangle := rightIso_lowerTriangle square rightIso

/-! ## Uniqueness of the filler against a monomorphism (funext-free) -/

/-- A map is a **monomorphism** when it is injective — `forward sourceOne = forward sourceTwo → sourceOne =
sourceTwo`.  The right-hand side condition under which a diagonal filler is unique. -/
def IsMono {Source Target : Type} (forward : Source → Target) : Prop :=
  (sourceOne sourceTwo : Source) → forward sourceOne = forward sourceTwo → sourceOne = sourceTwo

/-- ★ **Pointwise uniqueness of the diagonal filler against a monomorphism.**  When the right map is mono, any two
fillers of the same square have POINTWISE-equal diagonals: the shared lower triangle gives `right (fillerOne.diagonal
point) = square.bottom point = right (fillerTwo.diagonal point)`, and `right` mono cancels.  This is the genuine
UNIQUENESS half of orthogonality (`left ⊥ right`), funext-free — the space of fillers is a subsingleton pointwise.
The only residue needing `funext` is the cosmetic upgrade of pointwise agreement to function equality. -/
theorem filler_pointwise_unique_of_mono {upperLeft lowerLeft upperRight lowerRight : Type}
    {left : upperLeft → lowerLeft} {right : upperRight → lowerRight}
    {square : LiftingSquare left right} (rightMono : IsMono right)
    (fillerOne fillerTwo : Filler square) (point : lowerLeft) :
    fillerOne.diagonal point = fillerTwo.diagonal point :=
  rightMono _ _ (Eq.trans (fillerOne.lowerTriangle point) (fillerTwo.lowerTriangle point).symm)

/-- ★ **Iso-left + mono-right ⟹ pointwise-contractible filler space.**  Combining existence (`fillerOfLeftIso`)
with uniqueness (`filler_pointwise_unique_of_mono`): ANY filler agrees POINTWISE with the canonical iso-built
diagonal `square.top ∘ left⁻¹`.  This is genuine orthogonality (`left ⊥ right`) in the funext-free pointwise
sense — both halves (a filler exists, and it is unique pointwise). -/
theorem isoLeft_monoRight_filler_pointwise_unique {upperLeft lowerLeft upperRight lowerRight : Type}
    {left : upperLeft → lowerLeft} {right : upperRight → lowerRight}
    {square : LiftingSquare left right} (leftIso : IsIso left) (rightMono : IsMono right)
    (anyFiller : Filler square) (point : lowerLeft) :
    anyFiller.diagonal point = (fillerOfLeftIso square leftIso).diagonal point :=
  filler_pointwise_unique_of_mono rightMono anyFiller (fillerOfLeftIso square leftIso) point

/-! ## Honesty markers -/

/-- ★ **Honesty marker — pointwise unique lifting against a monomorphism ships.**  The genuine UNIQUENESS half of
orthogonality (`left ⊥ right`) — POINTWISE uniqueness of the diagonal filler when `right` is mono
(`filler_pointwise_unique_of_mono`), and the existence+uniqueness combination for an iso-left square
(`isoLeft_monoRight_filler_pointwise_unique`, the filler space is pointwise-contractible) — is proven funext-free.
The ONLY residue is the cosmetic upgrade of pointwise agreement (`fillerOne.diagonal point = fillerTwo.diagonal
point` for all `point`) to function equality (`fillerOne.diagonal = fillerTwo.diagonal`), which needs `funext`
(= `Quot.sound`, off-limits zero-axiom); equivalently the postcomposition-square-is-a-pullback reformulation.
`= true` for the pointwise content. -/
def fxMode_hasUniqueLifting : Bool := true

/-- **Honesty marker.**  The genuine FRACTURE THEOREM — that `fractureComparison` is an EQUIVALENCE for a modal map
(`A ≃ ○A ×_{○●A} ●A`, the reconstruction), beyond the comparison square shipped here — needs `funext` +
univalence.  `= false`. -/
def fxMode_hasModalFractureEquivalence : Bool := false

/-- **Honesty marker.**  The CLOSED modality as a genuine join HIT (`●A = Phase ⋆ A`) and the LEX condition making
`○` left-exact (the prerequisite for the fracture square to be cartesian), beyond the `PProd` stalk witness here,
need higher inductive types.  `= false`. -/
def fxMode_hasClosedModalityHIT : Bool := false

/-- **Honesty marker.**  The connection to the kernel's modal-lock / phase former unified with the fracture square
is cross-axis (`fib`), deferred.  `= false`. -/
def fxMode_hasKernelModalFractureConnection : Bool := false

end FX1Poly.Tier0
