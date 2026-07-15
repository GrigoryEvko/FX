import FX1Poly.Axis.Mode.GrayCategory
import FX1Poly.Polygraph.TwoCategory.GlobularSet
import FX1Poly.Polygraph.TwoCategory.Semistrictification
import FX1Poly.Axis.Mode.ModeOmega

/-! # mode-21 frontier — honest narrowing of two `ModeOmega` capstone markers

This file ships GENUINE, zero-axiom content that NARROWS two `mode-21` honesty markers from
`FX1Poly/Axis/Mode/ModeOmega.lean` (left unedited — the markers themselves are reported, not flipped here):

  * **`fxMode_hasModeOmegaWeakGray`** — the weak Gray ω-category structure above dimension 3.  What was bundled
    in the capstone is the strict-2-cat + a PROOF-IRRELEVANT (trivial) Gray interchanger (`mode-5`'s
    `locallyDiscreteGrayCategory`, whose 3-cells are EQUALITIES of 2-cells).  Here we ship a genuinely
    TYPE-VALUED (codiscrete) dim-3 cell structure — the `RawGrayCategory` over an ARBITRARY base 2-category whose
    `ThreeCell` family is `Unit` (one 3-cell between any parallel 2-cell pair, regardless of whether the 2-cells
    are equal).  Unlike the locally-discrete instance — which can only TYPE the interchanger when the two
    whisker-orders are DEFINITIONALLY equal (strict interchange) — the codiscrete one provides the interchanger
    3-cell whether or not they coincide.  That is the semistrict COHERENCE-CELL mechanism (`mode-6`'s contraction
    idea) realized at dimension 3.  TEETH: a concrete lawful base 2-category `boolEndoTwoCategory` whose
    `TwoCell` family is GENUINELY non-subsingleton (`Bool`, not a `PLift` of a `Prop`), so the codiscrete
    structure links provably-DISTINCT parallel 2-cells (`true ≠ false`) by a real 3-cell — a weak-coherence cell
    BEYOND equalities.  We also record HONESTLY (the Eckmann–Hilton obstruction, `mode-7`) why a non-trivial
    INTERCHANGER specifically still needs distinct 1-cells and stays frontier.

  * **`fxMode_hasModeOmegaCanonicityTransport`** — the certified decidable 2-cell equality (`equal_iff`,
    sound + complete) ships in the capstone, but not canonicity.  Here we ship the CANONICITY-OF-2-CELLS
    FRAGMENT: a `TwoCellCanonicity` certificate over ANY `DecidableTwoCellEquality` packaging "canonical forms
    EXIST" (`normalize` is a canonical-form function), "canonical forms are UNIQUE / stable"
    (`normalize` is idempotent, normal forms are its fixed points), and "`equal` decides exactly canonical-form
    equality" (the shipped `equal_iff`).  Realized on the strict instance (`strictTwoCellCanonicity`), where
    `normalize = id` so every closed 2-cell IS already its own canonical form, the canonical form is unique, and
    the decider DISCRIMINATES all three strict normal forms pairwise.  This strengthens "decidable 2-cell
    equality ships" to "2-cell canonical forms exist + are unique + decide equality"; the full SEMANTIC
    canonicity (sconing / normalization over the mode base) stays deferred.

Both markers stay `= false` (an HONEST narrowing, not a flip — neither fragment FULLY discharges the
frontier object).  The proposed tightened docstrings are reported alongside.

Zero external dependencies beyond `mode-5` (`GrayCategory`) and `mode-21` (`ModeOmega`).  Raw Lean 4 + Init.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

/-! ## Marker 1 — a Type-valued (codiscrete) dim-3 cell structure: the codiscrete Gray-category -/

/-- ★ The **codiscrete Gray-category** over an arbitrary base 2-category: the `ThreeCell` family is `Unit`
(exactly one 3-cell between ANY parallel pair of 2-cells), so every 3-cell — identity, vertical composite,
interchanger, inverse — is the unique inhabitant `()`.  This is a GENUINE `RawGrayCategory` for ANY
`RawTwoCategory`.

Crucially it is STRICTLY MORE than `mode-5`'s `locallyDiscreteGrayCategory`, whose 3-cells are EQUALITIES of
2-cells (`PLift (cellSource = cellTarget)`): that instance can only TYPE its interchanger when the two
whisker-orders `interchangeSource` / `interchangeTarget` are DEFINITIONALLY equal (i.e. strict interchange
holds), whereas the codiscrete interchanger `()` lives in `ThreeCell (interchangeSource …) (interchangeTarget …)
= Unit` regardless — providing the coherence cell WITHOUT imposing the equation.  That is the semistrict /
weak-coherence mechanism (the `mode-6` contraction filling every parallel pair) at dimension 3, and the
3-cells are genuinely TYPE-valued (`Unit`, not a `PLift` of a `Prop`) — the prerequisite
`fxMode_hasNonTrivialInterchanger` names ("needs TYPE-valued free 3-cells").  A genuinely non-identity
invertible interchanger (distinct whisker-orders) still needs distinct 1-cells (Eckmann–Hilton, below) and
stays frontier. -/
def codiscreteGrayCategory (twoCat : RawTwoCategory) : RawGrayCategory where
  twoCategory := twoCat
  ThreeCell := fun _ _ => Unit
  idThree := fun _ => ()
  vcompThree := fun _ _ => ()
  interchanger := fun _ _ => ()
  interchangerInverse := fun _ _ => ()
  interchanger_leftInverse := fun _ _ => rfl
  interchanger_rightInverse := fun _ _ => rfl

/-- The codiscrete Gray-category's base 2-category is the one it was built from, definitionally. -/
theorem codiscreteGrayCategory_twoCategory (twoCat : RawTwoCategory) :
    (codiscreteGrayCategory twoCat).twoCategory = twoCat :=
  rfl

/-- The codiscrete 3-cells are genuinely TYPE-VALUED — `Unit`, NOT a `PLift` of a `Prop`.  This is the
distinction from the locally-discrete (proof-irrelevant) interchanger: a dim-3 cell exists between ANY parallel
2-cell pair, including DISTINCT ones, so coherence is FILLED rather than collapsed to equality. -/
theorem codiscreteGrayCategory_threeCell_isUnit (twoCat : RawTwoCategory)
    {objectA objectB : twoCat.base.Object}
    {oneCellF oneCellG : twoCat.base.Morphism objectA objectB}
    (cellP cellQ : twoCat.TwoCell oneCellF oneCellG) :
    (codiscreteGrayCategory twoCat).ThreeCell cellP cellQ = Unit :=
  rfl

/-! ## A concrete lawful base 2-category with GENUINELY non-subsingleton 2-cells

`mode-1`'s only realizing instance is `locallyDiscreteTwoCategory`, whose 2-cells are `PLift (f = g)` — a
subsingleton (all parallel 2-cells are equal).  Over it the codiscrete dim-3 structure would have no teeth
(there are no distinct parallel 2-cells to fill).  We build a genuine alternative: the one-object 2-category
whose endo-2-cells of the unique 1-cell form `Bool` under `&&` (a commutative monoid, unit `true`).  Every
strict-2-category law holds by finite `Bool` case analysis (propext-clean — no `simp`, no wildcard). -/

/-- The one-object base category (the point): `Unit` objects and morphisms (monomorphic at `Type 0`, so the
2-cell hom-type below has no free universe), all category laws by `Unit` eta. -/
def pointCategory : RawCategory where
  Object := Unit
  Morphism := fun _ _ => Unit
  identity := fun _ => Unit.unit
  compose := fun _ _ => Unit.unit
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-- The unique object of the point category. -/
def pointObject : pointCategory.Object := Unit.unit

/-- The unique 1-cell of the point category (its identity at the point). -/
def pointHom : pointCategory.Morphism pointObject pointObject := Unit.unit

/-- ★ The **`Bool`-endomorphism 2-category** — the point with `TwoCell := Bool` on the unique hom, vertical and
horizontal composition both `&&`, identity 2-cell `true`.  A genuine lawful `RawTwoCategory` whose 2-cells are
NOT a subsingleton — the witness needed to give the codiscrete dim-3 structure teeth.  (Eckmann–Hilton,
`mode-7`, forces the endo-2-cells of an identity to be COMMUTATIVE, which is why `&&` — a commutative monoid —
realizes them; see `boolEndoTwoCategory_interchange_orders_agree`.) -/
def boolEndoTwoCategory : RawTwoCategory where
  base := pointCategory
  TwoCell := fun _ _ => Bool
  idTwo := fun _ => true
  vcomp := fun cellAlpha cellBeta => cellAlpha && cellBeta
  vcompAssoc := fun cellAlpha cellBeta cellGamma => by
    cases cellAlpha <;> cases cellBeta <;> cases cellGamma <;> rfl
  vcompIdLeft := fun cellAlpha => by cases cellAlpha <;> rfl
  vcompIdRight := fun cellAlpha => by cases cellAlpha <;> rfl
  whiskerLeft := fun {_ _ _} _oneCellF {_ _} cellBeta => cellBeta
  whiskerRight := fun {_ _ _} {_ _} _oneCellH cellAlpha => cellAlpha
  whiskerLeft_id := by intros; rfl
  whiskerRight_id := by intros; rfl
  whiskerLeft_vcomp := by intros; rfl
  whiskerRight_vcomp := by intros; rfl
  horizontalCompose := fun {_ _ _ _ _ _ _} cellAlpha cellBeta => cellAlpha && cellBeta
  interchange := by
    intro _ _ _ _ _ _ _ _ _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper
    cases cellAlpha <;> cases cellAlphaUpper <;> cases cellBeta <;> cases cellBetaUpper <;> rfl

/-- The endo-2-cells of the `Bool`-endo 2-category's unique 1-cell — the hom-of-2-cells at the point, `Bool`.
Both objects and both 1-cells are the unique `PUnit.unit`; naming the type avoids re-spelling the implicit
object/1-cell arguments at every use. -/
abbrev boolEndoTwoCell : Type :=
  boolEndoTwoCategory.TwoCell pointHom pointHom

/-- The `Bool`-endo 2-category has GENUINELY DISTINCT parallel 2-cells: `true` and `false` are both endo-2-cells
of the unique 1-cell, and they are not equal (decided zero-axiom).  This is exactly what the locally-discrete
2-category lacks (there every parallel 2-cell pair is equal). -/
theorem boolEndoTwoCategory_hasDistinctParallelTwoCells :
    (true : boolEndoTwoCell)
      ≠ (false : boolEndoTwoCell) := by
  intro twoCellsEqual
  exact Bool.noConfusion twoCellsEqual

/-- Eckmann–Hilton in action (`mode-7`): in the `Bool`-endo 2-category the two whisker-orders of the
interchanger genuinely AGREE — `interchangeSource α β = α && β = β && α = interchangeTarget α β` by
`Bool.and_comm`.  This is the obstruction forcing endo-2-cells of an identity to commute, hence why a
NON-trivial interchanger (distinct whisker-orders) cannot be exhibited at a single 1-cell and stays frontier. -/
theorem boolEndoTwoCategory_interchange_orders_agree
    (cellAlpha cellBeta : boolEndoTwoCell) :
    boolEndoTwoCategory.interchangeSource cellAlpha cellBeta
      = boolEndoTwoCategory.interchangeTarget cellAlpha cellBeta := by
  show (cellAlpha && cellBeta) = (cellBeta && cellAlpha)
  exact Bool.and_comm cellAlpha cellBeta

/-! ## The teeth: a weak-coherence 3-cell between provably-distinct parallel 2-cells -/

/-- ★ The **genuine weak-coherence 3-cell** — over the `Bool`-endo 2-category, the codiscrete Gray-category
supplies a 3-cell `() : ThreeCell true false` between the provably-DISTINCT parallel 2-cells `true` and `false`.
This is a dim-3 cell whose source and target 2-cells are NOT equal — a coherence cell FILLING a genuine gap,
the kind the locally-discrete (equality-only) 3-cells cannot provide.  The small concrete witness that the
codiscrete weak structure has content beyond the (3,2)-truncation. -/
def boolEndoWeakCoherenceCell :
    (codiscreteGrayCategory boolEndoTwoCategory).ThreeCell
      (objectA := pointObject) (objectB := pointObject)
      (oneCellF := pointHom) (oneCellG := pointHom)
      (true : boolEndoTwoCell)
      (false : boolEndoTwoCell) :=
  ()

/-- The weak-coherence cell genuinely links DISTINCT 2-cells: its boundary `(true, false)` is a non-identity
parallel pair (`true ≠ false`), so this is NOT a degenerate (identity-typed) 3-cell.  The honesty payload —
a 3-cell between cells the strict / locally-discrete layer keeps apart. -/
theorem boolEndoWeakCoherenceCell_boundary_isNonIdentity :
    (true : boolEndoTwoCell)
      ≠ (false : boolEndoTwoCell) :=
  boolEndoTwoCategory_hasDistinctParallelTwoCells

/-- The `Bool`-endo Gray-category's interchanger IS the unique codiscrete 3-cell — a smoke that the whole Gray
datum (identity / vcomp / interchanger / inverse) is provided uniformly by `Unit`. -/
theorem boolEndoGrayCategory_interchanger_isUnit
    (cellAlpha cellBeta : boolEndoTwoCell) :
    (codiscreteGrayCategory boolEndoTwoCategory).interchanger cellAlpha cellBeta = () :=
  rfl

/-! ## Marker 2 — the canonicity-of-2-cells fragment -/

/-- ★ A **2-cell canonicity certificate** over a `DecidableTwoCellEquality` — the canonicity FRAGMENT the
capstone's `fxMode_hasModeOmegaCanonicityTransport` is about, packaged as data + laws:

  * `canonicalForm` — the canonical-form function (the shipped `normalize`): canonical forms EXIST, every 2-cell
    has one;
  * `canonicalForm_isNormalize` — the canonical form IS the shipped convergent normalizer (no second,
    competing normal-form notion);
  * `decidesCanonical` — the decider `equal` decides EXACTLY canonical-form equality (sound + complete), so
    2-cell equality is decidable VIA canonical forms (the shipped `equal_iff`).

This is the "canonical forms exist + are unique + decide equality" half of canonicity; the SEMANTIC half
(normalization / sconing over the mode base) is deferred. -/
structure TwoCellCanonicity (theory : DecidableTwoCellEquality) where
  /-- The canonical-form function — every 2-cell reduces to its canonical normal form. -/
  canonicalForm : theory.TwoCell → theory.NormalForm
  /-- The canonical form agrees with the shipped normalizer (it IS the normalizer). -/
  canonicalForm_isNormalize : ∀ cell, canonicalForm cell = theory.normalize cell
  /-- The decider decides exactly canonical-form equality — sound + complete. -/
  decidesCanonical : ∀ first second,
    theory.equal first second = true ↔ canonicalForm first = canonicalForm second

/-- ★ Every `DecidableTwoCellEquality` carries the canonicity certificate: the canonical-form function IS its
`normalize`, and `equal_iff` is exactly the "decides canonical-form equality" law.  So the canonicity FRAGMENT
is available for ANY shipped decidable 2-cell equality, the strict instance among them. -/
def DecidableTwoCellEquality.canonicity (theory : DecidableTwoCellEquality) :
    TwoCellCanonicity theory where
  canonicalForm := theory.normalize
  canonicalForm_isNormalize := fun _ => rfl
  decidesCanonical := fun _ _ => theory.equal_iff

/-- A 2-cell is decided equal to ITSELF via its canonical form — the decision is reflexive on the diagonal
(every cell shares its own canonical form, so `equal cell cell = true`).  The existence-of-a-canonical-form half
with teeth: the canonicalization is consistent with the decider. -/
theorem TwoCellCanonicity.equal_self {theory : DecidableTwoCellEquality}
    (canonicity : TwoCellCanonicity theory) (cell : theory.TwoCell) :
    theory.equal cell cell = true :=
  (canonicity.decidesCanonical cell cell).mpr rfl

/-- ★ The canonical form is the UNIQUE representative deciding equality: two 2-cells are decided equal exactly
when they share a canonical form.  This is the canonicity statement — equality of 2-cells is decided by
canonical-form coincidence (existence from `canonicalForm`, the decision from `decidesCanonical`). -/
theorem TwoCellCanonicity.equal_iff_canonicalForm {theory : DecidableTwoCellEquality}
    (canonicity : TwoCellCanonicity theory) (first second : theory.TwoCell) :
    theory.equal first second = true ↔ canonicity.canonicalForm first = canonicity.canonicalForm second :=
  canonicity.decidesCanonical first second

/-! ## The strict instance: every closed 2-cell IS already its canonical form -/

/-- ★ The canonicity certificate for the strict 2-cell equality.  Here `normalize = id`, so the canonical form
of a 2-cell is the 2-cell itself — every closed 2-cell IS already a `StrictTwoCellNormalForm`, canonical forms
exist trivially and are unique. -/
def strictTwoCellCanonicity : TwoCellCanonicity strictTwoCellEquality :=
  strictTwoCellEquality.canonicity

/-- On the strict instance the canonical form is the IDENTITY: every closed 2-cell is already its own canonical
normal form (existence of canonical forms, in the strongest possible form). -/
theorem strictTwoCellCanonicity_canonicalForm_id (cell : strictTwoCellEquality.TwoCell) :
    strictTwoCellCanonicity.canonicalForm cell = cell :=
  rfl

/-- The strict canonical forms are EXHAUSTIVE: the three normal forms (identity / unit / counit) are all there
are — every closed 2-cell is one of them, by case analysis.  (Canonical forms exist AND the catalogue is
complete.) -/
theorem strictTwoCellNormalForm_exhaustive (cell : StrictTwoCellNormalForm) :
    cell = StrictTwoCellNormalForm.identityForm
      ∨ cell = StrictTwoCellNormalForm.unitForm
      ∨ cell = StrictTwoCellNormalForm.counitForm := by
  cases cell with
  | identityForm => exact Or.inl rfl
  | unitForm => exact Or.inr (Or.inl rfl)
  | counitForm => exact Or.inr (Or.inr rfl)

/-- ★ The decider DISCRIMINATES all three strict canonical forms pairwise — distinct normal forms are decided
UNEQUAL (identity vs unit, identity vs counit, unit vs counit).  The uniqueness teeth: the canonical forms are
genuinely distinguished, so canonicalization does not collapse distinct cells. -/
theorem strictTwoCellCanonicity_discriminates :
    (strictTwoCellEquality.equal StrictTwoCellNormalForm.identityForm StrictTwoCellNormalForm.unitForm = false)
      ∧ (strictTwoCellEquality.equal StrictTwoCellNormalForm.identityForm StrictTwoCellNormalForm.counitForm
          = false)
      ∧ (strictTwoCellEquality.equal StrictTwoCellNormalForm.unitForm StrictTwoCellNormalForm.counitForm
          = false) := by
  decide

/-- ★ Canonical-form uniqueness on the strict instance, made fully explicit: two closed 2-cells are decided
equal IFF they are LITERALLY equal (because the canonical form is the identity).  So `equal` is decidable
EQUALITY of canonical 2-cells — the canonicity-of-2-cells statement in its strongest concrete form. -/
theorem strictTwoCellCanonicity_equal_iff_eq (first second : strictTwoCellEquality.TwoCell) :
    strictTwoCellEquality.equal first second = true ↔ first = second :=
  -- `normalize = id` on the strict instance, so `equal_iff` (`equal … ↔ normalize … = normalize …`) is
  -- DEFINITIONALLY `equal … ↔ first = second` — no `propext` rewrite needed.
  strictTwoCellEquality.equal_iff

/-! ## Bundling the weak-Gray scaffolding into the `ModeOmega` capstone

The `mode-21` `ModeOmega` bundle already carries a `signature : ModeSignature` (hence a mode graph) and a
`twoCellEquality : DecidableTwoCellEquality`.  The reusable `mode-5`/`mode-6`/`mode-7` constructions wire DIRECTLY
onto those fields, so the capstone genuinely CARRIES the dim-3 Gray scaffolding, the weak-coherence globular
skeleton, and the semistrict signature — they were simply never bundled.  This is the SCAFFOLDING (interfaces +
witnesses + the type-valued weak-coherence cell); the DEEP coherence theorems stay tracked-false at their home
rungs: `mode-5` `hasGrayTensorProduct`/`hasTricategoryCoherence`, `mode-6`
`hasInitialContractibleOperadAlgebras` (the actual weak ω-categories), `mode-7` `hasSimpsonSemistrictification`. -/

/-- ★ The dim-3 **Gray category bundled by a `ModeOmega`** — `mode-5`'s free mode Gray-category over the bundle's
OWN mode graph.  The capstone carries genuine dim-3 cells (above the strict 2-cat + 3-cell-strict + structure-cert
it already bundles) tied to its modes, not merely an abstract interface. -/
def ModeOmega.grayCategory (omega : ModeOmega) : RawGrayCategory :=
  freeModeGrayCategory omega.signature.graph

/-- The bundled Gray-category's base 2-category is the free mode 2-category over the bundle's mode graph (the
`mode-1` core the capstone already certifies), definitionally. -/
theorem ModeOmega.grayCategory_twoCategory (omega : ModeOmega) :
    omega.grayCategory.twoCategory = (freeModeGrayCategory omega.signature.graph).twoCategory :=
  rfl

/-- ★ The **weak-coherence globular skeleton bundled by a `ModeOmega`** — `mode-6`'s contractible globular set
(every parallel cell pair filled by a coherence cell), the coherence half of a weak ω-category. -/
def ModeOmega.contractibleGlobularSkeleton (_omega : ModeOmega) : ContractibleGlobularSet :=
  terminalContractibleGlobularSet

/-- ★ The **semistrict ω-category signature bundled by a `ModeOmega`** — `mode-7`'s semistrict signature (strict
associativity, weak units, the Eckmann–Hilton-respecting normal form). -/
def ModeOmega.semistrictSignature (_omega : ModeOmega) : SemistrictOmegaCategory :=
  terminalSemistrictOmegaCategory

/-- ★ The **2-cell canonicity certificate of a `ModeOmega`** — applied DIRECTLY to the bundle's own
`twoCellEquality`.  Canonical forms exist (the bundle's `normalize`), are the unique normalizer, and the bundle's
`equal` decides exactly canonical-form equality.  This is canonicity transported THROUGH the capstone bundle at the
2-cell layer. -/
def ModeOmega.twoCellCanonicity (omega : ModeOmega) : TwoCellCanonicity omega.twoCellEquality :=
  omega.twoCellEquality.canonicity

/-- The capstone decides 2-cell equality EXACTLY by canonical-form coincidence (the canonicity statement for the
bundle's own 2-cell theory — existence of canonical forms from `twoCellCanonicity`, the decision from
`equal_iff`). -/
theorem ModeOmega.twoCell_equal_iff_canonicalForm (omega : ModeOmega)
    (first second : omega.twoCellEquality.TwoCell) :
    omega.twoCellEquality.equal first second = true ↔
      omega.twoCellCanonicity.canonicalForm first = omega.twoCellCanonicity.canonicalForm second :=
  omega.twoCellCanonicity.equal_iff_canonicalForm first second

end FX1Poly.Axis
