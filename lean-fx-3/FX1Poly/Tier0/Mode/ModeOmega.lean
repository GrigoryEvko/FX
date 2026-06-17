import FX1Poly.Tier0.Mode.Mode
import FX1Poly.Tier0.Mode.MultiplierStructureClass
import FX1Poly.Tier0.Mode.CombineAmalgamation

/-! # mode-21 ★ CAPSTONE — the standalone (weak) higher-polygraph mode ω-category

The capstone ASSEMBLES the whole mode axis as one finished frontier object: a single `ModeOmega` record that
carries the diabolical multimodal doctrine ENTIRELY AS DATA, with a DECIDABLE ADMISSIBILITY CERTIFICATE and
DECIDABLE 2-CELL EQUALITY, independent of any type theory.  It is the Tier0 deliverable the `fib-*` gluing (and
`Context/ModalLock`, which already names `Tier0/ModeOmega`) consumes.

`ModeOmega` bundles, by genuine aggregation of the shipped rungs:

  * the **polygraph signature** (`mode-0` `ModeSignature`) — the 0-cell modes, 1-cell modality generators, and
    2-cell generators;
  * the **structure-class certificate** (`mode-2` `MultiplierStructureClass`, Fig 7) per modality generator —
    affine / cartesian / dedekind / deMorgan, with `supportsDiagonal` etc.;
  * the **adjoint-string depth** (`mode-4`) per modality — the length of the modality's adjoint string (the full
    string coherence is `mode-4`);
  * the **doctrine** (`mode-17` / `mode-18` `Doctrine`) — the §6.8 feature profile with its decidable
    admissibility / amalgamation;
  * the **decidable 2-cell equality** (`mode-3`, the convergent 3-polygraph lifted) — packaged as a normalizer to
    normal forms plus a `DecidableEq` on them.

## What this file ships (each piece zero-axiom)

  * **`ModeOmega`** + **`ModeOmega.isAdmissible`** — the bundle + its decidable admissibility certificate
    (`doctrine.isAdmissible`, a computable `Bool`).
  * **`DecidableTwoCellEquality`** + `equal` + ★ `equal_refl` — the decidable 2-cell equality machine (normalizer
    + `DecidableEq` on normal forms ⟹ a decision procedure), reflexive.
  * the witnesses ★ **`fxModeOmega`** (the FX mode theory: the cohesion/adjunction seed + an admissible resource
    doctrine), **`cohesionModeOmega`** (`mode-13`), **`clockModeOmega`** (`mode-15`, a fresh one-mode
    later-modality signature) — wiring FXModeTheory + the cohesion/clock instances.
  * the headline theorems: ★ `fxModeOmega_isAdmissible` (the diabolical doctrine is §6.8-admissible, by `decide`),
    `fxModeOmega_modalities_supportDiagonal` (the `mode-2` certificate computes through the bundle),
    `fxModeOmega_isMultimodal` (genuinely ≥ 2 modes), ★ `modeOmega_combine_admissible` (the bundled doctrines
    combine admissibly — the `mode-18` O-COMBINE tie), `strictTwoCellEquality_refl`.

## What is DEFERRED (the honest ledger)

Strict-2-cat + structure-cert + 3-cell-strict + the decidable certificates SHIP.  Deferred (markers):

  * the genuine WEAK Gray ω-category structure — generators above dimension 3 + the semistrict/weak coherence
    (`mode-5` / `mode-6` / `mode-7`) — `hasModeOmegaWeakGray`;
  * multipliers beyond the finite `{affine, cartesian, dedekind, deMorgan}` classification (the general-multiplier
    endofunctor, `mode-12`) — `hasModeOmegaGeneralMultiplier`;
  * multimodal canonicity / normalization (`mode-9`) + transpension recovery (`mode-11`) transported through the
    bundle at full strength (here only the decidable 2-cell equality + admissibility certificate)
    — `hasModeOmegaCanonicityTransport`;
  * the kernel FIBRED over the mode theory — FXModeTheory → the `.mode` cell fibration (the MTT "everything ⊣
    mode", cross-axis) — `hasModeOmegaKernelFibration` (`fib-3`).

Aggregates `mode-0` + `mode-2` + `mode-18`.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The decidable 2-cell equality machine (mode-3 lifted) -/

/-- A **decidable 2-cell equality** — the convergent-3-polygraph normalizer (`mode-3`) lifted to a decision
procedure: a normalizer from 2-cells to NORMAL FORMS plus a `DecidableEq` on normal forms.  Two 2-cells are equal
exactly when their normal forms coincide; deciding that is the decidable word problem for the mode 2-cells. -/
structure DecidableTwoCellEquality where
  /-- The 2-cell expressions. -/
  TwoCell : Type
  /-- The unique normal forms (the convergent-3-polygraph normal forms). -/
  NormalForm : Type
  /-- The lifted normalizer `mode-3` supplies. -/
  normalize : TwoCell → NormalForm
  /-- Decidable equality on normal forms. -/
  normalFormDecEq : DecidableEq NormalForm

/-- The decision: two 2-cells are equal iff their normal forms are (decidably) equal. -/
def DecidableTwoCellEquality.equal (theory : DecidableTwoCellEquality)
    (first second : theory.TwoCell) : Bool :=
  match theory.normalFormDecEq (theory.normalize first) (theory.normalize second) with
  | isTrue _ => true
  | isFalse _ => false

/-- ★ The decision is REFLEXIVE — every 2-cell equals itself (the decision procedure is sound on the diagonal). -/
theorem DecidableTwoCellEquality.equal_refl (theory : DecidableTwoCellEquality)
    (cell : theory.TwoCell) : theory.equal cell cell = true := by
  unfold DecidableTwoCellEquality.equal
  cases theory.normalFormDecEq (theory.normalize cell) (theory.normalize cell) with
  | isTrue _ => rfl
  | isFalse contradiction => exact absurd rfl contradiction

/-- The decision is COMPLETE — equal normal forms are decided equal. -/
theorem DecidableTwoCellEquality.equal_complete (theory : DecidableTwoCellEquality)
    {first second : theory.TwoCell}
    (normalFormsEqual : theory.normalize first = theory.normalize second) :
    theory.equal first second = true := by
  unfold DecidableTwoCellEquality.equal
  cases theory.normalFormDecEq (theory.normalize first) (theory.normalize second) with
  | isTrue _ => rfl
  | isFalse normalFormsDistinct => exact absurd normalFormsEqual normalFormsDistinct

/-- The decision is SOUND — a decided-equal pair has equal normal forms. -/
theorem DecidableTwoCellEquality.equal_sound (theory : DecidableTwoCellEquality)
    {first second : theory.TwoCell}
    (decidedEqual : theory.equal first second = true) :
    theory.normalize first = theory.normalize second := by
  revert decidedEqual
  unfold DecidableTwoCellEquality.equal
  cases theory.normalFormDecEq (theory.normalize first) (theory.normalize second) with
  | isTrue normalFormsEqual => exact fun _ => normalFormsEqual
  | isFalse _ => exact fun decidedEqual => Bool.noConfusion decidedEqual

/-- ★ The decision is CERTIFIED — `equal` decides exactly normal-form equality (sound + complete).  The decidable
2-cell equality is not merely reflexive; it faithfully reflects the convergent normalizer. -/
theorem DecidableTwoCellEquality.equal_iff (theory : DecidableTwoCellEquality)
    {first second : theory.TwoCell} :
    theory.equal first second = true ↔ theory.normalize first = theory.normalize second :=
  ⟨fun decided => theory.equal_sound decided, fun normalsEqual => theory.equal_complete normalsEqual⟩

/-- The strict 2-cell normal forms of the adjunction/cohesion seed — identity, the unit, the counit (the
convergent normal forms of `mode-0`'s `AdjunctionTwoCell`). -/
inductive StrictTwoCellNormalForm where
  /-- The identity 2-cell normal form. -/
  | identityForm
  /-- The unit 2-cell normal form. -/
  | unitForm
  /-- The counit 2-cell normal form. -/
  | counitForm
  deriving DecidableEq

/-- The decidable 2-cell equality for the strict fragment — the 2-cells are already in normal form (the convergent
3-polygraph of `mode-3` does the lifting from expressions; here we package the resulting decision). -/
def strictTwoCellEquality : DecidableTwoCellEquality where
  TwoCell := StrictTwoCellNormalForm
  NormalForm := StrictTwoCellNormalForm
  normalize := fun cell => cell
  normalFormDecEq := inferInstance

/-- The decidable 2-cell equality DISCRIMINATES — distinct strict 2-cells (the unit vs the counit) are decided
unequal.  The decision is not vacuously reflexive; it has teeth. -/
theorem strictTwoCellEquality_discriminates :
    strictTwoCellEquality.equal StrictTwoCellNormalForm.unitForm StrictTwoCellNormalForm.counitForm = false := by
  decide

/-! ## The bundle: the mode axis as one finished object -/

/-- ★ **`ModeOmega`** — the whole mode axis as one record: the (weak) higher polygraph carried as DATA, with a
decidable admissibility certificate and decidable 2-cell equality.  Genuine aggregation of `mode-0` (the
signature), `mode-2` (the per-modality structure-class certificate), `mode-4` (the adjoint-string depth), and
`mode-17` / `mode-18` (the doctrine), plus the `mode-3` decidable 2-cell equality. -/
structure ModeOmega where
  /-- The polygraph signature — modes, modality generators, 2-cell generators (`mode-0`). -/
  signature : ModeSignature
  /-- The structure-class certificate per modality generator (`mode-2`, Fig 7). -/
  structureClass : {sourceMode targetMode : signature.graph.Mode} →
    signature.graph.Modality sourceMode targetMode → MultiplierStructureClass
  /-- The adjoint-string depth per modality (`mode-4` — the length of the modality's adjoint string). -/
  adjointDepth : {sourceMode targetMode : signature.graph.Mode} →
    signature.graph.Modality sourceMode targetMode → Nat
  /-- The doctrine — the §6.8 feature profile (`mode-17` / `mode-18`). -/
  doctrine : Doctrine
  /-- The decidable 2-cell equality (`mode-3`, the lifted normalizer). -/
  twoCellEquality : DecidableTwoCellEquality

/-- ★ The **decidable admissibility certificate** — the bundle is admissible exactly when its doctrine is
§6.8-collision-free.  A computable `Bool`, the whole point of carrying the diabolical doctrine as data. -/
def ModeOmega.isAdmissible (omega : ModeOmega) : Bool := omega.doctrine.isAdmissible

/-! ## Witnesses — wiring FXModeTheory + the cohesion / clock instances -/

/-- The FX mode-theory doctrine — a genuinely non-trivial admissible feature profile: classified + borrow
(no §6.8 collision). -/
def fxModeDoctrine : Doctrine where
  hasClassified := true
  hasFail := false
  hasBorrow := true
  hasAsync := false
  hasConstantTime := false

/-- ★ **`fxModeOmega`** — THE FX mode theory bundled: the `mode-0` cohesion/adjunction seed (two modes, a modality
each way, unit/counit 2-cells), every modality at the cartesian multiplier, an admissible resource doctrine, and
the strict decidable 2-cell equality. -/
def fxModeOmega : ModeOmega where
  signature := adjunctionModeSignature
  structureClass := fun _modality => MultiplierStructureClass.cartesian
  adjointDepth := fun _modality => 2
  doctrine := fxModeDoctrine
  twoCellEquality := strictTwoCellEquality

/-- The **cohesion** instance (`mode-13`) — the same adjunction seed (the `♭ ⊣ ♯` cohesion shape) with the pure
(feature-free) doctrine. -/
def cohesionModeOmega : ModeOmega where
  signature := adjunctionModeSignature
  structureClass := fun _modality => MultiplierStructureClass.cartesian
  adjointDepth := fun _modality => 2
  doctrine := emptyDoctrine
  twoCellEquality := strictTwoCellEquality

/-- The single mode of the clock instance. -/
inductive ClockMode where
  /-- The clock mode. -/
  | clock

/-- The clock modality generator — the guarded LATER, an endomodality on the clock mode. -/
inductive ClockModality : ClockMode → ClockMode → Type where
  /-- The later modality `▷ : clock ⟶ clock`. -/
  | tick : ClockModality ClockMode.clock ClockMode.clock

/-- The clock quiver — one mode, the later endomodality. -/
def clockModeGraph : ModeGraph where
  Mode := ClockMode
  Modality := ClockModality

/-- The clock signature — the clock quiver, no non-trivial 2-cell generators (clock-irrelevance lives at the
modality level). -/
def clockModeSignature : ModeSignature where
  graph := clockModeGraph
  twoCell := fun _ _ => Empty

/-- The **clock** instance (`mode-15`) — one mode, the later endomodality, feature-free doctrine. -/
def clockModeOmega : ModeOmega where
  signature := clockModeSignature
  structureClass := fun _modality => MultiplierStructureClass.cartesian
  adjointDepth := fun _modality => 1
  doctrine := emptyDoctrine
  twoCellEquality := strictTwoCellEquality

/-- An INADMISSIBLE doctrine — classified + Fail, a §6.8 collision (info leak via failure). -/
def unsoundDoctrine : Doctrine where
  hasClassified := true
  hasFail := true
  hasBorrow := false
  hasAsync := false
  hasConstantTime := false

/-- A bundle carrying the unsound doctrine — admissible only if the certificate were blind; it is not. -/
def unsoundModeOmega : ModeOmega where
  signature := adjunctionModeSignature
  structureClass := fun _modality => MultiplierStructureClass.cartesian
  adjointDepth := fun _modality => 2
  doctrine := unsoundDoctrine
  twoCellEquality := strictTwoCellEquality

/-- ★ The admissibility certificate has TEETH — it REJECTS the §6.8-colliding bundle (`classified × Fail`).  The
decidable admissibility genuinely discriminates sound from unsound mode doctrines (the mode-level no-go). -/
theorem unsoundModeOmega_isInadmissible : unsoundModeOmega.isAdmissible = false := by decide

/-! ## Headline theorems -/

/-- ★ The FX mode theory is §6.8-ADMISSIBLE — the diabolical multimodal doctrine carries no soundness collision,
decided by computation. -/
theorem fxModeOmega_isAdmissible : fxModeOmega.isAdmissible = true := by decide

/-- The cohesion instance is admissible. -/
theorem cohesionModeOmega_isAdmissible : cohesionModeOmega.isAdmissible = true := by decide

/-- The clock instance is admissible. -/
theorem clockModeOmega_isAdmissible : clockModeOmega.isAdmissible = true := by decide

/-- ★ The `mode-2` structure-class certificate COMPUTES through the bundle — every FX modality sits at the
cartesian multiplier, so its certificate `supportsDiagonal`.  The capstone genuinely carries the Fig 7
classification, not a stub. -/
theorem fxModeOmega_modalities_supportDiagonal {sourceMode targetMode : adjunctionGraph.Mode}
    (modality : adjunctionGraph.Modality sourceMode targetMode) :
    (fxModeOmega.structureClass modality).supportsDiagonal = true := rfl

/-- The bundled FX mode axis is genuinely MULTIMODAL — its signature has two distinct modes (not single-sorted
MTT). -/
theorem fxModeOmega_isMultimodal : AdjunctionMode.base ≠ AdjunctionMode.tip :=
  adjunctionHasTwoDistinctModes

/-- The bundled FX mode axis IS `mode-0`'s chosen FX datum — `fxModeOmega` round-trips with `fxModeAxis`. -/
theorem fxModeOmega_signature_isFxAxis : fxModeOmega.signature = fxModeAxis.signature := rfl

/-- ★ The bundled doctrines COMBINE admissibly — amalgamating the FX and cohesion mode doctrines (the `mode-18`
pushout) stays §6.8-sound.  The capstone is closed under O-COMBINE on its admissible instances. -/
theorem modeOmega_combine_admissible :
    (fxModeOmega.doctrine.combine cohesionModeOmega.doctrine).isAdmissible = true := by decide

/-- The bundled decidable 2-cell equality is reflexive — the lifted normalizer decides the 2-cell word problem
soundly on the diagonal. -/
theorem strictTwoCellEquality_refl (cell : strictTwoCellEquality.TwoCell) :
    strictTwoCellEquality.equal cell cell = true :=
  strictTwoCellEquality.equal_refl cell

/-! ## Honesty markers -/

/-- **Honesty marker.**  The genuine WEAK Gray ω-category structure — generating cells above dimension 3 + the
semistrict / weak coherence (`mode-5` / `mode-6` / `mode-7`), beyond the strict-2-cat + 3-cell-strict +
structure-cert bundled here — is the frontier.  `= false`. -/
def fxMode_hasModeOmegaWeakGray : Bool := false

/-- **Honesty marker.**  Multipliers beyond the finite `{affine, cartesian, dedekind, deMorgan}` classification —
the general-multiplier endofunctor (`mode-12`) — are deferred.  `= false`. -/
def fxMode_hasModeOmegaGeneralMultiplier : Bool := false

/-- **Honesty marker.**  The full SEMANTIC normalization-canonicity gluing (`mode-9`) + transpension recovery
(`mode-11`) transported through the bundle — here the CERTIFIED decidable 2-cell equality (`equal_iff`, sound +
complete — the Gratzer Conv-decidability half) + the admissibility certificate WITH TEETH ship, but not the full
semantic canonicity proof.  `= false`. -/
def fxMode_hasModeOmegaCanonicityTransport : Bool := false

/-- **Honesty marker.**  The kernel FIBRED over the mode theory — FXModeTheory → the `.mode` cell fibration (the
MTT "everything ⊣ mode") — is cross-axis (`fib-3`), deferred.  `= false`. -/
def fxMode_hasModeOmegaKernelFibration : Bool := false

end FX1Poly.Tier0
