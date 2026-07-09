import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleSaturatedConv
import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionNonThinness

/-! # WalkingCohesionQuadruple/QuadrupleThinFragment — the thin fragment, the decision-modulo, and the HONEST route

r1 (`QuadrupleSeed` / `QuadrupleSaturatedConv`) shipped the functor-level walking cohesion quadruple
`Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` (with `Disc`, `coDisc` fully faithful) and its saturated 2-cell convertibility.  This
file ships the THINNESS analysis: the decision assembly MODULO local posetality, the THIN FRAGMENT that is proved
outright, a sound `ℤ/2` parity invariant, and — HONESTLY — the route statement, because the recon hand-enumeration
DECIDES the route here, and the answer is NOT the recon's optimistic "non-thin via pullback."

## What the hand-enumeration actually finds (the route decision)

The recon anticipated a non-thin FINDING lifted from the induced-modality quotient (`WalkingCohesion`, machine-
refuted non-thin).  Working it out at the FUNCTOR level overturns that:

  * **Every adjunction here is a REFLECTION** (`Disc` ff below and in the middle, `coDisc` ff above).  Each shared
    leg (`disc`, `gamma`) is straightened by TWO triangles, and the ff-iso round-trips collapse the reflections'
    loops — so the low-complexity boundaries ENUMERATE AS THIN: each `pi0`/`disc`/`gamma`/`codisc` leg straightens
    to its identity, and the two snakes on each shared leg cohere (`quadDiscSnakesCohere`, `quadGammaSnakesCohere`).
  * **The induced refutation does NOT lift.**  The `WalkingCohesion` non-thinness (a `pi0`-parity separating the
    shape monad unit from a lower-adjunction route) came from the induced presentation's SEPARATE adjunction-unit
    and comonad-counit generators.  At the functor level those are DERIVED, not primitive, and there is NO clean
    strict 2-functor `quadruple ↠ induced`: `disc` and `gamma` each STRADDLE two adjunctions, so any map sending
    the length-2 composites `pi0·disc`, `gamma·disc`, `gamma·codisc` onto the single induced generators
    over-constrains the shared legs (sending `disc ↦ id` to collapse `pi0·disc ↦ shape` then forces `gamma·codisc`
    to be `gamma·codisc`, contradicting `♯ ↦ sharp`).  The pullback the recon leaned on does not exist.
  * **A sound `ℤ/2` invariant finds NO low-complexity separator.**  Instantiating the generic `genParity`
    (`WalkingCohesion/CohesionNonThinness`) with a `pi0`-adjunction weighting gives a sound congruence invariant
    (`quadCohesionParity_satConv`); it AGREES on every enumerated parallel pair (they are all convertible), unlike
    the induced lane where it SEPARATED a pair.  This is positive evidence that the functor level is thin-leaning
    — the non-thinness of the cohesive modalities is an ARTIFACT of the induced quotient's redundant generators.

## Disposition (route: FRAGMENT — thin fragment proved, global thinness OPEN, no flip)

So the honest verdict is the FRAGMENT route (neither a non-thin finding nor a global thin decision): the thin
FRAGMENT is proved outright (leg straightenings + shared-leg coherences + ff-iso collapses), the decision
ASSEMBLY modulo posetality is shipped (`decideQuadCohesionConvViaThinness`), and the FULL
`QuadCohesionLocalPosetality` is left NEITHER inhabited NOR refuted — global thinness is the OPEN residual, which
(unlike the induced quotient) is plausibly TRUE but would need a full normalizer, exactly the closure
`WalkingIdempotent`'s `normalizeFull` supplied for the single-letter idempotent walker.  `fxMode`-side cohesion
computation stays gated on this residual; NO thinness claim is forced.

Raw Lean 4 + Init; the fragment collapses are constructor chains, the parity soundness is structural induction
over the `Prop` relation, the decision is `Decidable`-plumbing — every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The thin fragment: the six reflection legs straighten -/

/-- The `Π₀ ⊣ Disc` snake on `pi0` straightens to `id_pi0`. -/
theorem quadTriPi0_straightens :
    QuadCohesionSaturatedTwoCellConv quadTriPi0SnakeCell quadPi0IdCell :=
  QuadCohesionSaturatedTwoCellConv.triPi0

/-- The `Π₀ ⊣ Disc` snake on `disc` straightens to `id_disc`. -/
theorem quadTriDiscLo_straightens :
    QuadCohesionSaturatedTwoCellConv quadTriDiscLoSnakeCell quadDiscIdCell :=
  QuadCohesionSaturatedTwoCellConv.triDiscLo

/-- The `Disc ⊣ Γ` snake on `disc` straightens to `id_disc`. -/
theorem quadTriDiscHi_straightens :
    QuadCohesionSaturatedTwoCellConv quadTriDiscHiSnakeCell quadDiscIdCell :=
  QuadCohesionSaturatedTwoCellConv.triDiscHi

/-- The `Disc ⊣ Γ` snake on `gamma` straightens to `id_gamma`. -/
theorem quadTriGammaLo_straightens :
    QuadCohesionSaturatedTwoCellConv quadTriGammaLoSnakeCell quadGammaIdCell :=
  QuadCohesionSaturatedTwoCellConv.triGammaLo

/-- The `Γ ⊣ coDisc` snake on `gamma` straightens to `id_gamma`. -/
theorem quadTriGammaHi_straightens :
    QuadCohesionSaturatedTwoCellConv quadTriGammaHiSnakeCell quadGammaIdCell :=
  QuadCohesionSaturatedTwoCellConv.triGammaHi

/-- The `Γ ⊣ coDisc` snake on `codisc` straightens to `id_codisc`. -/
theorem quadTriCodisc_straightens :
    QuadCohesionSaturatedTwoCellConv quadTriCodiscSnakeCell quadCodiscIdCell :=
  QuadCohesionSaturatedTwoCellConv.triCodisc

/-- ★ **The thin fragment is real** — the six reflection legs all straighten to their identities.  Together with
the two shared-leg snake coherences (`quadDiscSnakesCohere`, `quadGammaSnakesCohere`) and the three ff-iso
round-trip collapses (`quadLowerCounitIsInvertible` etc.), these are the concrete populated homs where the
quadruple's local posetality is PROVED outright — the non-vacuous thin fragment the decision consumes. -/
theorem quadThinFragment_legsStraighten :
    QuadCohesionSaturatedTwoCellConv quadTriPi0SnakeCell quadPi0IdCell ∧
      QuadCohesionSaturatedTwoCellConv quadTriDiscLoSnakeCell quadDiscIdCell ∧
      QuadCohesionSaturatedTwoCellConv quadTriDiscHiSnakeCell quadDiscIdCell ∧
      QuadCohesionSaturatedTwoCellConv quadTriGammaLoSnakeCell quadGammaIdCell ∧
      QuadCohesionSaturatedTwoCellConv quadTriGammaHiSnakeCell quadGammaIdCell ∧
      QuadCohesionSaturatedTwoCellConv quadTriCodiscSnakeCell quadCodiscIdCell :=
  ⟨quadTriPi0_straightens, quadTriDiscLo_straightens, quadTriDiscHi_straightens,
    quadTriGammaLo_straightens, quadTriGammaHi_straightens, quadTriCodisc_straightens⟩

/-! ## The sound `ℤ/2` parity invariant (reusing the generic `genParity`) -/

/-- The `ℤ/2` weight of each quadruple generator: the three `Π₀ ⊣ Disc` cells (`unitLower`, `counitLower`,
`invCounitLower`) weigh `true`, every other generator weighs `false`.  Full nine-constructor enumeration, constant
`Bool` motive (a wildcard arm would leak `propext`).  The choice balances EVERY saturation row: each triangle and
each ff-iso round-trip pairs two same-adjunction cells (`true^^true` or `false^^false`, both `= false = id`). -/
def quadCohesionGeneratorParity {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (generator : QuadCohesionTwoCell sourcePath targetPath) : Bool :=
  match generator with
  | .unitLower => true
  | .counitLower => true
  | .invCounitLower => true
  | .unitMiddle => false
  | .counitMiddle => false
  | .invUnitMiddle => false
  | .unitUpper => false
  | .counitUpper => false
  | .invCounitUpper => false

/-- ★ The **quadruple parity degree** — the generic `genParity` at the quadruple signature with the
`Π₀ ⊣ Disc`-adjunction weighting.  A sound congruence invariant. -/
def quadCohesionParity {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) : Bool :=
  genParity quadCohesionGeneratorParity cell

/-- ★ **Quadruple parity is a sound invariant of the saturated quadruple congruence.**  Convertible free 2-cells
have equal parity — the completed convertibility (`ofFull`, via the generic `genParity_convFull`), every triangle
and every ff-iso round-trip balances (each `rfl`), and the congruences propagate.  Hence any parity DIFFERENCE
proves non-convertibility (the tool that WOULD exhibit non-thinness were a low-complexity separator to exist). -/
theorem quadCohesionParity_satConv {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath}
    (conv : QuadCohesionSaturatedTwoCellConv cellAlpha cellBeta) :
    quadCohesionParity cellAlpha = quadCohesionParity cellBeta := by
  induction conv with
  | ofFull convFull => exact genParity_convFull quadCohesionGeneratorParity convFull
  | triPi0 => rfl
  | triDiscLo => rfl
  | triDiscHi => rfl
  | triGammaLo => rfl
  | triGammaHi => rfl
  | triCodisc => rfl
  | isoLowerCounitRight => rfl
  | isoLowerCounitLeft => rfl
  | isoMiddleUnitRight => rfl
  | isoMiddleUnitLeft => rfl
  | isoUpperCounitRight => rfl
  | isoUpperCounitLeft => rfl
  | vcompCongrLeft cellBeta _ ih => exact congrArg (fun bit => bit.xor (quadCohesionParity cellBeta)) ih
  | vcompCongrRight cellAlpha _ ih => exact congrArg (fun bit => (quadCohesionParity cellAlpha).xor bit) ih
  | whiskerLeftCongr _ _ ih => exact ih
  | whiskerRightCongr _ _ ih => exact ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Non-triviality: the parity is not constant — the lower unit `η` weighs `true` (it IS the weighted generator)
while any identity weighs `false`.  So `quadCohesionParity` is a genuine `ℤ/2` homomorphism, not the degenerate
everything-`false` map. -/
theorem quadCohesionParity_unitLower : quadCohesionParity quadUnitLowerCell = true := rfl

/-- The lower-counit round-trip (a genuine size-3 composite) weighs `false` — `counitLower ^^ invCounitLower =
true ^^ true` — matching its identity, consistent with the ff-iso law identifying them. -/
theorem quadCohesionParity_lowerRoundRight :
    quadCohesionParity quadLowerCounitRoundRightCell = false := rfl

/-- ★ **The invariant AGREES on a genuine identification** (non-degeneracy).  The two shared-`disc` snakes cohere
(`quadDiscSnakesCohere`), and the parity invariant respects that: both weigh `false`.  So `quadCohesionParity`
respects a genuinely-convertible pair — it is a real invariant, and its FAILURE to separate any enumerated
parallel pair is honest evidence for the thin fragment (contrast the induced lane, where the analogous invariant
DID separate a parallel pair). -/
theorem quadCohesionParity_agreesOnDiscSnakes :
    quadCohesionParity quadTriDiscLoSnakeCell = quadCohesionParity quadTriDiscHiSnakeCell :=
  quadCohesionParity_satConv quadDiscSnakesCohere

/-! ## Local posetality (thinness) and the decision modulo it -/

/-- ★ **Local posetality (thinness)** of the walking cohesion quadruple: ANY two parallel free 2-cells are
convertible — every hom is a poset with at most one 2-cell.  Proved on the thin fragment (leg straightenings +
shared-leg coherences + ff-iso collapses) and left as the OPEN residual on the general boundary (would need a full
normalizer, as `WalkingIdempotent`). -/
def QuadCohesionThinness : Prop :=
  ∀ {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath),
    QuadCohesionSaturatedTwoCellConv cellA cellB

/-- The walking cohesion quadruple's **local-posetality** package — the thinness collapse the decision needs.
Mirrors `CohesionLocalPosetality` / `IdempotentMonadLocalPosetality`: a single field whose full mechanization is
the OPEN residual (the general-boundary normalizer). -/
structure QuadCohesionLocalPosetality where
  /-- All parallel free 2-cells are convertible (at most one 2-cell per hom). -/
  allParallelConv : QuadCohesionThinness

/-- ★ **Decide walking-cohesion-quadruple saturated convertibility via thinness.**  Given local posetality, any
parallel pair is convertible, so the decision is `isTrue` unconditionally.  Complete and zero-axiom — the
`isFalse` branch never occurs because there are no non-convertible parallel pairs. -/
def decideQuadCohesionConvViaThinness (posetality : QuadCohesionLocalPosetality)
    {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) :
    Decidable (QuadCohesionSaturatedTwoCellConv cellA cellB) :=
  isTrue (posetality.allParallelConv cellA cellB)

/-- The walking cohesion quadruple's **saturated 2-cell word-problem interface**: saturated convertibility is
decidable on every parallel pair of free 2-cells. -/
abbrev QuadCohesionDecidableSaturatedTwoCellConvFor : Type :=
  {sourceMode targetMode : QuadCohesionMode} →
  {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode} →
  (cellA cellB : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) →
  Decidable (QuadCohesionSaturatedTwoCellConv cellA cellB)

/-- ★ **The walking cohesion quadruple's saturated 2-cell word problem, modulo local posetality.**  Supplying the
thinness collapse inhabits the full saturated decision interface — it decides EVERY parallel pair. -/
@[reducible] def quadCohesionSaturatedWordProblemModuloPosetality
    (posetality : QuadCohesionLocalPosetality) : QuadCohesionDecidableSaturatedTwoCellConvFor :=
  fun cellA cellB => decideQuadCohesionConvViaThinness posetality cellA cellB

/-- Smoke: were thinness supplied, the decision fires — `decideQuadCohesionConvViaThinness` on any parallel pair
is `isTrue`.  Stated as a function OF a posetality witness, so it is honest that the FULL decision is modulo the
OPEN residual — no unproven `isTrue` is manufactured; only the thin fragment is proved outright. -/
theorem decideQuadCohesion_isTrue_ofPosetality (posetality : QuadCohesionLocalPosetality) :
    ∀ {sourceMode targetMode : QuadCohesionMode}
      {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
      (cellA cellB : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath),
      QuadCohesionSaturatedTwoCellConv cellA cellB :=
  fun cellA cellB => posetality.allParallelConv cellA cellB

/-! ## Non-vacuity: a genuine identification + a genuine separation -/

/-- ★ **Genuine identification** (cross-adjunction coherence doing real work): the two shared-`disc` snakes — the
lower `Π₀ ⊣ Disc` snake and the middle `Disc ⊣ Γ` snake, syntactically distinct size-3 cells — are convertible,
both collapsing to `id_disc`.  A populated hom (`disc ⇒ disc`) where the thinness is proved outright. -/
theorem quadDecision_genuineIdentification :
    QuadCohesionSaturatedTwoCellConv quadTriDiscLoSnakeCell quadTriDiscHiSnakeCell :=
  quadDiscSnakesCohere

/-- ★ **Genuine separation / non-degeneracy**: the four functors are DISTINCT 1-cells (`pi0 ≠ gamma`,
`disc ≠ codisc`) and the induced modalities `ʃ = pi0·disc`, `♭ = gamma·disc` are distinct — so the quadruple is no
degenerate single-functor collapse, and the word problem is non-trivial. -/
theorem quadDecision_genuineSeparation :
    quadPi0 ≠ quadGamma ∧ quadDisc ≠ quadCodisc ∧ quadPi0Disc ≠ quadGammaDisc :=
  ⟨quadPi0_ne_gamma, quadDisc_ne_codisc, quadPi0Disc_ne_gammaDisc⟩

/-! ## P5 — the reflections' idempotency law demo (ff ⟹ idempotent (co)monad) -/

/-- ★ **The three reflections are idempotent (co)monads** — the functor-level source of the induced modality
idempotence.  Each fully-faithful leg's unit/counit is a two-sided iso (`quadLowerCounitIsInvertible` /
`quadMiddleUnitIsInvertible` / `quadUpperCounitIsInvertible`); by nLab (*reflective subcategory*: ff ⟺ counit iso
⟺ induced monad idempotent, dually for the comonad), this is EXACTLY the idempotence of the induced modalities
`ʃ = pi0·disc`, `♭ = gamma·disc`, `♯ = gamma·codisc` that `WalkingCohesion`'s `shapeIdempotence` /
`flatIdempotence` / `sharpIdempotence` POSIT as generators.  Here idempotence is DERIVED from full faithfulness —
the finer presentation's payoff. -/
theorem quadReflectionsAreIdempotent :
    (QuadCohesionSaturatedTwoCellConv quadLowerCounitRoundRightCell quadDiscPi0IdCell ∧
        QuadCohesionSaturatedTwoCellConv quadLowerCounitRoundLeftCell quadNilPointSetIdCell) ∧
      (QuadCohesionSaturatedTwoCellConv quadMiddleUnitRoundRightCell quadNilPointSetIdCell ∧
        QuadCohesionSaturatedTwoCellConv quadMiddleUnitRoundLeftCell quadDiscGammaIdCell) ∧
      (QuadCohesionSaturatedTwoCellConv quadUpperCounitRoundRightCell quadCodiscGammaIdCell ∧
        QuadCohesionSaturatedTwoCellConv quadUpperCounitRoundLeftCell quadNilPointSetIdCell) :=
  ⟨quadLowerCounitIsInvertible, quadMiddleUnitIsInvertible, quadUpperCounitIsInvertible⟩

/-! ## P4 — bridge notes (docstrings only): ZOO-COHESION + MODE-ADMIT -/

/-- **Bridge note (docstrings only) — the ZOO-COHESION and MODE-ADMIT consumption points.**

  * **ZOO-COHESION (Tier0 `Mode/CohesionModalityMetatheory`, `Mode/Transpension`).**  The Tier0 cohesion modality
    zoo consumes an idempotence/adjoint-string presentation for the `ʃ ⊣ ♭ ⊣ ♯` modalities.  This quadruple lane
    is the FUNCTOR-level refinement one granularity below the induced `WalkingCohesion` presentation the zoo
    currently references: it exhibits the induced (co)monad idempotence as DERIVED from `Disc`/`coDisc` full
    faithfulness (`quadReflectionsAreIdempotent`), the honest provenance the zoo's `fxMode`-side cohesion markers
    want.  No Tier0 edit here — this is the note.

  * **MODE-ADMIT (`Amalgam/ModeAdmit`, the registry gate #2214).**  MODE-ADMIT admits a presented mode theory by
    matching it against a registry of DECIDED walkers and handing back the packaged decider.  A quadruple decider
    would register here ONCE the global decision closes.  It does NOT register yet: the decision is only MODULO
    posetality (`decideQuadCohesionConvViaThinness`), and global thinness is the OPEN residual — so
    `fxQuadCohesion_isModeAdmitRegistryCandidate = false`.  When the general-boundary normalizer lands (the
    `WalkingIdempotent`-style closure), this lane becomes a registry candidate; until then the gate must not
    consume it.  This is the note only. -/
def fxQuadCohesion_isModeAdmitRegistryCandidate : Bool := false

/-! ## Honesty markers -/

/-- ★ **ESTABLISHED — the quadruple presentation ships.**  The functor-level walking cohesion quadruple
`Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` with `Disc`, `coDisc` fully faithful is presented (`QuadrupleSeed`), its saturated
convertibility is a congruence (`QuadrupleSaturatedConv`), and the reflections' idempotency is derived
(`quadReflectionsAreIdempotent`).  `= true`. -/
def fxQuadCohesion_hasQuadruplePresentation : Bool := true

/-- ★ **ESTABLISHED — the decision assembly modulo thinness + the thin fragment.**  The saturated decision is
shipped MODULO `QuadCohesionLocalPosetality` (the assembly `decideQuadCohesionConvViaThinness` /
`quadCohesionSaturatedWordProblemModuloPosetality` is complete and zero-axiom), and the thin FRAGMENT is proved
outright: the six reflection legs straighten (`quadThinFragment_legsStraighten`), both shared legs' snakes cohere
(`quadDiscSnakesCohere`, `quadGammaSnakesCohere`), the three ff-iso round-trips collapse, and the decision is
non-vacuous (`quadDecision_genuineIdentification` + `quadDecision_genuineSeparation`).  `= true`. -/
def fxQuadCohesion_hasDecisionAssemblyModuloThinness : Bool := true

/-- ★★ **HONEST WALL — the QUADRUPLE THINNESS is UNRESOLVED (NOT flipped, NOT refuted).**  The route
hand-enumeration finds the low-complexity boundaries THIN (every reflection leg straightens; the ff-iso
round-trips collapse the loops), a sound `ℤ/2` invariant (`quadCohesionParity_satConv`) finds NO low-complexity
separator, and — crucially — the induced-quotient non-thinness (`WalkingCohesion`, machine-refuted) does NOT lift:
`disc`/`gamma` straddle two adjunctions, so there is no clean strict 2-functor `quadruple ↠ induced` to pull the
refutation back.  So `QuadCohesionThinness` is left NEITHER inhabited (would need a full general-boundary
normalizer, the `WalkingIdempotent.normalizeFull`-style closure — NOT attempted this round) NOR refuted (no
separator exists at low complexity — the functor level is thin-LEANING, diverging from the induced quotient).
This is the honest FRAGMENT disposition: the presentation, the soundness, the thin fragment, and the decision
assembly ship; the GLOBAL thinness claim is NOT forced, and the downstream cohesion computation stays gated.
`= false`. -/
def fxQuadCohesion_hasQuadrupleThinnessResolution : Bool := false

end FX1Poly.Polygraph
