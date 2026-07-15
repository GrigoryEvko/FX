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

/-! ## The `pi0`-letter parity obstruction — the induced refutation provably does NOT lift

r1 hand-waved "the `WalkingCohesion` non-thinness refutation does not lift to the quadruple".  This section
PROVES it.  The induced refutation (`CohesionNonThinness`) worked because there `cohesionParity` weighs the
primitive shape unit `η^ʃ` at the ENDO boundary `id ⇒ shape` with `true` while a parallel route weighs `false` —
the weight is NOT determined by the boundary, so parity SEPARATES a parallel pair.  At the FUNCTOR level the
shape monad is the COMPOSITE `pi0·disc`, so the three parity-`true` generators (`unitLower`, `counitLower`,
`invCounitLower` — the entire `Π₀ ⊣ Disc` column) are exactly the generators that change the `pi0`-LETTER count
of the boundary by an odd amount.  Hence `quadCohesionParity` is a FUNCTION of the boundary
(`pi0`-parity of source XOR of target) — it is CONSTANT on every parallel pair, so it can separate NOTHING.  The
very invariant that killed the induced lane is neutered here; the induced non-thinness has no functor-level
image. -/

/-- A `false` on both sides of an XOR (`false = bit ^^ bit`) — exhaustive `Bool` casing, `propext`-free. -/
private theorem quadXorSelfFalse (bit : Bool) : (false : Bool) = bit.xor bit := by
  cases bit <;> rfl

/-- The vertical-composite XOR telescope `(a ^^ b) ^^ (b ^^ c) = a ^^ c` — exhaustive casing. -/
private theorem quadXorCross (bitA bitB bitC : Bool) :
    (bitA.xor bitB).xor (bitB.xor bitC) = bitA.xor bitC := by
  cases bitA <;> cases bitB <;> cases bitC <;> rfl

/-- The left-whisker XOR cancellation `g ^^ h = (p ^^ g) ^^ (p ^^ h)` — exhaustive casing. -/
private theorem quadXorCancelLeft (bitP bitG bitH : Bool) :
    bitG.xor bitH = (bitP.xor bitG).xor (bitP.xor bitH) := by
  cases bitP <;> cases bitG <;> cases bitH <;> rfl

/-- The right-whisker XOR cancellation `f ^^ g = (f ^^ p) ^^ (g ^^ p)` — exhaustive casing. -/
private theorem quadXorCancelRight (bitP bitF bitG : Bool) :
    bitF.xor bitG = (bitF.xor bitP).xor (bitG.xor bitP) := by
  cases bitP <;> cases bitF <;> cases bitG <;> rfl

/-- The `ℤ/2` PARITY of a free 1-cell (word) under a GENERIC per-generator `Bool` weight — structural XOR fold
over the path, constant `Bool` motive: `propext`-free.  Generic over any `ModeGraph` so the boundary-determined
argument below (which recurses over the free 2-cell family whose paths are typed at `signature.graph`) rewrites
against it without the concrete-graph projection mismatch. -/
def modalityWordParity {graph : ModeGraph}
    (modalityWeight : {sourceMode targetMode : graph.Mode} → graph.Modality sourceMode targetMode → Bool) :
    {sourceMode targetMode : graph.Mode} →
    ModalityPath graph sourceMode targetMode → Bool
  | _, _, .nil _ => false
  | _, _, .cons head rest => (modalityWeight head).xor (modalityWordParity modalityWeight rest)

/-- `modalityWordParity` is a monoid homomorphism `(paths, composePath) -> (Bool, xor)` — structural induction
on the first path (the `∀`-quantified `second` kept in the conclusion so the motive stays general, exactly the
`composePath_assoc` pattern), unit by `Bool.false_xor`, cons by `Bool.xor_assoc`. -/
theorem modalityWordParity_composePath {graph : ModeGraph}
    (modalityWeight : {sourceMode targetMode : graph.Mode} → graph.Modality sourceMode targetMode → Bool)
    {sourceMode middleMode : graph.Mode}
    (first : ModalityPath graph sourceMode middleMode) :
    ∀ {targetMode : graph.Mode} (second : ModalityPath graph middleMode targetMode),
      modalityWordParity modalityWeight (composePath first second)
        = (modalityWordParity modalityWeight first).xor (modalityWordParity modalityWeight second) := by
  induction first with
  | nil _ => intro _ second; exact (Bool.false_xor _).symm
  | cons head rest ih =>
      intro _ second
      show (modalityWeight head).xor (modalityWordParity modalityWeight (composePath rest second)) = _
      rw [ih second]
      exact (Bool.xor_assoc _ _ _).symm

/-- ★★ **`genParity` is BOUNDARY-DETERMINED whenever the generator weight is** — over any signature, if every
generator's weight is the XOR of the `modalityWordParity` of its source and target 1-cells (`hcompat`), then the
whole `genParity` factors through the boundary.  Structural recursion over the free 2-cell family: a generator is
`hcompat`, the identity is `bit ^^ bit`, vertical composition telescopes, and whiskering threads the
`modalityWordParity` homomorphism through the XOR cancellations.  Generic over `signature` so the recursion has
no concrete-graph projection mismatch. -/
theorem genParity_boundaryDetermined {signature : ModeSignature}
    (generatorWeight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Bool)
    (modalityWeight : {sourceMode targetMode : signature.graph.Mode} →
      signature.graph.Modality sourceMode targetMode → Bool)
    (hcompat : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      (generator : signature.twoCell sourcePath targetPath) →
      generatorWeight generator
        = (modalityWordParity modalityWeight sourcePath).xor (modalityWordParity modalityWeight targetPath)) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (cell : RawTwoCellExpr signature sourcePath targetPath) →
    genParity generatorWeight cell
      = (modalityWordParity modalityWeight sourcePath).xor (modalityWordParity modalityWeight targetPath)
  | _, _, _, _, .gen generator => hcompat generator
  | _, _, _, _, .id path => quadXorSelfFalse (modalityWordParity modalityWeight path)
  | _, _, _, _, .vcomp cellAlpha cellBeta => by
      show (genParity generatorWeight cellAlpha).xor (genParity generatorWeight cellBeta) = _
      rw [genParity_boundaryDetermined generatorWeight modalityWeight hcompat cellAlpha,
        genParity_boundaryDetermined generatorWeight modalityWeight hcompat cellBeta]
      exact quadXorCross _ _ _
  | _, _, _, _, .whiskerLeft oneCell cellBeta => by
      show genParity generatorWeight cellBeta = _
      rw [modalityWordParity_composePath, modalityWordParity_composePath,
        genParity_boundaryDetermined generatorWeight modalityWeight hcompat cellBeta]
      exact quadXorCancelLeft _ _ _
  | _, _, _, _, .whiskerRight oneCell cellAlpha => by
      show genParity generatorWeight cellAlpha = _
      rw [modalityWordParity_composePath, modalityWordParity_composePath,
        genParity_boundaryDetermined generatorWeight modalityWeight hcompat cellAlpha]
      exact quadXorCancelRight _ _ _

/-- Whether a modality generator is the pieces functor `pi0 = Π₀` — the only generator that shifts a 1-cell's
`pi0`-letter count.  Full four-case enumeration, constant `Bool` motive: `propext`-free. -/
def isPi0Modality {sourceMode targetMode : QuadCohesionMode}
    (modality : QuadCohesionModality sourceMode targetMode) : Bool :=
  match modality with
  | .pi0 => true
  | .disc => false
  | .gamma => false
  | .codisc => false

/-- The `ℤ/2` PARITY of the number of `pi0` letters in a free 1-cell (word) — `modalityWordParity` at the
`pi0`-detecting weight. -/
def pi0PathParity {sourceMode targetMode : QuadCohesionMode}
    (path : ModalityPath quadCohesionGraph sourceMode targetMode) : Bool :=
  modalityWordParity isPi0Modality path

/-- Each quadruple generator's parity weight IS the `pi0`-parity XOR of its boundary — the `Π₀ ⊣ Disc` column
(`unitLower`/`counitLower`/`invCounitLower`) shifts the `pi0`-count by one (weight `true`), everything else keeps
it (weight `false`).  Nine-constructor `cases` then `rfl`. -/
theorem quadCohesionGeneratorParity_boundaryCompat {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (generator : QuadCohesionTwoCell sourcePath targetPath) :
    quadCohesionGeneratorParity generator
      = (pi0PathParity sourcePath).xor (pi0PathParity targetPath) := by
  cases generator <;> rfl

/-- ★★ **`quadCohesionParity` is BOUNDARY-DETERMINED.**  Every free 2-cell's parity equals the XOR of the
`pi0`-letter parities of its source and target 1-cells — a genuine 2-functor `RawTwoCellExpr -> ℤ/2` that factors
THROUGH the boundary (the generic `genParity_boundaryDetermined` at the quadruple weighting, with the
per-generator compatibility `quadCohesionGeneratorParity_boundaryCompat`).  This is the functor-level fact the
induced lane lacked: there the weight was a free choice, here it is FORCED by the boundary. -/
theorem quadCohesionParity_boundaryDetermined {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) :
    quadCohesionParity cell = (pi0PathParity sourcePath).xor (pi0PathParity targetPath) := by
  exact genParity_boundaryDetermined quadCohesionGeneratorParity isPi0Modality
    quadCohesionGeneratorParity_boundaryCompat cell

/-- ★ **Parity separates NOTHING** — any two parallel free 2-cells have equal `quadCohesionParity` (both equal
the boundary's `pi0`-parity XOR).  This is precisely the negation of the induced lane's separating power: there
`cohesionParity` distinguished a parallel pair; here no boundary hosts a parity difference. -/
theorem quadCohesionParity_constantOnParallel {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) :
    quadCohesionParity cellA = quadCohesionParity cellB := by
  rw [quadCohesionParity_boundaryDetermined cellA, quadCohesionParity_boundaryDetermined cellB]

/-- The `pi0·disc` (`= ʃ`) unit boundary `id_space ⇒ pi0·disc` — the functor-level analog of the induced lane's
`id ⇒ shape` where `cohesionParity` SPLIT a parallel pair — is `quadCohesionParity`-HOMOGENEOUS at value `true`:
its target carries one `pi0` letter (odd), its source none, so EVERY cell over it weighs `true`.  There is no
`false`-parity partner to the lower unit; the induced separator has no image. -/
theorem quadCohesionParity_constantTrueOnShapeUnitBoundary
    (cell : RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) quadPi0Disc) :
    quadCohesionParity cell = true :=
  quadCohesionParity_boundaryDetermined cell

/-- ★★ **THE INDUCED NON-THINNESS REFUTATION DOES NOT LIFT (proved).**  `WalkingCohesion` refuted thinness by
exhibiting a parallel pair at `id ⇒ shape` split by `cohesionParity`.  At the functor level the analogous
invariant `quadCohesionParity` is BOUNDARY-DETERMINED (`quadCohesionParity_boundaryDetermined`), hence CONSTANT
on every parallel pair (`quadCohesionParity_constantOnParallel`) — in particular over the shape-unit boundary
`id_space ⇒ pi0·disc` it is uniformly `true` (`quadCohesionParity_unitLower`).  So the induced lane's separating
mechanism structurally cannot exist here: `disc`/`gamma` straddle two adjunctions, the induced generators become
DERIVED composites, and the `pi0`-column parity that would separate collapses to a boundary function.  The
functor-level quadruple is thin-LEANING, diverging from the induced quotient — the refutation is dead, not
merely absent. -/
theorem quadInducedRefutationDoesNotLift :
    (∀ (cellA cellB : RawTwoCellExpr quadCohesionModeSignature
        (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) quadPi0Disc),
      quadCohesionParity cellA = quadCohesionParity cellB)
      ∧ quadCohesionParity quadUnitLowerCell = true :=
  ⟨fun cellA cellB => quadCohesionParity_constantOnParallel cellA cellB, quadCohesionParity_unitLower⟩

/-! ## The ff-driven reflection critical-pair join on the shared leg `disc` (straddle-pair demo)

Beyond the two cross-adjunction snake coherences r1 shipped (`quadDiscSnakesCohere`, `quadGammaSnakesCohere`),
this is a genuine CRITICAL-PAIR JOIN on the shared leg `disc`, driven by the `Disc`-full-faithful iso.  The hom
`disc ⇒ disc·pi0·disc` is populated by two syntactically distinct constructions — the lower unit whiskered on
`disc`'s LEFT (`disc ◁ η`) and the lower-counit INVERSE whiskered on `disc`'s RIGHT (`ε⁻¹ ▷ disc`) — and they
are convertible.  The join is the classic reflection confluence: insert the `Π₀ ⊣ Disc` triangle
(`triDiscLo`) and let the ff-iso (`isoLowerCounitRight`) collapse the resulting `ε ⊟ ε⁻¹` loop.  The whisker
functoriality it uses is the SHIPPED `whiskerRightVcomp` STEP (whisker-of-vcomp), not the deferred
whisker-by-composite-1-cell brick. -/

/-- The `disc`-right-whiskered lower ff round-trip `(ε ▷ disc) ⊟ (ε⁻¹ ▷ disc)` collapses to `id_{disc·pi0·disc}`:
`whiskerRightVcomp` folds the two whiskers into `(ε ⊟ ε⁻¹) ▷ disc`, `isoLowerCounitRight` collapses
`ε ⊟ ε⁻¹` to `id_{disc·pi0}`, and `whiskerRightId` erases the whisker. -/
theorem quadDiscWhiskeredLowerRoundCollapses :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight quadDisc quadCounitLowerCell)
        (RawTwoCellExpr.whiskerRight quadDisc quadInvCounitLowerCell))
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) (composePath quadDiscPi0 quadDisc)) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerRightVcomp quadDisc quadCounitLowerCell quadInvCounitLowerCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadDisc
      QuadCohesionSaturatedTwoCellConv.isoLowerCounitRight) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) quadDiscPi0 quadDisc)

/-- ★★ **The straddle critical-pair join `disc ◁ η ≈ ε⁻¹ ▷ disc`** over the populated hom
`disc ⇒ disc·pi0·disc`.  Two syntactically distinct 2-cells — the left-whiskered lower unit and the
right-whiskered lower-counit INVERSE — are saturated-convertible: pad `disc ◁ η` with the identity on the
target, expand the identity to `(ε ▷ disc) ⊟ (ε⁻¹ ▷ disc)` (`quadDiscWhiskeredLowerRoundCollapses`
reversed), reassociate, straighten `(disc ◁ η) ⊟ (ε ▷ disc)` to `id_disc` via the `Π₀ ⊣ Disc` triangle
`triDiscLo`, and drop the left identity.  A concrete populated hom where the quadruple's local posetality holds
by an explicit ff-driven join — the thin fragment extended past the leg straightenings and snake coherences. -/
theorem quadStraddleDiscUnitInvCounitJoin :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft quadDisc quadUnitLowerCell)
      (RawTwoCellExpr.whiskerRight quadDisc quadInvCounitLowerCell) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.vcompIdRight (RawTwoCellExpr.whiskerLeft quadDisc quadUnitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerLeft quadDisc quadUnitLowerCell)
      (QuadCohesionSaturatedTwoCellConv.symm quadDiscWhiskeredLowerRoundCollapses)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerLeft quadDisc quadUnitLowerCell)
          (RawTwoCellExpr.whiskerRight quadDisc quadCounitLowerCell)
          (RawTwoCellExpr.whiskerRight quadDisc quadInvCounitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft
      (RawTwoCellExpr.whiskerRight quadDisc quadInvCounitLowerCell)
      QuadCohesionSaturatedTwoCellConv.triDiscLo) ?_
  show QuadCohesionSaturatedTwoCellConv
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature)
        (composePath (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadDisc))
      (RawTwoCellExpr.whiskerRight quadDisc quadInvCounitLowerCell))
    (RawTwoCellExpr.whiskerRight quadDisc quadInvCounitLowerCell)
  exact quadCohesionConvOfStep
    (TwoCellStep.vcompIdLeft (RawTwoCellExpr.whiskerRight quadDisc quadInvCounitLowerCell))

/-! ## P4 — bridge notes (docstrings only): ZOO-COHESION + MODE-ADMIT -/

/-- **Bridge note (docstrings only) — the ZOO-COHESION and MODE-ADMIT consumption points.**

  * **ZOO-COHESION (Axis `Mode/CohesionModalityMetatheory`, `Mode/Transpension`).**  The Axis cohesion modality
    zoo consumes an idempotence/adjoint-string presentation for the `ʃ ⊣ ♭ ⊣ ♯` modalities.  This quadruple lane
    is the FUNCTOR-level refinement one granularity below the induced `WalkingCohesion` presentation the zoo
    currently references: it exhibits the induced (co)monad idempotence as DERIVED from `Disc`/`coDisc` full
    faithfulness (`quadReflectionsAreIdempotent`), the honest provenance the zoo's `fxMode`-side cohesion markers
    want.  No Axis edit here — this is the note.

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

/-- ★ **ESTABLISHED — the `pi0`-parity obstruction ships: the induced refutation provably does NOT lift.**  The
r1 hand-wave is now a machine-checked theorem: `quadCohesionParity` is BOUNDARY-DETERMINED
(`quadCohesionParity_boundaryDetermined` — parity = source `pi0`-parity XOR target `pi0`-parity), hence CONSTANT
on every parallel pair (`quadCohesionParity_constantOnParallel`) and uniformly `true` on the shape-unit boundary
`id_space ⇒ pi0·disc` (`quadInducedRefutationDoesNotLift`).  So the very `ℤ/2` invariant that SEPARATED a
parallel pair in the induced lane (`CohesionNonThinness`) cannot separate anything here — the induced
non-thinness has no functor-level image.  `= true`. -/
def fxQuadCohesion_hasPi0ObstructionRefutationDoesNotLift : Bool := true

/-- ★ **ESTABLISHED — the ff-driven straddle critical-pair join ships (thin fragment extended).**  Beyond the six
leg straightenings and the two cross-adjunction snake coherences, the populated hom `disc ⇒ disc·pi0·disc` is
shown thin by an explicit join: `disc ◁ η ≈ ε⁻¹ ▷ disc` (`quadStraddleDiscUnitInvCounitJoin`), the reflection
confluence driven by the `Π₀ ⊣ Disc` triangle and the `Disc`-ff iso (`quadDiscWhiskeredLowerRoundCollapses`),
using only the SHIPPED whisker-of-vcomp step.  A concrete straddle-leg witness where local posetality holds by
construction.  `= true`. -/
def fxQuadCohesion_hasStraddleReflectionJoin : Bool := true

/-- ★★ **HONEST WALL — the QUADRUPLE THINNESS is UNRESOLVED (NOT flipped, NOT refuted), now with a SHARPER
boundary.**  The route hand-enumeration finds the low-complexity boundaries THIN (every reflection leg
straightens; the ff-iso round-trips collapse the loops; the straddle leg `disc` joins its unit against its
ff-inverse-counit, `quadStraddleDiscUnitInvCounitJoin`), and the sound `ℤ/2` invariant is now shown
BOUNDARY-DETERMINED (`quadCohesionParity_boundaryDetermined`) — so it CANNOT separate any parallel pair, and the
induced-quotient non-thinness (`WalkingCohesion`, machine-refuted) provably does NOT lift
(`quadInducedRefutationDoesNotLift`): `disc`/`gamma` straddle two adjunctions, the induced generators become
derived composites, and the separating `pi0`-column parity collapses to a boundary function.  So
`QuadCohesionThinness` is left NEITHER inhabited (would need a full general-boundary normalizer over FREE 1-cell
words — the `WalkingIdempotent.normalizeFull`-style closure, but here the 1-cells have no length normal form, so
it is a genuine multi-file arc — NOT attempted this round; and the literature warns the FREE ff-adjoint string is
generically non-posetal, Dawson–Paré–Pronk) NOR refuted (no separator can exist — parity is neutered, the
functor level is thin-LEANING, diverging from the induced quotient).  This is the honest FRAGMENT disposition:
the presentation, the soundness, the thin fragment (now including the straddle join), the pi0-obstruction, and
the decision assembly ship; the GLOBAL thinness claim is NOT forced, and the downstream cohesion computation
stays gated.  `= false`. -/
def fxQuadCohesion_hasQuadrupleThinnessResolution : Bool := false

end FX1Poly.Polygraph
