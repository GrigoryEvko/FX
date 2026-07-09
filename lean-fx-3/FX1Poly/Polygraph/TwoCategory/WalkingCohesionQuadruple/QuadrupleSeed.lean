import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model

/-! # WalkingCohesionQuadruple/QuadrupleSeed — the walking COHESION QUADRUPLE `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc`

The FUNCTOR-level presentation of the walking cohesion mode theory as a 2-computad (`ModeSignature`).  Where the
walking-cohesion seed (`WalkingCohesion/CohesionSeed`) presents the INDUCED modalities `ʃ ⊣ ♭ ⊣ ♯` as three
endo-1-cell generators on ONE mode, this seed is the FINER, functor-level presentation the modalities are
COMPOSED from: the adjoint QUADRUPLE of the global-sections geometric morphism `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` with

  * TWO modes `space` (the cohesive site `C`) and `pointSet` (the base `S`),
  * FOUR modality generators — `pi0 = Π₀ : space ⟶ pointSet` (pieces / connected components), `disc = Disc :
    pointSet ⟶ space` (the discrete embedding, fully faithful), `gamma = Γ : space ⟶ pointSet` (points / global
    sections), and `codisc = coDisc : pointSet ⟶ space` (the codiscrete embedding, fully faithful).  `disc` and
    `gamma` are each SHARED between two adjacent adjunctions (`disc` right below, left in the middle; `gamma` right
    in the middle, left above),
  * SIX generating adjunction 2-cells — one unit and one counit per adjunction — and THREE FULLY-FAITHFUL inverse
    2-cells: `Disc` ff makes the lower counit and the middle unit isos, `coDisc` ff makes the upper counit an iso.

## The induced modalities are COMPOSITES here, not generators

By nLab (*cohesive topos*): the quadruple induces, by composition, the adjoint string of MODALITIES
`ʃ = Disc∘Π₀`, `♭ = Disc∘Γ`, `♯ = coDisc∘Γ`.  At the functor level these are the length-2 endo-paths
`pi0·disc`, `gamma·disc`, `gamma·codisc` (diagrammatic / `cons` order, source-to-target).  So the walking-cohesion
seed is the QUOTIENT-flavoured presentation whose primitive modality generators are these composites; this
quadruple seed is one granularity finer — the primitive functors themselves, with the induced (co)monads DERIVED.

## The adjoint-quadruple boundary convention

Mirrors `WalkingString/StringSeed` (`FreeAdjunctionData`): for an adjunction `left ⊣ right` a unit is
`id ⇒ left·right`, a counit is `right·left ⇒ id` (diagrammatic `cons` order).  So

  * `Π₀ ⊣ Disc` (`left = pi0`, `right = disc`): unit `id_space ⇒ pi0·disc`, counit `disc·pi0 ⇒ id_pointSet`,
  * `Disc ⊣ Γ`  (`left = disc`, `right = gamma`): unit `id_pointSet ⇒ disc·gamma`, counit `gamma·disc ⇒ id_space`,
  * `Γ ⊣ coDisc` (`left = gamma`, `right = codisc`): unit `id_space ⇒ gamma·codisc`, counit
    `codisc·gamma ⇒ id_pointSet`.

`disc` is right adjoint below (`Π₀ ⊣ Disc`) and left adjoint in the middle (`Disc ⊣ Γ`); `gamma` is right adjoint
in the middle and left adjoint above (`Γ ⊣ coDisc`) — exactly the two shared central legs of the quadruple.

Licata–Shulman (*Adjoint Logic with a 2-Category of Modes*, LFCS 2016): the cohesion interface is `Π₀, Γ : C → S`
and `Δ, ∇ : S → C` with `Π₀ ⊣ Δ ⊣ Γ ⊣ ∇` and `Δ, ∇ FULLY FAITHFUL`; the ff conditions are the three inverse
generators here (a right adjoint is ff iff its counit is iso; a left adjoint is ff iff its unit is iso).

Generic presentation data (no mode-theory dependence).  Zero external dependencies beyond the free-2-cell model.
Raw Lean 4 + Init. -/

namespace FX1Poly.Polygraph

/-! ## The walking-quadruple quiver: two modes, four functor generators -/

/-- The two modes (0-cells) of the walking cohesion quadruple: the cohesive site `space` (`C`) and the base
`pointSet` (`S`). -/
inductive QuadCohesionMode where
  /-- The cohesive site `C`. -/
  | space
  /-- The base topos `S` of sets / points. -/
  | pointSet

/-- The four generating functors (1-cells) of the walking cohesion quadruple: the pieces functor `pi0 = Π₀`, the
discrete embedding `disc = Disc` (fully faithful), the global-sections functor `gamma = Γ`, and the codiscrete
embedding `codisc = coDisc` (fully faithful).  `pi0` and `gamma` are PARALLEL (`space ⟶ pointSet`) but distinct;
`disc` and `codisc` are PARALLEL (`pointSet ⟶ space`) but distinct. -/
inductive QuadCohesionModality : QuadCohesionMode → QuadCohesionMode → Type where
  /-- The pieces functor `Π₀ : space ⟶ pointSet`. -/
  | pi0 : QuadCohesionModality QuadCohesionMode.space QuadCohesionMode.pointSet
  /-- The discrete embedding `Disc : pointSet ⟶ space` (fully faithful). -/
  | disc : QuadCohesionModality QuadCohesionMode.pointSet QuadCohesionMode.space
  /-- The global-sections functor `Γ : space ⟶ pointSet`. -/
  | gamma : QuadCohesionModality QuadCohesionMode.space QuadCohesionMode.pointSet
  /-- The codiscrete embedding `coDisc : pointSet ⟶ space` (fully faithful). -/
  | codisc : QuadCohesionModality QuadCohesionMode.pointSet QuadCohesionMode.space

/-- The walking-quadruple quiver: two modes, four functor generators. -/
def quadCohesionGraph : ModeGraph where
  Mode := QuadCohesionMode
  Modality := QuadCohesionModality

/-! ## The generating 1-cells as length-1 paths -/

/-- The pieces functor `Π₀` as the length-1 path. -/
def quadPi0 : ModalityPath quadCohesionGraph QuadCohesionMode.space QuadCohesionMode.pointSet :=
  singletonModalityPath QuadCohesionModality.pi0

/-- The discrete embedding `Disc` as the length-1 path. -/
def quadDisc : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet QuadCohesionMode.space :=
  singletonModalityPath QuadCohesionModality.disc

/-- The global-sections functor `Γ` as the length-1 path. -/
def quadGamma : ModalityPath quadCohesionGraph QuadCohesionMode.space QuadCohesionMode.pointSet :=
  singletonModalityPath QuadCohesionModality.gamma

/-- The codiscrete embedding `coDisc` as the length-1 path. -/
def quadCodisc : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet QuadCohesionMode.space :=
  singletonModalityPath QuadCohesionModality.codisc

/-! ## The six length-2 endo-paths the adjunction 2-cells live between -/

/-- The composite `pi0·disc = Disc∘Π₀ = ʃ` (space endo) — the codomain of the lower unit. -/
def quadPi0Disc : ModalityPath quadCohesionGraph QuadCohesionMode.space QuadCohesionMode.space :=
  composePath quadPi0 quadDisc

/-- The composite `disc·pi0 = Π₀∘Disc` (pointSet endo) — the domain of the lower counit. -/
def quadDiscPi0 : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet QuadCohesionMode.pointSet :=
  composePath quadDisc quadPi0

/-- The composite `disc·gamma = Γ∘Disc` (pointSet endo) — the codomain of the middle unit. -/
def quadDiscGamma : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet QuadCohesionMode.pointSet :=
  composePath quadDisc quadGamma

/-- The composite `gamma·disc = Disc∘Γ = ♭` (space endo) — the domain of the middle counit. -/
def quadGammaDisc : ModalityPath quadCohesionGraph QuadCohesionMode.space QuadCohesionMode.space :=
  composePath quadGamma quadDisc

/-- The composite `gamma·codisc = coDisc∘Γ = ♯` (space endo) — the codomain of the upper unit. -/
def quadGammaCodisc : ModalityPath quadCohesionGraph QuadCohesionMode.space QuadCohesionMode.space :=
  composePath quadGamma quadCodisc

/-- The composite `codisc·gamma = Γ∘coDisc` (pointSet endo) — the domain of the upper counit. -/
def quadCodiscGamma : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet QuadCohesionMode.pointSet :=
  composePath quadCodisc quadGamma

/-! ## The nine generating 2-cells: three adjunctions (six units/counits) + three ff inverses -/

/-- The generating 2-cells of the walking cohesion quadruple — the six adjunction units / counits (one per side of
each of `Π₀ ⊣ Disc`, `Disc ⊣ Γ`, `Γ ⊣ coDisc`) plus the three FULLY-FAITHFUL inverse cells (`Disc` ff makes the
lower counit and the middle unit isos; `coDisc` ff makes the upper counit an iso).  These are the GENERATORS only;
the SIX triangle identities and the SIX ff-iso round-trip laws are the saturation relations
(`QuadrupleSaturatedConv`). -/
inductive QuadCohesionTwoCell :
    {sourceMode targetMode : QuadCohesionMode} →
    ModalityPath quadCohesionGraph sourceMode targetMode →
    ModalityPath quadCohesionGraph sourceMode targetMode → Type where
  /-- The **lower unit** `η : id_space ⇒ pi0·disc` of `Π₀ ⊣ Disc` (arity `(0, 2)`, the lower CUP). -/
  | unitLower : QuadCohesionTwoCell (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) quadPi0Disc
  /-- The **lower counit** `ε : disc·pi0 ⇒ id_pointSet` of `Π₀ ⊣ Disc` (arity `(2, 0)`, the lower CAP). -/
  | counitLower :
      QuadCohesionTwoCell quadDiscPi0 (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
  /-- The **middle unit** `η' : id_pointSet ⇒ disc·gamma` of `Disc ⊣ Γ` (arity `(0, 2)`). -/
  | unitMiddle :
      QuadCohesionTwoCell (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadDiscGamma
  /-- The **middle counit** `ε' : gamma·disc ⇒ id_space` of `Disc ⊣ Γ` (arity `(2, 0)`). -/
  | counitMiddle :
      QuadCohesionTwoCell quadGammaDisc (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space)
  /-- The **upper unit** `η'' : id_space ⇒ gamma·codisc` of `Γ ⊣ coDisc` (arity `(0, 2)`). -/
  | unitUpper :
      QuadCohesionTwoCell (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) quadGammaCodisc
  /-- The **upper counit** `ε'' : codisc·gamma ⇒ id_pointSet` of `Γ ⊣ coDisc` (arity `(2, 0)`). -/
  | counitUpper :
      QuadCohesionTwoCell quadCodiscGamma (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
  /-- The **lower-counit inverse** `id_pointSet ⇒ disc·pi0` — witnesses `Disc` FULLY FAITHFUL (right adjoint of
  `Π₀ ⊣ Disc` ⟹ counit iso). -/
  | invCounitLower :
      QuadCohesionTwoCell (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadDiscPi0
  /-- The **middle-unit inverse** `disc·gamma ⇒ id_pointSet` — witnesses `Disc` FULLY FAITHFUL (left adjoint of
  `Disc ⊣ Γ` ⟹ unit iso). -/
  | invUnitMiddle :
      QuadCohesionTwoCell quadDiscGamma (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
  /-- The **upper-counit inverse** `id_pointSet ⇒ codisc·gamma` — witnesses `coDisc` FULLY FAITHFUL (right adjoint
  of `Γ ⊣ coDisc` ⟹ counit iso). -/
  | invCounitUpper :
      QuadCohesionTwoCell (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadCodiscGamma

/-- ★ The **walking-cohesion-quadruple mode signature** — the free 2-category on `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` with
`Disc`, `coDisc` fully faithful: two modes `space`/`pointSet`, four functor generators, and the nine unit / counit
/ ff-inverse 2-cell generators.  This is the seed the saturated convertibility and the thinness analysis are
instantiated at. -/
def quadCohesionModeSignature : ModeSignature where
  graph := quadCohesionGraph
  twoCell := fun firstPath secondPath => QuadCohesionTwoCell firstPath secondPath

/-! ## Freeness smokes -/

/-- Smoke: `pi0·disc` (`ʃ`) is the length-2 endo-path at `space`. -/
theorem quadPi0Disc_length : quadPi0Disc.length = 2 := rfl

/-- Smoke: `gamma·disc` (`♭`) is the length-2 endo-path at `space`. -/
theorem quadGammaDisc_length : quadGammaDisc.length = 2 := rfl

/-- Smoke: `gamma·codisc` (`♯`) is the length-2 endo-path at `space`. -/
theorem quadGammaCodisc_length : quadGammaCodisc.length = 2 := rfl

/-- Smoke: `codisc·gamma` is the length-2 endo-path at `pointSet`. -/
theorem quadCodiscGamma_length : quadCodiscGamma.length = 2 := rfl

/-- Smoke: `pi0` and `gamma` are PARALLEL (`space ⟶ pointSet`) but DISTINCT functor generators — the free
construction separates them, so the quadruple is not a degenerate collapse of pieces onto sections. -/
theorem quadPi0_ne_gamma : quadPi0 ≠ quadGamma := by
  intro pathsEqual
  have generatorsEqual : QuadCohesionModality.pi0 = QuadCohesionModality.gamma :=
    singletonModalityPath_injective pathsEqual
  nomatch generatorsEqual

/-- Smoke: `disc` and `codisc` are PARALLEL (`pointSet ⟶ space`) but DISTINCT — the discrete and codiscrete
embeddings are separated by the free construction. -/
theorem quadDisc_ne_codisc : quadDisc ≠ quadCodisc := by
  intro pathsEqual
  have generatorsEqual : QuadCohesionModality.disc = QuadCohesionModality.codisc :=
    singletonModalityPath_injective pathsEqual
  nomatch generatorsEqual

/-- Smoke: the induced monad `ʃ = pi0·disc` and the induced comonad `♭ = gamma·disc` are DISTINCT length-2
1-cells — their heads `pi0` and `gamma` differ (`quadPi0_ne_gamma`), so the shape and flat modalities do not
collapse and the cross-modality comparison the induced lane studies is a genuine (non-degenerate) boundary here
too. -/
theorem quadPi0Disc_ne_gammaDisc : quadPi0Disc ≠ quadGammaDisc := by
  intro pathsEqual
  apply quadPi0_ne_gamma
  have headEqual :
      QuadCohesionModality.pi0 = QuadCohesionModality.gamma := by
    injection pathsEqual
  exact congrArg singletonModalityPath headEqual

end FX1Poly.Polygraph
