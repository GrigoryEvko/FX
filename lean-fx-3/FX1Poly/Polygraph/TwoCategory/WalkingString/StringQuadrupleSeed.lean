import FX1Poly.Polygraph.Computad.Signature
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringKParameterizationCensus

/-! # WalkingString — the `k = 3` ADJOINT-QUADRUPLE SEED (`L1 ⊣ L2 ⊣ L3 ⊣ L4`, FC-4 r2, brick R1)

The census (`StringKParameterizationCensus`, FC-4 r1 O1) NAMED the `2`-baked seed sites and exhibited a `k`-generic
index-word carrier (`adjointStringCupCods`/`adjointStringCapDoms`) that elaborates at `k = 2` AND `k = 3`.  This file
ships the CONCRETE `k = 3` seed — the free 2-computad (`ModeSignature`) of the walking adjoint QUADRUPLE
`L1 ⊣ L2 ⊣ L3 ⊣ L4` — the genuine three-colour sibling of the shipped adjoint-triple seed (`StringSeed`, `k = 2`).

Where the shipped triple has THREE letters `{F, G, H}` (two colours) and FOUR generators, the quadruple has:

  * TWO modes `base` / `tip` (letters alternate `base → tip → base → tip`, so still exactly two modes),
  * FOUR letters `L1 = letterOne : base ⟶ tip`, `L2 = letterTwo : tip ⟶ base`, `L3 = letterThree : base ⟶ tip`,
    `L4 = letterFour : tip ⟶ base` (three adjacencies `L1 ⊣ L2`, `L2 ⊣ L3`, `L3 ⊣ L4`),
  * SIX generating 2-cells — three units (cups) + three counits (caps), one couple `(η_i, ε_i)` per adjacency,
    with NO cross-pair relation (the free construction: per-morphism-local generators, Lobski *Layered Monoidal
    Theories* Def 8.16; Riva–Rovelli *Zigzags and free adjunctions* — `Z²([1]) ≃ Adj`, minimal relation set).

## The mode-partition table (the crux the r2 atom-pin reroute rides)

| mode pair   | cups (dom `nil`)                          | caps (cod `nil`)                        |
| ----------- | ----------------------------------------- | --------------------------------------- |
| `base→base` | **η1** (cod `[1,2]`), **η3** (cod `[3,4]`)| ε2 (dom `[3,2]`)                        |
| `tip→tip`   | η2 (cod `[2,3]`)                          | **ε1** (dom `[2,1]`), **ε3** (dom `[4,3]`)|

Two cups collide at `base→base` (both dom `nil`) — so "DOM determines COD" is REFUTED at `k ≥ 3` (`η1`, `η3` share
dom `nil`, differ in cod).  Two caps collide at `tip→tip` (both cod `nil`) — so "COD determines DOM" is refuted.  This
asymmetry is exactly why BOTH restricted pins ship in `StringQuadrupleAtomPinReroute`: cups have injective COD (not
DOM), caps injective DOM (not COD).

## The HONESTY LAW bridge (this seed IS the `k = 3` instance of the census family)

The six generator boundary words, abstracted to `List Nat` index words by `quadIndexWord` (the quadruple analog of
the census `pathIndexWord`), coincide ON THE NOSE with the `k`-generic carrier at `k = 3`:
`quadCupCods_eq_carrierAtThree : [η1.cod, η2.cod, η3.cod] = adjointStringCupCods 3 = [[1,2],[2,3],[3,4]]` and the cap
dual — the direct analog of the census `shippedCupCods_eq_carrierAtTwo`, but at the FRESH `k = 3` slice (letter `L4`,
index `4`, absent from the `k = 2` alphabet `{1,2,3}`).  A concrete signature value (not a `Nat`-indexed family):
the two restricted pins are `cases`-`cases` over a FINITE constructor set, so a concrete value keeps them free of the
`Fin`-index arithmetic (and its propext traps) an indexed family would demand, and gives `rfl`-computable fixtures for
the engine at `k = 3` (`StringQuadrupleAtomPinReroute`).

ADDITIVE ONLY: no shipped WalkingString file is touched.  Raw Lean 4 + Init; structural recursion / full-enum matches
(`quadLabelIndex` / `quadIndexWord` are four-letter / `nil`-`cons` full enumerations — no wildcard, propext-clean);
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The walking-adjoint-quadruple quiver: two modes, four alternating letters -/

/-- The two modes (0-cells) of the walking adjoint quadruple: `base` (`A`) and `tip` (`B`).  The four letters
alternate `base → tip → base → tip`, so — as at the triple — exactly two modes suffice. -/
inductive AdjointQuadrupleMode where
  /-- The source mode `A`. -/
  | base
  /-- The target mode `B`. -/
  | tip

/-- The four generating modalities (1-cells) of the walking adjoint quadruple: `L1 = letterOne`, `L2 = letterTwo`,
`L3 = letterThree`, `L4 = letterFour`, forming the adjunction string `L1 ⊣ L2 ⊣ L3 ⊣ L4`.  The odd letters
(`L1`, `L3`) go `base ⟶ tip`, the even letters (`L2`, `L4`) go `tip ⟶ base`; `L1` and `L3` are PARALLEL but distinct
generators, as are `L2` and `L4`. -/
inductive AdjointQuadrupleModality : AdjointQuadrupleMode → AdjointQuadrupleMode → Type where
  /-- `L1 : base ⟶ tip`. -/
  | letterOne : AdjointQuadrupleModality AdjointQuadrupleMode.base AdjointQuadrupleMode.tip
  /-- `L2 : tip ⟶ base`. -/
  | letterTwo : AdjointQuadrupleModality AdjointQuadrupleMode.tip AdjointQuadrupleMode.base
  /-- `L3 : base ⟶ tip`. -/
  | letterThree : AdjointQuadrupleModality AdjointQuadrupleMode.base AdjointQuadrupleMode.tip
  /-- `L4 : tip ⟶ base`. -/
  | letterFour : AdjointQuadrupleModality AdjointQuadrupleMode.tip AdjointQuadrupleMode.base

/-- The walking-adjoint-quadruple quiver: two modes, four modality generators. -/
def adjointQuadrupleGraph : ModeGraph where
  Mode := AdjointQuadrupleMode
  Modality := AdjointQuadrupleModality

/-! ## The six endo-words the generating 2-cells live between -/

/-- `L1·L2 : base ⟶ tip ⟶ base` — the cod of the unit `η1` (a `base` endo-path, cup cod). -/
def quadL1L2 : ModalityPath adjointQuadrupleGraph AdjointQuadrupleMode.base AdjointQuadrupleMode.base :=
  ModalityPath.cons AdjointQuadrupleModality.letterOne
    (ModalityPath.cons AdjointQuadrupleModality.letterTwo
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base))

/-- `L2·L1 : tip ⟶ base ⟶ tip` — the dom of the counit `ε1` (a `tip` endo-path, cap dom). -/
def quadL2L1 : ModalityPath adjointQuadrupleGraph AdjointQuadrupleMode.tip AdjointQuadrupleMode.tip :=
  ModalityPath.cons AdjointQuadrupleModality.letterTwo
    (ModalityPath.cons AdjointQuadrupleModality.letterOne
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip))

/-- `L2·L3 : tip ⟶ base ⟶ tip` — the cod of the unit `η2` (a `tip` endo-path, cup cod). -/
def quadL2L3 : ModalityPath adjointQuadrupleGraph AdjointQuadrupleMode.tip AdjointQuadrupleMode.tip :=
  ModalityPath.cons AdjointQuadrupleModality.letterTwo
    (ModalityPath.cons AdjointQuadrupleModality.letterThree
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip))

/-- `L3·L2 : base ⟶ tip ⟶ base` — the dom of the counit `ε2` (a `base` endo-path, cap dom). -/
def quadL3L2 : ModalityPath adjointQuadrupleGraph AdjointQuadrupleMode.base AdjointQuadrupleMode.base :=
  ModalityPath.cons AdjointQuadrupleModality.letterThree
    (ModalityPath.cons AdjointQuadrupleModality.letterTwo
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base))

/-- `L3·L4 : base ⟶ tip ⟶ base` — the cod of the unit `η3` (a `base` endo-path, cup cod; the FRESH letter `L4`). -/
def quadL3L4 : ModalityPath adjointQuadrupleGraph AdjointQuadrupleMode.base AdjointQuadrupleMode.base :=
  ModalityPath.cons AdjointQuadrupleModality.letterThree
    (ModalityPath.cons AdjointQuadrupleModality.letterFour
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base))

/-- `L4·L3 : tip ⟶ base ⟶ tip` — the dom of the counit `ε3` (a `tip` endo-path, cap dom; the FRESH letter `L4`). -/
def quadL4L3 : ModalityPath adjointQuadrupleGraph AdjointQuadrupleMode.tip AdjointQuadrupleMode.tip :=
  ModalityPath.cons AdjointQuadrupleModality.letterFour
    (ModalityPath.cons AdjointQuadrupleModality.letterThree
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip))

/-! ## The six generating 2-cells: three units and three counits -/

/-- The generating 2-cells of the walking adjoint quadruple — three units (`unitOne`/`unitTwo`/`unitThree`, cups,
arity `(0, 2)`) and three counits (`counitOne`/`counitTwo`/`counitThree`, caps, arity `(2, 0)`), one `(η_i, ε_i)`
couple per adjacency `L_i ⊣ L_{i+1}`.  These are the GENERATORS only; the SIX triangle identities (two per adjacency)
are the saturation relations, deferred.  The boundary convention mirrors the shipped triple (`StringTwoCell`): a unit
is `id ⇒ L_i·L_{i+1}`, a counit is `L_{i+1}·L_i ⇒ id`. -/
inductive StringQuadTwoCell :
    {sourceMode targetMode : AdjointQuadrupleMode} →
    ModalityPath adjointQuadrupleGraph sourceMode targetMode →
    ModalityPath adjointQuadrupleGraph sourceMode targetMode → Type where
  /-- The **unit** `η1 : id_base ⇒ L1·L2` (arity `(0, 2)`, cup). -/
  | unitOne :
      StringQuadTwoCell (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) quadL1L2
  /-- The **counit** `ε1 : L2·L1 ⇒ id_tip` (arity `(2, 0)`, cap). -/
  | counitOne :
      StringQuadTwoCell quadL2L1 (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip)
  /-- The **unit** `η2 : id_tip ⇒ L2·L3` (arity `(0, 2)`, cup). -/
  | unitTwo :
      StringQuadTwoCell (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip) quadL2L3
  /-- The **counit** `ε2 : L3·L2 ⇒ id_base` (arity `(2, 0)`, cap). -/
  | counitTwo :
      StringQuadTwoCell quadL3L2 (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base)
  /-- The **unit** `η3 : id_base ⇒ L3·L4` (arity `(0, 2)`, cup; the FRESH letter `L4`). -/
  | unitThree :
      StringQuadTwoCell (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base) quadL3L4
  /-- The **counit** `ε3 : L4·L3 ⇒ id_tip` (arity `(2, 0)`, cap; the FRESH letter `L4`). -/
  | counitThree :
      StringQuadTwoCell quadL4L3 (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip)

/-- ★ The **walking-adjoint-quadruple mode signature** — the free 2-category on `L1 ⊣ L2 ⊣ L3 ⊣ L4`: two modes, four
modality generators, and the six unit / counit 2-cell generators.  The `k = 3` sibling of `adjointTripleModeSignature`
that the (colour-blind) two-level matching tower instantiates at three colours. -/
def adjointQuadrupleModeSignature : ModeSignature where
  graph := adjointQuadrupleGraph
  twoCell := fun firstPath secondPath => StringQuadTwoCell firstPath secondPath

/-! ## The faithful index abstraction: a quadruple word as a `List Nat` index word -/

/-- The index of a quadruple letter: `L1 ↦ 1`, `L2 ↦ 2`, `L3 ↦ 3`, `L4 ↦ 4` — the quadruple analog of the census
`wireLabelIndex`.  Full-enum match (four letters), constant `Nat` motive — propext-clean. -/
def quadLabelIndex {sourceMode targetMode : AdjointQuadrupleMode}
    (letter : AdjointQuadrupleModality sourceMode targetMode) : Nat :=
  match letter with
  | .letterOne => 1
  | .letterTwo => 2
  | .letterThree => 3
  | .letterFour => 4

/-- The **index word** of a quadruple 1-cell: its letter sequence mapped to indices.  The quadruple analog of the
census `pathIndexWord`, defined by direct structural recursion (`nil ↦ []`, `cons ↦ index :: rec` — full-enum, no
wildcard) so `congrArg quadIndexWord` carries no polymorphic-eq propext leak. -/
def quadIndexWord {sourceMode targetMode : AdjointQuadrupleMode}
    (path : ModalityPath adjointQuadrupleGraph sourceMode targetMode) : List Nat :=
  match path with
  | .nil _ => []
  | .cons letter rest => quadLabelIndex letter :: quadIndexWord rest

/-! ## Freeness smokes -/

/-- Smoke: `L1·L2` is the length-2 endo-path at `base`. -/
theorem quadL1L2_length : quadL1L2.length = 2 := rfl

/-- Smoke: `L2·L1` is the length-2 endo-path at `tip`. -/
theorem quadL2L1_length : quadL2L1.length = 2 := rfl

/-- Smoke: `L2·L3` is the length-2 endo-path at `tip`. -/
theorem quadL2L3_length : quadL2L3.length = 2 := rfl

/-- Smoke: `L3·L2` is the length-2 endo-path at `base`. -/
theorem quadL3L2_length : quadL3L2.length = 2 := rfl

/-- Smoke: `L3·L4` is the length-2 endo-path at `base`. -/
theorem quadL3L4_length : quadL3L4.length = 2 := rfl

/-- Smoke: `L4·L3` is the length-2 endo-path at `tip`. -/
theorem quadL4L3_length : quadL4L3.length = 2 := rfl

/-- Smoke: the parallel odd letters `L1` and `L3` (both `base ⟶ tip`) are DISTINCT generators (free-construction
faithfulness) — the `k = 3` analog of the shipped colour separator `string_left_ne_coLeft`. -/
theorem quad_letterOne_ne_letterThree :
    singletonModalityPath (graph := adjointQuadrupleGraph) AdjointQuadrupleModality.letterOne
      ≠ singletonModalityPath (graph := adjointQuadrupleGraph) AdjointQuadrupleModality.letterThree := by
  intro pathsEqual
  have generatorsEqual : AdjointQuadrupleModality.letterOne = AdjointQuadrupleModality.letterThree :=
    singletonModalityPath_injective pathsEqual
  nomatch generatorsEqual

/-- Smoke: the parallel even letters `L2` and `L4` (both `tip ⟶ base`) are DISTINCT generators. -/
theorem quad_letterTwo_ne_letterFour :
    singletonModalityPath (graph := adjointQuadrupleGraph) AdjointQuadrupleModality.letterTwo
      ≠ singletonModalityPath (graph := adjointQuadrupleGraph) AdjointQuadrupleModality.letterFour := by
  intro pathsEqual
  have generatorsEqual : AdjointQuadrupleModality.letterTwo = AdjointQuadrupleModality.letterFour :=
    singletonModalityPath_injective pathsEqual
  nomatch generatorsEqual

/-! ## The census bridge — the seed's boundary words are the `k = 3` instance of the carrier -/

/-- The unit `η1` cod word `L1·L2` has index word `[1, 2]` (ascending).  `rfl`. -/
theorem quadIndexWord_quadL1L2 : quadIndexWord quadL1L2 = [1, 2] := rfl

/-- The counit `ε1` dom word `L2·L1` has index word `[2, 1]` (descending).  `rfl`. -/
theorem quadIndexWord_quadL2L1 : quadIndexWord quadL2L1 = [2, 1] := rfl

/-- The unit `η2` cod word `L2·L3` has index word `[2, 3]` (ascending).  `rfl`. -/
theorem quadIndexWord_quadL2L3 : quadIndexWord quadL2L3 = [2, 3] := rfl

/-- The counit `ε2` dom word `L3·L2` has index word `[3, 2]` (descending).  `rfl`. -/
theorem quadIndexWord_quadL3L2 : quadIndexWord quadL3L2 = [3, 2] := rfl

/-- The unit `η3` cod word `L3·L4` has index word `[3, 4]` (ascending; the FRESH letter `L4`).  `rfl`. -/
theorem quadIndexWord_quadL3L4 : quadIndexWord quadL3L4 = [3, 4] := rfl

/-- The counit `ε3` dom word `L4·L3` has index word `[4, 3]` (descending; the FRESH letter `L4`).  `rfl`. -/
theorem quadIndexWord_quadL4L3 : quadIndexWord quadL4L3 = [4, 3] := rfl

/-- ★★ The seed's three cup COD words `{η1, η2, η3}.cod`, via `quadIndexWord`, coincide ON THE NOSE with the census
`k`-generic carrier at `k = 3` (`adjointStringCupCods 3 = [[1,2],[2,3],[3,4]]`).  This is the HONESTY LAW bridge: the
concrete adjoint-quadruple seed IS the `k = 3` instance of the census family (the FRESH `k = 3` analog of the shipped
`shippedCupCods_eq_carrierAtTwo`), so an `n`-colour claim proven here is a genuine three-colour claim, not the `k = 2`
world relabelled.  `rfl`. -/
theorem quadCupCods_eq_carrierAtThree :
    [quadIndexWord quadL1L2, quadIndexWord quadL2L3, quadIndexWord quadL3L4] = adjointStringCupCods 3 := rfl

/-- ★★ The seed's three cap DOM words `{ε1, ε2, ε3}.dom`, via `quadIndexWord`, coincide on the nose with the census
carrier at `k = 3` (`adjointStringCapDoms 3 = [[2,1],[3,2],[4,3]]`).  The cap side of the `k = 3` faithful embedding.
`rfl`. -/
theorem quadCapDoms_eq_carrierAtThree :
    [quadIndexWord quadL2L1, quadIndexWord quadL3L2, quadIndexWord quadL4L3] = adjointStringCapDoms 3 := rfl

/-! ## Road marker -/

/-- **★ ESTABLISHED — the `k = 3` adjoint-quadruple seed is shipped.**  The free 2-computad
(`adjointQuadrupleModeSignature`) of the walking adjoint quadruple `L1 ⊣ L2 ⊣ L3 ⊣ L4` — two modes, four alternating
letters, six unit / counit generators — the genuine three-colour sibling of the shipped `adjointTripleModeSignature`.
Its six boundary words, abstracted by `quadIndexWord`, coincide on the nose with the census `k`-generic carrier at
`k = 3` (`quadCupCods_eq_carrierAtThree` / `quadCapDoms_eq_carrierAtThree`), so the seed IS the `k = 3` instance of the
family — the HONESTY LAW bridge for the FC-4 r2 determinacy reroute.  `= true`. -/
def fxString_hasAdjointQuadrupleSeed : Bool := true

end FX1Poly.Polygraph
