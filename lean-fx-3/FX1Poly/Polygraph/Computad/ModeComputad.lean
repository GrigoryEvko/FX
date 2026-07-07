import FX1Poly.Polygraph.Computad.AdjunctionSeed

/-! # Polygraph/Computad/ModeComputad — the FINITE first-order presentation of a 2-computad

`Signature.lean`'s `ModeSignature` is the SEMANTIC carrier: `Mode : Type`, `Modality : Mode -> Mode ->
Type`, `twoCell : ... -> Type`.  Its categorical richness (objects x 1-cell-algebra x dimension) is NOT
readable off that carrier — `Mode` has no `Fintype`, `twoCell` inhabitation is undecidable.
`ModeSignatureSpectrum.lean` (A3) worked around this by THREADING the three richness dials as
hand-supplied `ModeSignatureRichness` evidence per signature.

`ModeComputad` closes that gap: a FINITE, first-order presentation (one `Nat`, two `List`s) whose richness
IS a total function of its fields, and which RECONSTRUCTS the semantic carrier (`toModeGraph` /
`toModeSignatureSkeleton`, `Mode := Fin modeCount`).  The concrete `singleObjectSemiringComputad` and
`adjunctionComputad` instantiate it; the reconstruction of the two-mode seed is proven FAITHFUL to the
shipped `adjunctionModeSignature` at the 0/1-skeleton level as a genuine `ModeGraphEquiv` iso in Lean
(`adjunctionComputadGraphEquiv`), and observably faithful at the endpoint / count level.

This is generic presentation machinery with NO dependence on any mode theory, so it lives in the
signature-free `Polygraph/` library (imports only the computad signature + the adjunction seed).  Raw
Lean 4 + Init.  DecidableEq is FREE everywhere (Fin / Nat / List structural; the reconstructed 1-cell
family is a `Fin`-subtype, so `inferInstance` supplies it).  No `Fintype`, no `Classical`.  Propext-free:
`Fin` values are written `Fin.mk` (an `(OfNat)`-literal `(0 : Fin n)` would pull `propext`), and finite
contradictions are drawn by component `congrArg` + `Nat.noConfusion` rather than `decide` on a
`Prod`-of-`Fin` equality (which pulls `propext`).
-/

namespace FX1Poly.Polygraph

/-! ## The finite 2-generator spec: a parallel pair of generator-words -/

/-- A **2-cell generator, presented finitely** — a parallel pair of free 1-cells over the finite 1-cell
generating set.  A free 1-cell is a WORD `List (Fin modalityGenerators.length)` (a sequence of 1-generator
INDICES); the 2-generator boundary is its endpoints `src`, `tgt` and its two parallel words `lhs`, `rhs`.
First-order and fully decidable (only `Fin` / `List` data). -/
structure ComputadTwoGen (modeCount : Nat)
    (modalityGenerators : List (Fin modeCount × Fin modeCount)) where
  /-- The common source mode of both parallel paths. -/
  src : Fin modeCount
  /-- The common target mode of both parallel paths. -/
  tgt : Fin modeCount
  /-- The source 1-cell as a word of 1-generator indices. -/
  lhs : List (Fin modalityGenerators.length)
  /-- The target 1-cell as a word of 1-generator indices. -/
  rhs : List (Fin modalityGenerators.length)

/-! ## The finite computad -/

/-- A **mode computad** — the FINITE first-order presentation of a 2-computad: a mode COUNT (the 0-cells
are `Fin modeCount`), a `List` of 1-cell generators tagged with their `(src, tgt)` endpoints, and a `List`
of finite 2-cell generators (parallel word-pairs).  Everything richness needs is a `List.length` away —
this is the carrier-computed replacement for the threaded `ModeSignatureRichness` evidence. -/
structure ModeComputad where
  /-- `|Mode|` — the object count; the 0-cells are `Fin modeCount`. -/
  modeCount : Nat
  /-- The 1-cell generators, each tagged with its `(source, target)` endpoints. -/
  modalityGenerators : List (Fin modeCount × Fin modeCount)
  /-- The 2-cell generators, each a finite parallel word-pair. -/
  twoCellGenerators : List (ComputadTwoGen modeCount modalityGenerators)

/-- The **dimension profile** `(n0, n1, n2)` — the object / 1-generator / 2-generator counts, read
straight off the carrier (the Steiner richness dials).  The profile IS the richness. -/
def ModeComputad.dimensionProfile (computad : ModeComputad) : Nat × Nat × Nat :=
  (computad.modeCount, computad.modalityGenerators.length, computad.twoCellGenerators.length)

/-- The **richness-evidence data** COMPUTED from the carrier — the exact `(modeCount,
hasGeneratingModality, hasGeneratingTwoCell)` triple that `ModeSignatureSpectrum.lean` had to hand-supply,
now a total function of the `List` fields.  This is the gap-closure witness. -/
def ModeComputad.richnessEvidence (computad : ModeComputad) : Nat × Bool × Bool :=
  (computad.modeCount, !computad.modalityGenerators.isEmpty, !computad.twoCellGenerators.isEmpty)

/-! ## Reconstruction to the shipped semantic carrier (`Signature.lean`) -/

/-- The **reconstructed 1-cell family** — `Modality src tgt` is the set of 1-generators whose recorded
endpoints are exactly `(src, tgt)`: a subtype of `Fin modalityGenerators.length`.  DecidableEq is FREE
(`Fin` DecidableEq on the index, proof-irrelevant subtype). -/
def ModeComputad.Modality (computad : ModeComputad) (src tgt : Fin computad.modeCount) : Type :=
  { index : Fin computad.modalityGenerators.length //
      computad.modalityGenerators.get index = (src, tgt) }

/-- DecidableEq of the reconstructed 1-cells is free (Fin index + proof-irrelevant subtype). -/
instance (computad : ModeComputad) (src tgt : Fin computad.modeCount) :
    DecidableEq (computad.Modality src tgt) :=
  inferInstanceAs (DecidableEq (Subtype _))

/-- `toModeGraph` — the reconstructed 0/1-skeleton as a shipped `ModeGraph`: `Mode := Fin modeCount`,
`Modality := the endpoint-matched generator family`.  Total, zero-axiom. -/
def ModeComputad.toModeGraph (computad : ModeComputad) : ModeGraph where
  Mode := Fin computad.modeCount
  Modality := computad.Modality

/-- `toModeSignatureSkeleton` — the reconstructed 2-polygraph with the 0/1-skeleton faithful and NO
generating 2-cells (`twoCell := Empty`).  This is the session-complete bridge into the shipped
`ModeSignature` carrier; the full `twoCell` reconstruction (interpreting the finite words as
`ModalityPath`s with a composability fold) is the multi-brick `toModeSignature` deferred below. -/
def ModeComputad.toModeSignatureSkeleton (computad : ModeComputad) : ModeSignature where
  graph := computad.toModeGraph
  twoCell := fun _ _ => Empty

/-! ## The TOTAL word-to-`ModalityPath` interpreter and the reconstructed 2-cell family

The stub `twoCell := fun _ _ => Empty` above discards the finite 2-generators.  Below is the genuine total
reconstruction (task 2A-i): a finite generator-word `List (Fin modalityGenerators.length)` is folded
head-first into a typed `ModalityPath` over `toModeGraph`, threading each generator's recorded endpoint
witness through the `cons`.  A word may fail to chain (a generator's recorded source disagrees with the
running mode), so the fold is `Option`-valued and TOTAL — no partiality escapes into the reconstructed
signature.  This produces the 2-cell DATA only; DECIDING 2-cell equality modulo the 3-polygraph relations is
the separate `fxMode_hasDecidableTwoCellEquality` research half (2A-ii) and is NOT touched here. -/

/-- `interpretWordFrom` — the total word-to-`ModalityPath` fold.  From a seed mode `src`, consume a word of
1-generator indices head-first: each index resolves to a generator with recorded endpoints `(a, b)`; it is
legal to prepend only when `a = src` (decided by the FREE `DecidableEq (Fin modeCount)`), after which the
running source becomes `b` and the tail is folded from there.  Returns the DISCOVERED target mode paired with
the built `ModalityPath` (`Sigma`), or `none` when the word does not chain.  Structural on the word; the
endpoint witness transports `get index = (a, b)` to `get index = (src, b)` via `congrArg` (propext-free,
proof-irrelevant subtype). -/
def ModeComputad.interpretWordFrom (computad : ModeComputad)
    (src : Fin computad.modeCount)
    (word : List (Fin computad.modalityGenerators.length)) :
    Option (Sigma (fun targetMode : Fin computad.modeCount =>
      ModalityPath computad.toModeGraph src targetMode)) :=
  match word with
  | [] => some ⟨src, ModalityPath.nil (graph := computad.toModeGraph) src⟩
  | index :: rest =>
      if headEndpointMatchesSrc : (computad.modalityGenerators.get index).1 = src then
        match computad.interpretWordFrom (computad.modalityGenerators.get index).2 rest with
        | none => none
        | some restInterpreted =>
            some ⟨restInterpreted.fst,
              ModalityPath.cons
                (⟨index,
                    congrArg
                      (fun endpointSource =>
                        (endpointSource, (computad.modalityGenerators.get index).2))
                      headEndpointMatchesSrc⟩ :
                  computad.Modality src (computad.modalityGenerators.get index).2)
                restInterpreted.snd⟩
      else
        none

/-- The **reconstructed 2-cell family** — mirroring `Modality` one dimension up.  A generating 2-cell between
the parallel paths `sourcePath`, `targetPath` (both `src -> tgt`) is a 2-generator INDEX whose two words
interpret, from `src`, to EXACTLY `sourcePath` and `targetPath`.  A subtype of `Fin` — TOTAL (every parallel
boundary gets a possibly-empty Type), self-correcting on the stored endpoints (a generator authored for a
different boundary either folds to `none` or lands a different path, failing its conjunct).  This is 2-cell
DATA; no 2-cell-equality decision is made. -/
@[reducible] def ModeComputad.ReconstructedTwoCell (computad : ModeComputad)
    {src tgt : Fin computad.modeCount}
    (sourcePath targetPath : ModalityPath computad.toModeGraph src tgt) : Type :=
  { index : Fin computad.twoCellGenerators.length //
      computad.interpretWordFrom src (computad.twoCellGenerators.get index).lhs
          = some ⟨tgt, sourcePath⟩
        ∧ computad.interpretWordFrom src (computad.twoCellGenerators.get index).rhs
          = some ⟨tgt, targetPath⟩ }

/-- ★ `toModeSignature` — the TOTAL interpreter: the reconstructed 2-polygraph with the real generating
2-cells (`ReconstructedTwoCell`) in place of the skeleton's `twoCell := Empty`.  A genuine total function
`ModeComputad -> ModeSignature`, zero-axiom, superseding `toModeSignatureSkeleton`.  Every downstream
consumer that reads only `.graph` or the carrier-computed richness is unaffected; the `richnessEvidence`
`hasGeneratingTwoCell` bit is now WITNESSED by an actually-inhabited family (see the adjunction unit/counit
reconstruction below) rather than asserted. -/
def ModeComputad.toModeSignature (computad : ModeComputad) : ModeSignature where
  graph := computad.toModeGraph
  twoCell := fun sourcePath targetPath => computad.ReconstructedTwoCell sourcePath targetPath

/-- The total interpreter keeps the skeleton's 0/1-graph on the nose — it only fills in the 2-cells. -/
theorem ModeComputad.toModeSignature_graph (computad : ModeComputad) :
    computad.toModeSignature.graph = computad.toModeSignatureSkeleton.graph := rfl

/-! ## Instance 1 — the single-object semiring computad (modeCount 1) -/

/-- The **single-object semiring computad** — one object, one endo-1-generator (the multiplication
`carrier -> carrier`), no 2-cells.  The finite presentation of `singleObjectSemiringSignature`. -/
def singleObjectSemiringComputad : ModeComputad where
  modeCount := 1
  modalityGenerators := [(⟨0, by decide⟩, ⟨0, by decide⟩)]
  twoCellGenerators := []

/-! ## Instance 2 — the adjunction computad (modeCount 2, unit/counit 2-gens) -/

/-- The adjunction 1-generators `left : 0 -> 1`, `right : 1 -> 0` (generator indices 0 and 1).  Written
with `Fin.mk` (an `OfNat` literal `(0 : Fin 2)` would pull `propext`). -/
def adjunctionComputadModalityGenerators : List (Fin 2 × Fin 2) :=
  [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨0, by decide⟩)]

/-- The **adjunction computad** — the finite presentation of the walking-adjunction seed
`adjunctionModeSignature`: two objects, `left`/`right` 1-generators, and the unit `id_0 => left.right`
(word `[0,1]`) and counit `right.left => id_1` (word `[1,0]`) 2-generators. -/
def adjunctionComputad : ModeComputad where
  modeCount := 2
  modalityGenerators := adjunctionComputadModalityGenerators
  twoCellGenerators :=
    [ { src := ⟨0, by decide⟩, tgt := ⟨0, by decide⟩,
        lhs := [], rhs := [⟨0, by decide⟩, ⟨1, by decide⟩] },
      { src := ⟨1, by decide⟩, tgt := ⟨1, by decide⟩,
        lhs := [⟨1, by decide⟩, ⟨0, by decide⟩], rhs := [] } ]

/-! ## Observable faithfulness to the shipped `adjunctionModeSignature`

Literal `adjunctionComputad.toModeSignatureSkeleton = adjunctionModeSignature` is IMPOSSIBLE (the two
`Modality` families are distinct Types — a `Fin`-subtype vs the bespoke `AdjunctionModality` GADT).  The
observable faithfulness compares the presented 1-generator endpoints and 2-generator count in `Fin`
coordinates via the mode encoding `base |-> 0`, `tip |-> 1`; the genuine Type-level iso follows below. -/

/-- The mode encoding `AdjunctionMode -> Fin 2` anchoring the endpoint comparison (also the `invFun` of the
mode equivalence below). -/
def adjunctionModeToFin : AdjunctionMode → Fin 2
  | .base => ⟨0, by decide⟩
  | .tip => ⟨1, by decide⟩

/-- The bespoke signature's 1-generators enumerated by boundary (`left : base -> tip`, `right : tip ->
base`).  Hand-enumerated ONE-TIME data anchoring the faithfulness claim. -/
def adjunctionSignatureGeneratorEndpoints : List (AdjunctionMode × AdjunctionMode) :=
  [(AdjunctionMode.base, AdjunctionMode.tip), (AdjunctionMode.tip, AdjunctionMode.base)]

/-- **1-generator faithfulness** — the computad's 1-generator endpoints are EXACTLY the bespoke
signature's generator boundaries, transported through `adjunctionModeToFin`.  Compared entirely in `Fin`
coordinates (definitional, so `rfl`; `decide` on a `Prod`-of-`Fin` list would pull `propext`). -/
theorem adjunctionComputad_generators_faithful :
    adjunctionComputad.modalityGenerators
      = adjunctionSignatureGeneratorEndpoints.map
          (fun endpoints => (adjunctionModeToFin endpoints.1, adjunctionModeToFin endpoints.2)) :=
  rfl

/-- **2-generator-count faithfulness** — the computad has exactly the two 2-generators (unit, counit) the
bespoke `AdjunctionTwoCell` presents. -/
theorem adjunctionComputad_twoCellCount_faithful :
    adjunctionComputad.twoCellGenerators.length = 2 := rfl

/-- The single-object computad presents exactly the one endo-1-generator of the semiring signature, no
2-cells. -/
theorem singleObjectSemiringComputad_shape :
    singleObjectSemiringComputad.modalityGenerators.length = 1
      ∧ singleObjectSemiringComputad.twoCellGenerators.length = 0 :=
  ⟨rfl, rfl⟩

/-! ## The Type-level faithfulness iso: a proven `ModeGraphEquiv`

The 0/1-skeleton of the reconstruction is faithful to the shipped `adjunctionModeSignature` ON THE NOSE:
`adjunctionComputad.toModeGraph` is equivalent (a mode-equivalence plus a per-hom modality-equivalence over
it) to `adjunctionGraph`.  This is the genuine Lean witness — not just observable — that the finite computad
generates back INTO the shipped carrier.  The `twoCell`-inclusive signature iso (which needs the
word-to-`ModalityPath` interpreter to even build `toModeSignature`'s reconstructed 2-cell family) is the
documented multi-brick. -/

/-- A bare type equivalence (Init ships none). -/
structure TypeEquiv (Source Target : Type) where
  /-- Forward map. -/
  toFun : Source → Target
  /-- Backward map. -/
  invFun : Target → Source
  /-- `invFun` is a left inverse. -/
  leftInverse : ∀ source, invFun (toFun source) = source
  /-- `invFun` is a right inverse. -/
  rightInverse : ∀ target, toFun (invFun target) = target

/-- A **mode-graph equivalence** — a `Mode`-equivalence with, over it, a per-hom `Modality`-equivalence.
The faithfulness of a reconstruction is exactly the inhabitation of this between `toModeGraph` and the
bespoke graph. -/
structure ModeGraphEquiv (first second : ModeGraph) where
  /-- The 0-cell equivalence. -/
  modeEquiv : TypeEquiv first.Mode second.Mode
  /-- The per-hom 1-cell equivalence, over the mode equivalence. -/
  modalityEquiv : (src tgt : first.Mode) →
    TypeEquiv (first.Modality src tgt) (second.Modality (modeEquiv.toFun src) (modeEquiv.toFun tgt))

/-- The forward mode map `Fin 2 -> AdjunctionMode` (the impossible `≥ 2` index is discharged
propext-free by `Nat.not_lt_zero`). -/
def adjunctionFinToMode : Fin 2 → AdjunctionMode
  | ⟨0, _⟩ => AdjunctionMode.base
  | ⟨1, _⟩ => AdjunctionMode.tip
  | ⟨index + 2, isLt⟩ =>
      False.elim (Nat.not_lt_zero index (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)))

/-- The **0-cell equivalence** `Fin 2 ~= AdjunctionMode`.  Both round-trips are structural; the `Fin 2`
side is cased by `Fin.mk` patterns (an `OfNat`/`Fin.cases` route would pull `propext`). -/
def adjunctionComputadModeEquiv : TypeEquiv (Fin 2) AdjunctionMode where
  toFun := adjunctionFinToMode
  invFun := adjunctionModeToFin
  leftInverse
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨index + 2, isLt⟩ =>
        False.elim (Nat.not_lt_zero index (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)))
  rightInverse := fun mode => by cases mode <;> rfl

/-- Only 1-generator index `0` carries the endpoints `(base, tip)` — drawn propext-free by projecting the
`Prod` and `Fin` components with `congrArg` and closing the mismatched index by `Nat.noConfusion`. -/
theorem adjunctionComputad_onlyIndexZeroIsBaseTip :
    ∀ (index : Fin adjunctionComputadModalityGenerators.length),
      adjunctionComputadModalityGenerators.get index = ((⟨0, by decide⟩ : Fin 2), (⟨1, by decide⟩ : Fin 2)) →
      (⟨0, by decide⟩ : Fin adjunctionComputadModalityGenerators.length) = index
  | ⟨0, _⟩, _ => rfl
  | ⟨1, _⟩, endpointsEqual => Nat.noConfusion (congrArg Fin.val (congrArg Prod.fst endpointsEqual))
  | ⟨index + 2, isLt⟩, _ =>
      False.elim (Nat.not_lt_zero index (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)))

/-- Only 1-generator index `1` carries the endpoints `(tip, base)`. -/
theorem adjunctionComputad_onlyIndexOneIsTipBase :
    ∀ (index : Fin adjunctionComputadModalityGenerators.length),
      adjunctionComputadModalityGenerators.get index = ((⟨1, by decide⟩ : Fin 2), (⟨0, by decide⟩ : Fin 2)) →
      (⟨1, by decide⟩ : Fin adjunctionComputadModalityGenerators.length) = index
  | ⟨0, _⟩, endpointsEqual => Nat.noConfusion (congrArg Fin.val (congrArg Prod.fst endpointsEqual))
  | ⟨1, _⟩, _ => rfl
  | ⟨index + 2, isLt⟩, _ =>
      False.elim (Nat.not_lt_zero index (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)))

/-- No 1-generator has endpoints `(base, base)` — the reconstructed hom at the base-endo boundary is
empty, matching `AdjunctionModality base base`. -/
theorem adjunctionComputad_noGeneratorIsBaseBase :
    ∀ (index : Fin adjunctionComputadModalityGenerators.length),
      adjunctionComputadModalityGenerators.get index = ((⟨0, by decide⟩ : Fin 2), (⟨0, by decide⟩ : Fin 2)) →
      False
  | ⟨0, _⟩, endpointsEqual => Nat.noConfusion (congrArg Fin.val (congrArg Prod.snd endpointsEqual))
  | ⟨1, _⟩, endpointsEqual => Nat.noConfusion (congrArg Fin.val (congrArg Prod.fst endpointsEqual))
  | ⟨index + 2, isLt⟩, _ =>
      Nat.not_lt_zero index (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt))

/-- No 1-generator has endpoints `(tip, tip)`. -/
theorem adjunctionComputad_noGeneratorIsTipTip :
    ∀ (index : Fin adjunctionComputadModalityGenerators.length),
      adjunctionComputadModalityGenerators.get index = ((⟨1, by decide⟩ : Fin 2), (⟨1, by decide⟩ : Fin 2)) →
      False
  | ⟨0, _⟩, endpointsEqual => Nat.noConfusion (congrArg Fin.val (congrArg Prod.fst endpointsEqual))
  | ⟨1, _⟩, endpointsEqual => Nat.noConfusion (congrArg Fin.val (congrArg Prod.snd endpointsEqual))
  | ⟨index + 2, isLt⟩, _ =>
      Nat.not_lt_zero index (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt))

/-- The **per-hom 1-cell equivalence** — for every parallel pair of modes, the reconstructed hom
`adjunctionComputad.Modality src tgt` is equivalent to `AdjunctionModality (finToMode src) (finToMode tgt)`.
The two off-diagonal homs carry exactly one generator (left / right); the two diagonal homs are both
empty. -/
def adjunctionComputadModalityEquiv : (src tgt : Fin 2) →
    TypeEquiv (adjunctionComputad.Modality src tgt)
      (AdjunctionModality (adjunctionFinToMode src) (adjunctionFinToMode tgt))
  | ⟨0, _⟩, ⟨0, _⟩ =>
    { toFun := fun modality => False.elim (adjunctionComputad_noGeneratorIsBaseBase modality.val modality.property)
      invFun := fun modality => nomatch modality
      leftInverse := fun modality => False.elim (adjunctionComputad_noGeneratorIsBaseBase modality.val modality.property)
      rightInverse := fun modality => nomatch modality }
  | ⟨0, _⟩, ⟨1, _⟩ =>
    { toFun := fun _ => AdjunctionModality.left
      invFun := fun _ => ⟨⟨0, by decide⟩, rfl⟩
      leftInverse := fun modality => Subtype.ext (adjunctionComputad_onlyIndexZeroIsBaseTip modality.val modality.property)
      rightInverse := fun modality => by cases modality; rfl }
  | ⟨1, _⟩, ⟨0, _⟩ =>
    { toFun := fun _ => AdjunctionModality.right
      invFun := fun _ => ⟨⟨1, by decide⟩, rfl⟩
      leftInverse := fun modality => Subtype.ext (adjunctionComputad_onlyIndexOneIsTipBase modality.val modality.property)
      rightInverse := fun modality => by cases modality; rfl }
  | ⟨1, _⟩, ⟨1, _⟩ =>
    { toFun := fun modality => False.elim (adjunctionComputad_noGeneratorIsTipTip modality.val modality.property)
      invFun := fun modality => nomatch modality
      leftInverse := fun modality => False.elim (adjunctionComputad_noGeneratorIsTipTip modality.val modality.property)
      rightInverse := fun modality => nomatch modality }
  | ⟨index + 2, isLt⟩, _ =>
      False.elim (Nat.not_lt_zero index (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)))
  | ⟨0, _⟩, ⟨index + 2, isLt⟩ =>
      False.elim (Nat.not_lt_zero index (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)))
  | ⟨1, _⟩, ⟨index + 2, isLt⟩ =>
      False.elim (Nat.not_lt_zero index (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)))

/-- ★ **THE faithfulness theorem** — the reconstructed 0/1-skeleton of `adjunctionComputad` is a genuine
`ModeGraphEquiv` to the shipped `adjunctionGraph` underlying `adjunctionModeSignature`.  A proven iso in
Lean (zero-axiom), superseding a literal `= adjunctionModeSignature` (impossible: distinct carrier
Types). -/
def adjunctionComputadGraphEquiv : ModeGraphEquiv adjunctionComputad.toModeGraph adjunctionGraph where
  modeEquiv := adjunctionComputadModeEquiv
  modalityEquiv := adjunctionComputadModalityEquiv

/-! ## Dimension-2 faithfulness: the interpreter reconstructs the unit / counit 2-cells

The `Fin`-coordinate analogues of `adjunctionLeftThenRight` / `adjunctionRightThenLeft` — exactly the paths
the interpreter builds from the unit's `rhs = [0,1]` and the counit's `lhs = [1,0]`.  Their reconstructed
2-cells are inhabited by the corresponding generator index, both interpreter conjuncts closing by `rfl`
(definitional reduction of the fold + proof-irrelevant `Modality` witnesses).  This is the dimension-2
analogue of the shipped 0/1-skeleton iso `adjunctionComputadGraphEquiv`. -/

/-- The reconstructed unit codomain `id_base ⟹ (left then right)` in `Fin` coordinates — the interpreter's
image of the unit's word `[0, 1]`. -/
def adjunctionComputadReconstructedLeftThenRight :
    ModalityPath adjunctionComputad.toModeGraph (⟨0, by decide⟩ : Fin 2) (⟨0, by decide⟩ : Fin 2) :=
  ModalityPath.cons
    (⟨⟨0, by decide⟩, rfl⟩ : adjunctionComputad.Modality ⟨0, by decide⟩ ⟨1, by decide⟩)
    (ModalityPath.cons
      (⟨⟨1, by decide⟩, rfl⟩ : adjunctionComputad.Modality ⟨1, by decide⟩ ⟨0, by decide⟩)
      (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨0, by decide⟩))

/-- The reconstructed counit domain `(right then left) ⟹ id_tip` in `Fin` coordinates — the interpreter's
image of the counit's word `[1, 0]`. -/
def adjunctionComputadReconstructedRightThenLeft :
    ModalityPath adjunctionComputad.toModeGraph (⟨1, by decide⟩ : Fin 2) (⟨1, by decide⟩ : Fin 2) :=
  ModalityPath.cons
    (⟨⟨1, by decide⟩, rfl⟩ : adjunctionComputad.Modality ⟨1, by decide⟩ ⟨0, by decide⟩)
    (ModalityPath.cons
      (⟨⟨0, by decide⟩, rfl⟩ : adjunctionComputad.Modality ⟨0, by decide⟩ ⟨1, by decide⟩)
      (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩))

/-- ★ **Reconstructed unit** — the 2-generator index `0` inhabits `ReconstructedTwoCell` at the boundary
`(id_base, left-then-right)`: the interpreter sends `lhs = []` to `id_base` and `rhs = [0,1]` to
`adjunctionComputadReconstructedLeftThenRight`, both by `rfl`. -/
def adjunctionComputad_reconstructsUnit :
    adjunctionComputad.ReconstructedTwoCell
      (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) (⟨0, by decide⟩ : Fin 2))
      adjunctionComputadReconstructedLeftThenRight :=
  ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩

/-- ★ **Reconstructed counit** — the 2-generator index `1` inhabits `ReconstructedTwoCell` at the boundary
`(right-then-left, id_tip)`: the interpreter sends `lhs = [1,0]` to
`adjunctionComputadReconstructedRightThenLeft` and `rhs = []` to `id_tip`, both by `rfl`. -/
def adjunctionComputad_reconstructsCounit :
    adjunctionComputad.ReconstructedTwoCell
      adjunctionComputadReconstructedRightThenLeft
      (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) (⟨1, by decide⟩ : Fin 2)) :=
  ⟨⟨1, by decide⟩, ⟨rfl, rfl⟩⟩

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the finite `ModeComputad` carrier ships, reconstructing the semantic carrier and
faithful to `adjunctionModeSignature`.**  The finite presentation (`modeCount` + two `List`s), the
carrier-computed `dimensionProfile` / `richnessEvidence`, the reconstruction `toModeGraph` /
`toModeSignatureSkeleton` (with FREE DecidableEq on the reconstructed 1-cells), the two concrete computads,
observable faithfulness (`adjunctionComputad_generators_faithful`, `adjunctionComputad_twoCellCount_faithful`),
and the genuine 0/1-skeleton iso `adjunctionComputadGraphEquiv : ModeGraphEquiv adjunctionComputad.toModeGraph
adjunctionGraph`.  The `twoCell`-inclusive `toModeSignature` (needing the word-to-`ModalityPath` interpreter)
is the documented multi-brick.  `= true`. -/
def polygraph_hasModeComputad : Bool := true

/-- ★ **Honesty marker — the TOTAL `toModeSignature` interpreter ships (task 2A-i).**  The word-to-`ModalityPath`
fold `interpretWordFrom`, the reconstructed 2-cell family `ReconstructedTwoCell`, the total function
`toModeSignature` (superseding the skeleton's `twoCell := Empty`), and the dimension-2 unit/counit
reconstruction (`adjunctionComputad_reconstructsUnit` / `_reconstructsCounit`).  This produces the 2-cell
DATA only; DECIDING 2-cell equality modulo the 3-polygraph relations stays behind
`fxMode_hasDecidableTwoCellEquality = false` (task 2A-ii, the fib-3-coupled research half).  `= true`. -/
def polygraph_hasTotalModeSignatureInterpreter : Bool := true

end FX1Poly.Polygraph
