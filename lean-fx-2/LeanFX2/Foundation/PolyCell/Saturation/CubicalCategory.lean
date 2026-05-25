/-!
# Cubical (ω,p)-Category (Malbos-Massacrier-Struth §2)

An (ω,p)-category is an ω-category where all cells in dimension > p
are R_i-invertible for each direction i. The cubical structure adds
face maps, degeneracies, connections, and per-direction composition.

This is the computational substrate for: cubical Newman's lemma,
cubical Church-Rosser, cubical Squier coherence, and the cube law.

For FX: the kernel polygraph is a (ω,0)-category — all positive-dim
cells have invertibility structure (Conv witnesses are invertible,
cd_lemma fillers are invertible).

Reference: arXiv:2511.16852 §2.1-2.2.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Saturation

universe u

/-- Cell data for a cubical ω-category: cells at each dimension. -/
structure CubicalCells where
  cells : Nat → Type u
  /-- Face maps: extract (n-1)-dim face in direction i with sign ε. -/
  face : {dimension : Nat} → (direction : Fin (dimension + 1)) → (sign : Bool) →
         cells (dimension + 1) → cells dimension
  /-- Degeneracy: promote an n-cell to a degenerate (n+1)-cell in direction i. -/
  degeneracy : {dimension : Nat} → (direction : Fin (dimension + 1)) →
               cells dimension → cells (dimension + 1)
  /-- Composition in direction i: compose two cells sharing an i-face. -/
  compose : {dimension : Nat} → (direction : Fin (dimension + 1)) →
            cells (dimension + 1) → cells (dimension + 1) →
            cells (dimension + 1)

/-- How much of Axis 4 has been constructed for a profile.

This is an honesty ledger, not a mathematical theorem.  A profile at
`finiteIdentifierCells` has only concrete cubical cell data; it does not
claim MMS contraction, Newman, Church-Rosser, or Squier coherence. -/
inductive SaturationConstructionLevel where
  /-- Concrete finite identifier cells only; no cubical relations theorem. -/
  | finiteIdentifierCells : SaturationConstructionLevel
  /-- Face/degeneracy cubical relations have been supplied. -/
  | cubicalRelations : SaturationConstructionLevel
  /-- Full cubical omega-category laws have been supplied. -/
  | cubicalOmegaCategory : SaturationConstructionLevel
  /-- A computable contraction structure has been supplied. -/
  | operationalContraction : SaturationConstructionLevel
  /-- Cubical Newman/Church-Rosser/Squier consequences have been supplied. -/
  | churchRosserSquier : SaturationConstructionLevel
  deriving DecidableEq, Repr

/-- Whether this Axis 4 ledger level includes a concrete contraction witness. -/
def SaturationConstructionLevel.hasOperationalContraction :
    SaturationConstructionLevel → Bool
  | .finiteIdentifierCells => false
  | .cubicalRelations => false
  | .cubicalOmegaCategory => false
  | .operationalContraction => true
  | .churchRosserSquier => true

/-- Whether this Axis 4 ledger level includes the coherent confluence
consequences used later to replace the cascade proofs. -/
def SaturationConstructionLevel.hasCoherentConfluence :
    SaturationConstructionLevel → Bool
  | .finiteIdentifierCells => false
  | .cubicalRelations => false
  | .cubicalOmegaCategory => false
  | .operationalContraction => false
  | .churchRosserSquier => true

/-- Current finite cubical-cell scaffold used while Axis 4 is being built.

Cells in dimension `dimension` are identifiers `0, ..., dimension`.  Faces and
degeneracies choose the distinguished zero identifier; composition keeps the
left input.  This gives concrete computable cubical-cell operations, but it is
not an omega-category law package and must not be read as FX saturation. -/
def finiteIdentifierCubicalCells : CubicalCells where
  cells := fun dimension => Fin (dimension + 1)
  face := fun {dimension} _ _ _ => ⟨0, Nat.zero_lt_succ dimension⟩
  degeneracy := fun {dimension} _ _ => ⟨0, Nat.zero_lt_succ (dimension + 1)⟩
  compose := fun _ cellLeft _ => cellLeft

/-- The current scaffold has no contraction witness. -/
theorem finiteIdentifierCells_hasOperationalContraction :
    SaturationConstructionLevel.finiteIdentifierCells.hasOperationalContraction =
      false := rfl

/-- The current scaffold has no coherent confluence consequence. -/
theorem finiteIdentifierCells_hasCoherentConfluence :
    SaturationConstructionLevel.finiteIdentifierCells.hasCoherentConfluence =
      false := rfl

/-- The cubical identity relations (MMS §2.1.2):
face-face, face-degeneracy, degeneracy-degeneracy commutation laws.
These make the face/degeneracy structure coherent. -/
structure CubicalRelations (cubicalCells : CubicalCells.{u}) where
  /-- Face-face: faces in different directions commute.

  This scaffold uses same-index interchange rather than the full shifted
  cubical identity. It is still an actual equation over the face operations,
  not an empty `True` witness. -/
  faceFace :
    ∀ {dimension : Nat} (dirI : Fin (dimension + 1))
      (dirJ : Fin (dimension + 1))
      (signI signJ : Bool) (cell : cubicalCells.cells (dimension + 2)),
    dirI.val < dirJ.val →
      cubicalCells.face dirI signI
          (cubicalCells.face (Fin.castSucc dirJ) signJ cell) =
        cubicalCells.face dirJ signJ
          (cubicalCells.face (Fin.castSucc dirI) signI cell)
  /-- Face-degeneracy interaction. -/
  faceDegeneracy :
    ∀ {dimension : Nat} (faceDirection : Fin (dimension + 1))
      (degeneracyDirection : Fin (dimension + 1))
      (sign : Bool) (cell : cubicalCells.cells dimension),
    faceDirection.val = degeneracyDirection.val →
      cubicalCells.face faceDirection sign
          (cubicalCells.degeneracy degeneracyDirection cell) =
        cell
  /-- Degeneracy-degeneracy: degeneracies in different directions commute. -/
  degeneracyDegeneracy :
    ∀ {dimension : Nat} (dirI dirJ : Fin (dimension + 1))
      (cell : cubicalCells.cells dimension),
    dirI.val ≤ dirJ.val →
      cubicalCells.degeneracy (Fin.castSucc dirI)
          (cubicalCells.degeneracy dirJ cell) =
        cubicalCells.degeneracy (Fin.succ dirJ)
          (cubicalCells.degeneracy dirI cell)

/-- A cubical ω-category: cells + face/degen/compose + cubical relations. -/
structure CubicalOmegaCat extends CubicalCells.{u} where
  relations : CubicalRelations toCubicalCells
  /-- Composition is associative in each direction. -/
  composeAssoc :
    ∀ {dimension : Nat} (direction : Fin (dimension + 1))
      (cellA cellB cellC : cells (dimension + 1)),
      compose direction (compose direction cellA cellB) cellC =
        compose direction cellA (compose direction cellB cellC)
  /-- Degeneracies are left units for composition. -/
  degeneracyIsLeftUnit :
    ∀ {dimension : Nat} (direction : Fin (dimension + 1))
      (cell : cells (dimension + 1)),
      compose direction
          (degeneracy direction (face direction false cell))
          cell =
        cell
  /-- Degeneracies are right units for composition. -/
  degeneracyIsRightUnit :
    ∀ {dimension : Nat} (direction : Fin (dimension + 1))
      (cell : cells (dimension + 1)),
      compose direction cell
          (degeneracy direction (face direction true cell)) =
        cell

/-- R_i-invertibility: a cell has a pseudo-inverse in direction i.
compose_i(cell, inverse) is degenerate AND compose_i(inverse, cell) is degenerate. -/
structure RiInvertible (cubicalCat : CubicalOmegaCat.{u})
    {dimension : Nat}
    (direction : Fin (dimension + 1))
    (cell : cubicalCat.cells (dimension + 1)) where
  inverse : cubicalCat.cells (dimension + 1)
  /-- Left inverse witness: compose(inverse, cell) ≈ degeneracy. -/
  leftInverseWitness :
    cubicalCat.compose direction inverse cell =
      cubicalCat.degeneracy direction
        (cubicalCat.face direction false cell)
  /-- Right inverse witness: compose(cell, inverse) ≈ degeneracy. -/
  rightInverseWitness :
    cubicalCat.compose direction cell inverse =
      cubicalCat.degeneracy direction
        (cubicalCat.face direction true cell)

/-- A cubical (ω,p)-category: an ω-category where cells above dim p are
R_i-invertible in every direction. The parameter p controls the "directed"
vs "invertible" boundary. -/
structure CubicalOmegaPCategory (truncationLevel : Nat) extends CubicalOmegaCat.{u} where
  /-- Every cell above dim p is invertible in every direction. -/
  invertibilityAboveP :
    ∀ {dimension : Nat} (_hAbove : dimension ≥ truncationLevel)
      (direction : Fin (dimension + 1))
      (cell : toCubicalOmegaCat.cells (dimension + 1)),
    RiInvertible toCubicalOmegaCat direction cell

/-- Boundary data for the one-step reduction relation carried by a cubical
category. -/
structure ReductionBoundary (cubicalCat : CubicalOmegaCat.{u}) where
  sourceOf : cubicalCat.cells 1 → cubicalCat.cells 0
  targetOf : cubicalCat.cells 1 → cubicalCat.cells 0
  isStep : cubicalCat.cells 1 → Bool

/-- One-step reduction relation induced by explicit boundary data. -/
def ReductionBoundary.Rel {cubicalCat : CubicalOmegaCat.{u}}
    (boundary : ReductionBoundary cubicalCat) :
    cubicalCat.cells 0 → cubicalCat.cells 0 → Prop :=
  fun source target =>
    ∃ stepCell : cubicalCat.cells 1,
      boundary.isStep stepCell = true ∧
      boundary.sourceOf stepCell = source ∧
      boundary.targetOf stepCell = target

/-- A Noetherian condition for one concrete reduction boundary: no infinite
descending chains of the relation induced by that boundary.

For FX this should eventually be instantiated from the K12 strong
normalization theorem, through concrete source/target data for dim-1 cells. -/
def ReductionBoundary.IsNoetherian {cubicalCat : CubicalOmegaCat.{u}}
    (boundary : ReductionBoundary cubicalCat) : Prop :=
  WellFounded boundary.Rel

/-- An abstract rewriting system (p-ARS) in a cubical (ω,p)-category:
a designated set of "rewrite generators" at dim p+1 (the one-step reductions). -/
structure AbstractRewritingSystem (cubicalCat : CubicalOmegaCat.{u}) where
  /-- Boundary and step predicate for the actual one-step relation. -/
  boundary : ReductionBoundary cubicalCat
  /-- Noetherian: rewrite chains terminate. -/
  noetherian : boundary.IsNoetherian

/-- The one-step reduction relation of an ARS. -/
def AbstractRewritingSystem.Rel {cubicalCat : CubicalOmegaCat.{u}}
    (ars : AbstractRewritingSystem cubicalCat) :
    cubicalCat.cells 0 → cubicalCat.cells 0 → Prop :=
  ars.boundary.Rel

/-- A local branching: two co-initial rewrite generators from the same source. -/
structure LocalBranching {cubicalCat : CubicalOmegaCat.{u}}
    (ars : AbstractRewritingSystem cubicalCat) where
  source : cubicalCat.cells 0
  rewriteLeft : cubicalCat.cells 1
  rewriteRight : cubicalCat.cells 1
  leftIsStep : ars.boundary.isStep rewriteLeft = true
  rightIsStep : ars.boundary.isStep rewriteRight = true
  leftStartsAtSource : ars.boundary.sourceOf rewriteLeft = source
  rightStartsAtSource : ars.boundary.sourceOf rewriteRight = source

/-- A local confluence filler: a concrete one-step join plus a dim-2 cell
witnessing the square. -/
structure LocalConfluenceFiller {cubicalCat : CubicalOmegaCat.{u}}
    {ars : AbstractRewritingSystem cubicalCat}
    (branching : LocalBranching ars) where
  joinTarget : cubicalCat.cells 0
  leftJoin : cubicalCat.cells 1
  rightJoin : cubicalCat.cells 1
  leftJoinIsStep : ars.boundary.isStep leftJoin = true
  rightJoinIsStep : ars.boundary.isStep rightJoin = true
  leftJoinStartsAtLeftTarget :
    ars.boundary.sourceOf leftJoin = ars.boundary.targetOf branching.rewriteLeft
  rightJoinStartsAtRightTarget :
    ars.boundary.sourceOf rightJoin = ars.boundary.targetOf branching.rewriteRight
  leftJoinEndsAtJoin : ars.boundary.targetOf leftJoin = joinTarget
  rightJoinEndsAtJoin : ars.boundary.targetOf rightJoin = joinTarget
  filler : cubicalCat.cells 2
  fillerLeftBranchFace :
    cubicalCat.face ⟨0, Nat.zero_lt_succ 1⟩ false filler =
      branching.rewriteLeft
  fillerRightBranchFace :
    cubicalCat.face ⟨0, Nat.zero_lt_succ 1⟩ true filler =
      branching.rewriteRight
  fillerLeftJoinFace :
    cubicalCat.face ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ false filler =
      leftJoin
  fillerRightJoinFace :
    cubicalCat.face ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ true filler =
      rightJoin

/-- An ARS is locally confluent when every local branching has a concrete
filler.  The filler function is stored directly because later Church-Rosser
construction must consume the actual square, not merely know that one exists. -/
structure IsLocallyConfluent {cubicalCat : CubicalOmegaCat.{u}}
    (ars : AbstractRewritingSystem cubicalCat) where
  fillerFor : ∀ (branching : LocalBranching ars),
    LocalConfluenceFiller branching

/-- An ARS is convergent: Noetherian + locally confluent. -/
structure IsConvergent {cubicalCat : CubicalOmegaCat.{u}}
    (ars : AbstractRewritingSystem cubicalCat) where
  noetherian : ars.boundary.IsNoetherian
  locallyConfluent : IsLocallyConfluent ars

end LeanFX2.Foundation.PolyCell.Saturation
