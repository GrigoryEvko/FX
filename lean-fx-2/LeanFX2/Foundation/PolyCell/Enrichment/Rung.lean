/-!
# Enrichment Ladder — Segal/Rezk Synthetic Predicates (Axis 5)

Per-dimension enrichment levels: each dimension of the PolyCell framework
operates at a specific "categorical level" determined by a Rung:
- hLevel n: n-truncated types (sets for n=2, propositions for n=1)
- segal: Segal types (unique composition = category structure)
- rezk: Rezk types (univalent categories: equivalences = equalities)
- directed: directed-univalent (Gratzer-Weinberger-Buchholtz TT_⊠)
- omegaLimit: limit of all finite levels (full (∞,ω))

For FX: the current scaffold records the intended rung assignment:
dim 0 = hLevel 2, dim 1 = segal, dim 2 = rezk, dim 3 = directed,
dim >= 4 = omegaLimit.  It checks finite monotonicity of that assignment,
but it does not construct Segal composition, Rezk univalence, directed
univalence, or the omega-limit object.

Reference: arXiv:2407.09146, arXiv:1705.07442.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Enrichment

universe u

/-- Enrichment levels — each represents a categorical-strength predicate. -/
inductive Rung where
  | hLevel (truncationLevel : Nat)
  | segal
  | rezk
  | directed
  | omegaLimit
  deriving DecidableEq, Repr

/-- Rungs form a total preorder: higher rungs subsume lower ones. -/
def Rung.strength : Rung → Nat
  | .hLevel truncationLevel => truncationLevel
  | .segal => 100
  | .rezk => 200
  | .directed => 300
  | .omegaLimit => 1000

/-- Rung ordering: stronger rungs have greater or equal strength. -/
def Rung.isAtMost (rungA rungB : Rung) : Bool :=
  rungA.strength ≤ rungB.strength

/-- How much of Axis 5 has actually been constructed. -/
inductive EnrichmentConstructionLevel where
  /-- Only the per-dimension rung assignment has been recorded. -/
  | rungAssignmentOnly
  /-- Finite monotonicity of the rung assignment has been checked. -/
  | finiteRungMonotonicity
  /-- Segal composition structure has been supplied. -/
  | segalComposition
  /-- Rezk univalence has been supplied. -/
  | rezkUnivalence
  /-- Directed univalence has been supplied. -/
  | directedUnivalence
  /-- The omega-limit enrichment object has been supplied. -/
  | omegaLimitStructure
  deriving DecidableEq, Repr

/-- Whether this Axis 5 level includes the finite rung-monotonicity check. -/
def EnrichmentConstructionLevel.hasFiniteRungMonotonicity :
    EnrichmentConstructionLevel → Bool
  | .rungAssignmentOnly => false
  | .finiteRungMonotonicity => true
  | .segalComposition => true
  | .rezkUnivalence => true
  | .directedUnivalence => true
  | .omegaLimitStructure => true

/-- Whether this Axis 5 level includes Segal composition structure. -/
def EnrichmentConstructionLevel.hasSegalComposition :
    EnrichmentConstructionLevel → Bool
  | .rungAssignmentOnly => false
  | .finiteRungMonotonicity => false
  | .segalComposition => true
  | .rezkUnivalence => true
  | .directedUnivalence => true
  | .omegaLimitStructure => true

/-- Whether this Axis 5 level includes Rezk univalence. -/
def EnrichmentConstructionLevel.hasRezkUnivalence :
    EnrichmentConstructionLevel → Bool
  | .rungAssignmentOnly => false
  | .finiteRungMonotonicity => false
  | .segalComposition => false
  | .rezkUnivalence => true
  | .directedUnivalence => true
  | .omegaLimitStructure => true

/-- Whether this Axis 5 level includes directed univalence. -/
def EnrichmentConstructionLevel.hasDirectedUnivalence :
    EnrichmentConstructionLevel → Bool
  | .rungAssignmentOnly => false
  | .finiteRungMonotonicity => false
  | .segalComposition => false
  | .rezkUnivalence => false
  | .directedUnivalence => true
  | .omegaLimitStructure => true

/-- Whether this Axis 5 level includes the omega-limit object. -/
def EnrichmentConstructionLevel.hasOmegaLimitStructure :
    EnrichmentConstructionLevel → Bool
  | .rungAssignmentOnly => false
  | .finiteRungMonotonicity => false
  | .segalComposition => false
  | .rezkUnivalence => false
  | .directedUnivalence => false
  | .omegaLimitStructure => true

/-- An enrichment profile assigns a rung per dimension. -/
def Enrichment := Nat → Rung

/-- The FX enrichment: terms are sets, steps compose uniquely (segal),
cd_lemma fillers are canonical (rezk), higher is directed/omega. -/
def fxEnrichment : Enrichment
  | 0 => .hLevel 2
  | 1 => .segal
  | 2 => .rezk
  | 3 => .directed
  | _ => .omegaLimit

/-- Current FX Axis 5 construction level. -/
def fxEnrichmentConstructionLevel : EnrichmentConstructionLevel :=
  .finiteRungMonotonicity

/-- A Hom type between two elements (abstract — the directed morphism type). -/
structure HomType (carrier : Type u) where
  source : carrier
  target : carrier

/-- The Segal condition (Riehl-Shulman): unique composition.
For a type A with a notion of directed morphism, A is Segal when
every composable pair (f : Hom a b, g : Hom b c) has a unique composite. -/
structure IsSegal (carrier : Type u) where
  Hom : carrier → carrier → Type u
  identity : (object : carrier) → Hom object object
  compose : {objectA objectB objectC : carrier} →
            Hom objectA objectB → Hom objectB objectC → Hom objectA objectC
  isCompositeOf : {objectA objectB objectC : carrier} →
                  Hom objectA objectB → Hom objectB objectC →
                  Hom objectA objectC → Prop
  composeWitness : {objectA objectB objectC : carrier} →
                   (morphismF : Hom objectA objectB) →
                   (morphismG : Hom objectB objectC) →
                   isCompositeOf morphismF morphismG (compose morphismF morphismG)
  composeUnique : {objectA objectB objectC : carrier} →
                  (morphismF : Hom objectA objectB) →
                  (morphismG : Hom objectB objectC) →
                  (candidate : Hom objectA objectC) →
                  isCompositeOf morphismF morphismG candidate →
                  candidate = compose morphismF morphismG
  identityLeftIsUnit : {objectA objectB : carrier} →
                       (morphismF : Hom objectA objectB) →
                       compose (identity objectA) morphismF = morphismF
  identityRightIsUnit : {objectA objectB : carrier} →
                        (morphismF : Hom objectA objectB) →
                        compose morphismF (identity objectB) = morphismF

/-- Explicit two-sided inverse data for the Rezk equivalence-to-equality map. -/
structure InverseData {carrier : Type u} (segalStructure : IsSegal carrier)
    {objectA objectB : carrier}
    (morphismF : segalStructure.Hom objectA objectB) where
  inverse : segalStructure.Hom objectB objectA
  leftInverseIsIdentity :
    segalStructure.compose morphismF inverse = segalStructure.identity objectA
  rightInverseIsIdentity :
    segalStructure.compose inverse morphismF = segalStructure.identity objectB

/-- The Rezk condition: identity types = equivalence types.
A Segal type is Rezk when "being equivalent" (having a morphism with
two-sided inverse) is the same as "being equal" (identity type). -/
structure IsRezk (carrier : Type u) extends IsSegal carrier where
  equivToEq : {objectA objectB : carrier} →
              (morphismF : Hom objectA objectB) →
              (hasInverse : InverseData toIsSegal morphismF) →
              objectA = objectB
  eqToEquiv : {objectA objectB : carrier} →
              objectA = objectB →
              Hom objectA objectB

/-- Finite rung monotonicity: each represented dimension is no stronger than
the next one.  This is only a ledger check; it does not build Segal/Rezk
structure. -/
def Enrichment.hasMonotoneRungsUpTo (enrichment : Enrichment) : Nat → Bool
  | 0 => true
  | dimension + 1 =>
      Enrichment.hasMonotoneRungsUpTo enrichment dimension &&
        Rung.isAtMost (enrichment dimension) (enrichment (dimension + 1))

/-- Current finite check horizon: dim 0 -> 1 -> 2 -> 3 -> 4. -/
def Enrichment.finiteCheckDepth : Nat := 4

/-- Finite monotonicity check over the PolyCell scaffold currently represented
in `fxProfile.shapeMaxDim`.  Later profile fibration work should make this
depth a profile field rather than a local constant. -/
def Enrichment.hasFiniteRungMonotonicity (enrichment : Enrichment) : Bool :=
  enrichment.hasMonotoneRungsUpTo Enrichment.finiteCheckDepth

/-- FX enrichment has finite rung monotonicity over the current scaffold. -/
theorem fxEnrichment_hasFiniteRungMonotonicity :
    fxEnrichment.hasFiniteRungMonotonicity = true := rfl

/-- FX Axis 5 currently has only finite rung-monotonicity evidence. -/
theorem fxEnrichmentConstructionLevel_eq :
    fxEnrichmentConstructionLevel =
      EnrichmentConstructionLevel.finiteRungMonotonicity := rfl

/-- FX Axis 5 currently has no Segal composition structure. -/
theorem fxEnrichment_hasNoSegalComposition :
    fxEnrichmentConstructionLevel.hasSegalComposition = false := rfl

/-- FX Axis 5 currently has no Rezk univalence theorem. -/
theorem fxEnrichment_hasNoRezkUnivalence :
    fxEnrichmentConstructionLevel.hasRezkUnivalence = false := rfl

/-- FX Axis 5 currently has no directed-univalence theorem. -/
theorem fxEnrichment_hasNoDirectedUnivalence :
    fxEnrichmentConstructionLevel.hasDirectedUnivalence = false := rfl

/-- FX Axis 5 currently has no omega-limit enrichment object. -/
theorem fxEnrichment_hasNoOmegaLimitStructure :
    fxEnrichmentConstructionLevel.hasOmegaLimitStructure = false := rfl

/-- Rung at a specific dimension. -/
def Enrichment.atDim (enrichment : Enrichment) (dimension : Nat) : Rung :=
  enrichment dimension

theorem fxEnrichment_dim0 : fxEnrichment.atDim 0 = .hLevel 2 := rfl
theorem fxEnrichment_dim1 : fxEnrichment.atDim 1 = .segal := rfl
theorem fxEnrichment_dim2 : fxEnrichment.atDim 2 = .rezk := rfl
theorem fxEnrichment_dim3 : fxEnrichment.atDim 3 = .directed := rfl

end LeanFX2.Foundation.PolyCell.Enrichment
