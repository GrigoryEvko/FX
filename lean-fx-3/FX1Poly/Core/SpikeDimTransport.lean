import FX1Poly.Core.CellSort

/-! # SPIKE-1: value-level dim transport in certified generatingCell

A minimal spike confirming that moving dim from a type INDEX to a
COMPUTED value keeps the boundary transport propext-free.  The
`#print axioms` commands at the end record the verdict; the spike is
retained as the empirical evidence cited by `HasEqualDim.lean`. -/

namespace FX1Poly.Core.SpikeDimTransport

inductive SpikeRawCell : Nat → Type where
  | termBase : {scope : Nat} → Nat → SpikeRawCell scope
  | generatingCell : {scope : Nat} →
      Nat → SpikeRawCell scope → SpikeRawCell scope → SpikeRawCell scope

@[reducible] def SpikeRawCell.dim {scope : Nat} : SpikeRawCell scope → Nat
  | .termBase _ => 0
  | .generatingCell _ source _ => source.dim + 1

def SpikeBoundary (scope : Nat) : Nat → Type
  | 0 => Unit
  | _ + 1 => SpikeRawCell scope × SpikeRawCell scope

/-- Certified cell. The generatingCell ctor takes dimEqual as a
hypothesis and stores BOTH endpoint certs at `canonicalDim` (an
explicit Nat parameter), with propositional equations tying it to
the computed dims. This avoids the `▸`-on-computed-function motive
failure. -/
inductive SpikeCertCell (scope : Nat) :
    (cellDim : Nat) → SpikeBoundary scope cellDim →
    SpikeRawCell scope → Type where
  | atom : {payload : Nat} →
      SpikeCertCell scope 0 () (.termBase payload)
  | generatingCell :
      {source target : SpikeRawCell scope} →
      (canonicalDim : Nat) →
      (sourceDimEq : source.dim = canonicalDim) →
      (targetDimEq : target.dim = canonicalDim) →
      {sourceBoundary : SpikeBoundary scope canonicalDim} →
      {targetBoundary : SpikeBoundary scope canonicalDim} →
      SpikeCertCell scope canonicalDim sourceBoundary source →
      SpikeCertCell scope canonicalDim targetBoundary target →
      SpikeCertCell scope (canonicalDim + 1) (source, target)
        (.generatingCell 0 source target)

/-- Concrete: two dim-0 atoms. -/
def buildConcrete (scope : Nat) (srcPay tgtPay : Nat) :
    SpikeCertCell scope 1
      (SpikeRawCell.termBase srcPay, SpikeRawCell.termBase tgtPay)
      (.generatingCell 0 (.termBase srcPay) (.termBase tgtPay)) :=
  .generatingCell 0 rfl rfl .atom .atom

/-- General: arbitrary cells with decided dim equality.
Uses Eq.rec to transport certs from source.dim/target.dim to canonicalDim.
The `#print axioms` verdict below confirms this Eq.rec is propext-free. -/
def buildGeneral (scope : Nat)
    (source target : SpikeRawCell scope)
    (sourceBoundary : SpikeBoundary scope source.dim)
    (certSource : SpikeCertCell scope source.dim sourceBoundary source)
    (targetBoundary : SpikeBoundary scope target.dim)
    (certTarget : SpikeCertCell scope target.dim targetBoundary target)
    : Option (SpikeCertCell scope (source.dim + 1) (source, target)
        (.generatingCell 0 source target)) :=
  if dimEqual : source.dim = target.dim then
    -- We need certTarget : SpikeCertCell scope target.dim targetBoundary target
    -- repackaged as     : SpikeCertCell scope source.dim ?boundary target
    -- Use a helper that takes the dim equality and does one cast on the
    -- DEPENDENT PAIR (boundary, cert) simultaneously.
    let packed : (boundary : SpikeBoundary scope source.dim) ×
        SpikeCertCell scope source.dim boundary target :=
      dimEqual ▸ ⟨targetBoundary, certTarget⟩
    some (.generatingCell source.dim rfl dimEqual.symm certSource packed.2)
  else
    none

/-- Smoke: concrete produces the expected cert. -/
theorem buildConcrete_eq :
    buildConcrete 4 0 1 = .generatingCell 0 rfl rfl .atom .atom := rfl

end FX1Poly.Core.SpikeDimTransport

-- ═══════════════════════════════════════════════════════════════════
-- THE VERDICT
-- ═══════════════════════════════════════════════════════════════════
#print axioms FX1Poly.Core.SpikeDimTransport.SpikeRawCell
#print axioms FX1Poly.Core.SpikeDimTransport.SpikeRawCell.dim
#print axioms FX1Poly.Core.SpikeDimTransport.SpikeBoundary
#print axioms FX1Poly.Core.SpikeDimTransport.SpikeCertCell
#print axioms FX1Poly.Core.SpikeDimTransport.buildConcrete
#print axioms FX1Poly.Core.SpikeDimTransport.buildGeneral
#print axioms FX1Poly.Core.SpikeDimTransport.buildConcrete_eq
