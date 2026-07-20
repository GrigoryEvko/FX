import FX1Poly.Polygraph.Net.PrimeEventStructure

/-! # FX1PolyAudit/Polygraph/Net/PrimeEventStructureAxiomWitness — independent own-probe (NET-14)

Standalone witness importing the shipped prime-event-structure file FIRST, with
`autoImplicit`/`relaxedAutoImplicit` disabled so nothing is admitted vacuously.  It
re-ascribes the load-bearing headlines VERBATIM against the shipped declarations and adds
FRESH ground fires the shipped build did not pin, then reports `#print axioms` on each so an
independent reader can confirm every headline is axiom-free. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1PolyAudit.PrimeEventStructureWitness

open FX1Poly.Polygraph.Net
open FX1Poly.ComputerAlgebra (cswSort)

/-! ## Verbatim re-ascription of the shipped headlines -/

/-- Keystone re-ascribed verbatim. -/
theorem witnessExtendPreservesConfig (eventStructure : EventStructure) (config : List Nat)
    (newEvent : Nat)
    (hConfig : evsIsConfiguration eventStructure config = true)
    (hEnabled : evsEnabled eventStructure config newEvent = true) :
    evsIsConfiguration eventStructure (newEvent :: config) = true :=
  evsExtendPreservesConfig eventStructure config newEvent hConfig hEnabled

/-- Configuration-equality soundness re-ascribed verbatim. -/
theorem witnessConfigEqSound (left right : List Nat) :
    evsConfigEq left right = true → cswSort left = cswSort right :=
  evsConfigEqSound left right

/-- The Winskel-unfolding wall equation re-ascribed verbatim. -/
theorem witnessUnfoldingWallEqualsDickson :
    evsHasPetriUnfolding = FX1Poly.ComputerAlgebra.fxNet4_dicksonWall :=
  evsUnfoldingWallEqualsDickson

/-! ## Fresh ground fires not pinned by the shipped build -/

/-- The empty set is always a configuration. -/
theorem witnessEmptyIsConfig : evsIsConfiguration evsExample (List.nil) = true := rfl

/-- The singleton `{0}` is a configuration (no predecessor obligation, no conflict). -/
theorem witnessSingletonIsConfig : evsIsConfiguration evsExample (0 :: []) = true := rfl

/-- The conflict lookup is symmetric on the stored pair `1 # 2`. -/
theorem witnessConflictLookup : evsInConflict evsExample 2 1 = true := rfl

/-- The covering decision fires: `{2, 0}` covers `{0}` (witness `2`). -/
theorem witnessCoversFires : evsCovers evsExample (0 :: []) (2 :: 0 :: []) = true := rfl

/-- The full config `{0, 1, 2}` is NOT valid (`0 # 1`). -/
theorem witnessFullSetInvalid : evsIsConfiguration evsExample (0 :: 1 :: 2 :: []) = false := rfl

#print axioms witnessExtendPreservesConfig
#print axioms witnessConfigEqSound
#print axioms witnessUnfoldingWallEqualsDickson
#print axioms witnessEmptyIsConfig
#print axioms witnessSingletonIsConfig
#print axioms witnessConflictLookup
#print axioms witnessCoversFires
#print axioms witnessFullSetInvalid

end FX1PolyAudit.PrimeEventStructureWitness
