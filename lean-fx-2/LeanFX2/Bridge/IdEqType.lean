import LeanFX2.HoTT.Univalence

/-! # Bridge/IdEqType

Observational type equality as equivalence.

## Deliverable

This module exposes the bridge-facing names for the existing kernel
univalence reductions:

* `idEqTypeRefl` is the reflexive type-equality fragment.
* `idEqTypeHet` is the heterogeneous-carrier fragment for a packaged
  equivalence witness.

Both are conversion theorems between typed terms, not raw type-family
equalities.  The full pseudo-signature from the sprint plan,
`Conv (Ty.id Type A B) (Ty.equiv A B)`, is represented in this kernel by
the corresponding `Term` witnesses because `Conv` relates terms.
-/

namespace LeanFX2
namespace Bridge

/-- Reflexive observational type equality reduces to the canonical identity
equivalence.

This is the bridge-local name for the rfl fragment of univalence:
`Term.equivReflIdAtId` inhabits identity at the universe, and reduces to
`Term.equivReflId` at equivalence type. -/
theorem idEqTypeRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    Conv (Term.equivReflIdAtId (context := context)
        innerLevel innerLevelLt carrier carrierRaw)
      (Term.equivReflId (context := context) carrier) :=
  Univalence innerLevel innerLevelLt carrier carrierRaw

/-- Heterogeneous observational type equality reduces to the packaged
equivalence witness.

This is the bridge-local name for heterogeneous univalence.  It is only as
strong as the supplied `equivWitness`; this theorem does not synthesize an
equivalence from arbitrary raw endpoints. -/
theorem idEqTypeHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness :
      Term context (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Conv (Term.uaIntroHet (context := context)
        innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness)
      equivWitness :=
  UnivalenceHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness

end Bridge
end LeanFX2
