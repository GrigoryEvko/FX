import FX1Poly.Typed.ConsistencyTargetSignature

/-! Independent receipt probe: confirm the headline candidate-bridge theorems are zero-axiom
    and have the claimed types.  Scratch-only; not part of the library. -/

open FX1Poly.Typed FX1Poly.Core

-- Headline unconditional consistency: closed typing at emptyType -> False.
#check @emptyConsistencyViaCandidateBridge
#print axioms emptyConsistencyViaCandidateBridge

-- The obstruction-reversal candidate bridge.
#check @emptyTypeCell_candidate_isEmptyCandidate
#print axioms emptyTypeCell_candidate_isEmptyCandidate

-- The sconing-leg member identity + the empty candidate's member-freeness.
#check @emptyTypeCell_closedTypingYieldsEmptyCandidateMember
#print axioms emptyTypeCell_closedTypingYieldsEmptyCandidateMember
#print axioms emptyTaitCandidate.noClosedMember
