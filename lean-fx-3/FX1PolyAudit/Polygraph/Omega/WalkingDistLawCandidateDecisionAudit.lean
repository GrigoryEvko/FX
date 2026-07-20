import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingDistLawCandidateDecision

/-! # FX1PolyAudit.Polygraph.Omega.WalkingDistLawCandidateDecisionAudit — zero-axiom gate for the
walking distributive law's candidate-enumeration decision machine + bounded no-go (WP-DISTLAW).

Per-declaration `#assert_no_axioms` on the carrier (layer words, monad presentation, candidate
table, fuelled evaluator), the reused word-equality bridge, the four Beck-axiom Bool checks, the
validity decision and its soundness, the positive / invalid candidates, the exhaustive bounded
enumeration, the two walls, all ground fires, and the state marker.  Exact parity with the
shipped file. -/

namespace FX1PolyAudit

-- T1: the carrier
#assert_no_axioms FX1Poly.Polygraph.Omega.DlwLetter
#assert_no_axioms FX1Poly.Polygraph.Omega.DlwWord
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwLetterS
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwLetterT
#assert_no_axioms FX1Poly.Polygraph.Omega.DlwMonadPres
#assert_no_axioms FX1Poly.Polygraph.Omega.DlwCandidate
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwAppend
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwLookup
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwCrossingCovered
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwCandidateWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwPrepend
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwStep
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwEval

-- the reused word-equality bridge
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwEncodeLetter
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwEncodeWord
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwWordBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwWordBeqToEncodeEq

-- T2: the four Beck-axiom checks and the conjunction
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwBeckFuel
#assert_no_axioms FX1Poly.Polygraph.Omega.beckUnitS
#assert_no_axioms FX1Poly.Polygraph.Omega.beckUnitT
#assert_no_axioms FX1Poly.Polygraph.Omega.beckMultS
#assert_no_axioms FX1Poly.Polygraph.Omega.beckMultT
#assert_no_axioms FX1Poly.Polygraph.Omega.isValidDistLaw

-- T3: the decision, soundness, leg reflections, presentations, candidates
#assert_no_axioms FX1Poly.Polygraph.Omega.decideDistLawValid
#assert_no_axioms FX1Poly.Polygraph.Omega.isValidDistLaw_sound
#assert_no_axioms FX1Poly.Polygraph.Omega.beckMultS_legEq
#assert_no_axioms FX1Poly.Polygraph.Omega.beckMultT_legEq
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFreeMonadS
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFreeMonadT
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwSingleCrossings
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwSwapCandidate
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwIdentityCandidate
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwDoublingCandidate

-- the exhaustive bounded enumeration
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwConsEach
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwAppendWords
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwWordsUpTo
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwToCandidates
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwAllInvalid
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwNoValidDistLawExists

-- T4: the walls
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwHasGeneralDistLawExistence
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwHasHigherCoherence

-- T5: the ground fires
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireSwapWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireSwapValid
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireSwapMultSLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireIdentityUnitS
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireIdentityUnitT
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireIdentityMultS
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireIdentityInvalid
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireDoublingInvalid
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireWordsUpToOne
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireNoValidAtBoundOne
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireValidAppearsAtBoundTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.dlwFireSwapMultTLegEq

-- the state marker
#assert_no_axioms FX1Poly.Polygraph.Omega.fxDistLaw_candidateDecisionStateRecorded

end FX1PolyAudit
