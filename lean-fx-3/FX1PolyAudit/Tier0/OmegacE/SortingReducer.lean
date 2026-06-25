import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.OmegacE.SortingReducer

/-! # FX1PolyAudit.Tier0.OmegacE.SortingReducer

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.OmegacE.SortingReducer`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- SORTING REDUCER + DECIDABILITY (SortingReducer.lean): the sorting capstone. The bounded-search reducer mirrors the
-- transposition reducer but the scanner's firing test is the DECIDABLE ORDER GUARD slotValue second < slotValue
-- first (Nat.decLt), not a fixed-pair cell equality. soundness fires sortingSwapRule_fires under context;
-- completeness destructures the guarded existential membership. decidableConvertibleModulo_sortingSystem =
-- decidableConvertibleModulo_ofConvergent (sortingHasLocalConfluence + sortingSystem_isTerminating + reducer) needs
-- NO distinctness (the guard is in membership). Third fully-decided OmegacE system, the symmetric-group word problem.
-- Zero-axiom (nomatch/Bool.noConfusion, dsimp+if_pos, option_isSome_map reused; no list-append simp).
#assert_no_axioms FX1Poly.OmegacE.sortingReduceCells_fires

#assert_no_axioms FX1Poly.OmegacE.sortingReduceCells_isSome_append_right

#assert_no_axioms FX1Poly.OmegacE.sortingReduceCells_isSome_append_left

#assert_no_axioms FX1Poly.OmegacE.sortingReduceCells_sound

#assert_no_axioms FX1Poly.OmegacE.sortingRewrite_implies_reduceCells_isSome

#assert_no_axioms FX1Poly.OmegacE.sortingWordReducer

#assert_no_axioms FX1Poly.OmegacE.decidableConvertibleModulo_sortingSystem

end FX1PolyAudit
