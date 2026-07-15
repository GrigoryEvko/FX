import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Generator.GeneratorRedexHead

/-! # FX1PolyAudit.Axis.Term.Generator.GeneratorRedexHead

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Term.Generator.GeneratorRedexHead`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- GeneratorRedexHead (HON-2): the operational-liveness axis of the honesty ledger. Generator.hasRedexHead
-- decides whether a Step fires at the ROOT of a cell headed by g — the 11 eliminator generators (β: gen_app;
-- ι: boolElim/fst/snd/natElim/natRec/listElim/optionMatch/eitherMatch/idJ/idStrictRec), exactly
-- RawTerm.hasRootStepSource's set. Canonical value-formers (lam/boolTrue/pair) are NOT redex heads (live as
-- VALUES via the static axis); the recursive/strict eliminators (natElim/natRec/listElim/idStrictRec) REDUCE
-- but are statically reserved — the operational axis's marginal tier contribution. Zero-axiom (decide over
-- DecidableEq Generator, no wildcard match; every witness rfl). Soundness (false ⟹ no root Step) is HON-6.
#assert_no_axioms FX1Poly.Core.Generator.hasRedexHead

#assert_no_axioms FX1Poly.Core.hasRedexHead_app

#assert_no_axioms FX1Poly.Core.hasRedexHead_boolElim

#assert_no_axioms FX1Poly.Core.hasRedexHead_natElim

#assert_no_axioms FX1Poly.Core.hasRedexHead_natRec

#assert_no_axioms FX1Poly.Core.hasRedexHead_listElim

#assert_no_axioms FX1Poly.Core.hasRedexHead_idStrictRec

#assert_no_axioms FX1Poly.Core.hasRedexHead_lam

#assert_no_axioms FX1Poly.Core.hasRedexHead_boolTrue

#assert_no_axioms FX1Poly.Core.hasRedexHead_pair

#assert_no_axioms FX1Poly.Core.hasRedexHead_piTyCode

#assert_no_axioms FX1Poly.Core.hasRedexHead_hilbertSpace

#assert_no_axioms FX1Poly.Core.hasRedexHead_quantumGate

end FX1PolyAudit
