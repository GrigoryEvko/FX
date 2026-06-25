import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.Core.GeneratorRedexHeadSoundness

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Core.GeneratorRedexHeadSoundness

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Reduction.Core.GeneratorRedexHeadSoundness`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- GeneratorRedexHeadSoundness (HON-6): the operational-inertness SOUNDNESS of hasRedexHead (HON-2). A
-- generator the redex-head classifier rejects fires NO root redex for ANY cell built on it — universally, in
-- the kernel's own no-root-redex vocabulary: hasRedexHead_false_imp_no_root_redex gives
-- hasRootStepSource = false (the !-half of isStepNormalFormBool), proved DIRECTLY against the detector's
-- eleven-head dite-chain (the bespoke fireRootRedex intermediary retired with IOTA-T11). The instances cover
-- a reserved head (hilbertSpace) and a value head (lam, live via the static axis, not a redex head). This is
-- the operational half of semanticTier soundness (HON-7); reserved ⟹ hasRedexHead = false, so it applies to
-- every reserved generator. Zero-axiom (rw + Bool.noConfusion disequality extraction, dsimp + 11 dif_neg;
-- no Bool.or_eq_false_iff).
#assert_no_axioms FX1Poly.Core.hasRedexHead_false_imp_no_root_redex

#assert_no_axioms FX1Poly.Core.hilbertSpace_no_root_redex

#assert_no_axioms FX1Poly.Core.lam_no_root_redex

end FX1PolyAudit
