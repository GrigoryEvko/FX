import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.FoldSoundness

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.FoldSoundness — zero-axiom gate
(the generic denotational soundness of the closed-form fold)

Per-declaration zero-axiom gate for the fold-soundness brick: the fold-as-take/drop/cat
reformulation, its F2 linearity (zero + xor), the four-way xor rearrangement, the
fold/cat identity, the fold kernel form, the generator-block/kill core pair
characterization with its well-formedness and codomain arity, the fold-reflects-span
principle, the kernel-in-spider-span content for both colours, the generic soundness
theorems `zxoFoldSoundnessZ` / `zxoFoldSoundnessX`, the five content-instance fires,
and the honest content marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoSplitAtFst
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoSplitAtSnd
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoCatRowEqCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldRowExpand
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldRowsEqMapRows
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoXor4Swap
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldRowZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldRowXor
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoZeroCatDistrib
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldCatEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldKerForm

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoTailWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoTailCod
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoTailPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldReflectsSpan

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoSpiderZeroBandMemZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldSoundnessZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoSpiderZeroBandMemX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldSoundnessX

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoNatEqBComplete
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoLayersWFBOfWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoDiagramWFBOfWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoZSpiderClosedFormConvOfReflection
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoXSpiderClosedFormConvOfReflection

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldSoundnessZContentFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldSoundnessZBandsFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldSoundnessZMergeFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldSoundnessXContentFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoFoldSoundnessXBandsFire

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoHasFoldSoundness
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxoClosedFormConvReducesToReflection

end FX1PolyAudit
