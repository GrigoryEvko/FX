import LeanFX2.Reduction.ConvCumulHomo

-- ConvCumulHomo internals
#print axioms LeanFX2.ConvCumulHomo.toCumul
#print axioms LeanFX2.ConvCumulHomo.cast_eq_indep
#print axioms LeanFX2.ConvCumulHomo.cast_eq_both
#print axioms LeanFX2.ConvCumulHomo.fromCumul_refl

-- BHKM headlines on ConvCumulHomo (the internal relation)
#print axioms LeanFX2.ConvCumulHomo.rename_compatible_benton
#print axioms LeanFX2.ConvCumulHomo.subst_compatible_benton

-- BHKM headlines lifted to ConvCumul output (via toCumul)
#print axioms LeanFX2.ConvCumul.rename_compatible_homo_benton
#print axioms LeanFX2.ConvCumul.subst_compatible_homo_benton

-- viaUp case (cross-context cumul promotion at arbitrary scopeLow)
#print axioms LeanFX2.ConvCumul.subst_compatible_viaUp
#print axioms LeanFX2.ConvCumul.rename_compatible_viaUp
