import LeanFX2.Reduction.CumulPattern23Bridge

/-! # AuditPattern23Bridge — zero-axiom audit for the P2 ⇔ P3 bridge.

`#print axioms` over every shipped declaration in
`Reduction/CumulPattern23Bridge.lean`.  All must report
"does not depend on any axioms" under strict policy.
-/

-- TermSubstHet.fromTermSubst (kernel piece — lives in Term/SubstHet.lean,
-- audited separately but re-listed here for completeness)
#print axioms LeanFX2.TermSubstHet.fromTermSubst

-- Forward bridge: P2 input → P3 output at refl-compat
#print axioms LeanFX2.ConvCumul.bentonInput_to_pairedAllaisAtRefl

-- Backward bridge: P2 input via toCumul
#print axioms LeanFX2.ConvCumul.bentonInput_to_homoBentonViaCumul

-- The diamond — both halves
#print axioms LeanFX2.ConvCumul.pattern23_both_halves
