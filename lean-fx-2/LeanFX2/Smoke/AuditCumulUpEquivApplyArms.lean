import LeanFX2.Term.RenameInjective.InductiveArms

/-!
# Reviewer log: cumulUp + equivApply rename-injectivity arms are zero-axiom.

Two Tier-A unique-raw arms shipped 2026-05-21 in commits 4e95a608 (cumulUp)
and 598fea15 (equivApply).  These are the cumulativity-wrapper and
univalence-β application ctors — both at distinct RawTerm shapes with no
result-type casts, discharged via the standard suffices+cases+injection
recipe (~85 LoC each).

53 → 55 of 78 arms shipped on strength-T2 (#1953).  Remaining 23 ctors
(appPi/snd/boolElim/idJ/oeqJ/oeqFunext/idStrictRec/pathApp/glueElim/hcomp/
hcompPath/effectPerform/universeCode/equivReflId/funextRefl/
equivReflIdAtId/funextReflAtId/equivIntroHet/equivApp/uaIntroHet/
funextIntroHet/transp/uaToEquiv) involve cast-on-result walls, dependent-
eliminator existentials, 4-way η collisions, or the toNat non-injectivity
wall — deferred to future sessions using the noConfusion HEq-aware
breakthrough (see `feedback_lean_noconfusion_heq_aware`).
-/

#print axioms LeanFX2.Term.rename_injective_arm_cumulUp
#print axioms LeanFX2.Term.rename_injective_arm_equivApply
