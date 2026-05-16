import LeanFX2.Reduction.ParRed.ParInductive

/-! # LeanFX2.Reduction.ParRed.CongAliases

Exact-name aliases for legacy `Step.par` congruence constructors.

The strict dashboard counts declarations named `Step.par.<ctor>Cong`
for each `Term.<ctor>`.  Several early `Step.par` constructors were
already semantically congruence rules but predated that naming
discipline (`app`, `lam`, `pair`, ...).  These aliases expose the
canonical names without changing the inductive, duplicating proof
logic, or adding any new reduction behavior.
-/

namespace LeanFX2

namespace Step.par

/-- Exact-name alias for non-dependent application congruence. -/
abbrev appCong := @LeanFX2.Step.par.app

/-- Exact-name alias for non-dependent lambda congruence. -/
abbrev lamCong := @LeanFX2.Step.par.lam

/-- Exact-name alias for dependent lambda congruence. -/
abbrev lamPiCong := @LeanFX2.Step.par.lamPi

/-- Exact-name alias for dependent application congruence. -/
abbrev appPiCong := @LeanFX2.Step.par.appPi

/-- Exact-name alias for sigma-pair congruence. -/
abbrev pairCong := @LeanFX2.Step.par.pair

/-- Exact-name alias for first-projection congruence. -/
abbrev fstCong := @LeanFX2.Step.par.fst

/-- Exact-name alias for second-projection congruence. -/
abbrev sndCong := @LeanFX2.Step.par.snd

/-- Exact-name alias for boolean eliminator congruence. -/
abbrev boolElimCong := @LeanFX2.Step.par.boolElim

/-- Exact-name alias for natural successor congruence. -/
abbrev natSuccCong := @LeanFX2.Step.par.natSucc

/-- Exact-name alias for natural eliminator congruence. -/
abbrev natElimCong := @LeanFX2.Step.par.natElim

/-- Exact-name alias for natural recursor congruence. -/
abbrev natRecCong := @LeanFX2.Step.par.natRec

/-- Exact-name alias for list-cons congruence. -/
abbrev listConsCong := @LeanFX2.Step.par.listCons

/-- Exact-name alias for list eliminator congruence. -/
abbrev listElimCong := @LeanFX2.Step.par.listElim

/-- Exact-name alias for option-some congruence. -/
abbrev optionSomeCong := @LeanFX2.Step.par.optionSome

/-- Exact-name alias for option eliminator congruence. -/
abbrev optionMatchCong := @LeanFX2.Step.par.optionMatch

/-- Exact-name alias for either-left congruence. -/
abbrev eitherInlCong := @LeanFX2.Step.par.eitherInl

/-- Exact-name alias for either-right congruence. -/
abbrev eitherInrCong := @LeanFX2.Step.par.eitherInr

/-- Exact-name alias for either eliminator congruence. -/
abbrev eitherMatchCong := @LeanFX2.Step.par.eitherMatch

/-- Exact-name alias for identity eliminator congruence. -/
abbrev idJCong := @LeanFX2.Step.par.idJ

/-- Exact-name alias for modal introduction congruence. -/
abbrev modIntroCong := @LeanFX2.Step.par.modIntro

/-- Exact-name alias for modal elimination congruence. -/
abbrev modElimCong := @LeanFX2.Step.par.modElim

/-- Exact-name alias for modal subsumption congruence. -/
abbrev subsumeCong := @LeanFX2.Step.par.subsume

/-- Exact-name alias for universe cumulativity marker congruence. -/
abbrev cumulUpCong := @LeanFX2.Step.par.cumulUpInnerCong

end Step.par

end LeanFX2
