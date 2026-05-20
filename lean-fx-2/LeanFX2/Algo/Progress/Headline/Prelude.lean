import LeanFX2.Algo.WHNF
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step.Inductive
import LeanFX2.Algo.Progress.CanonicalIntroductions
import LeanFX2.Algo.Progress.CanonicalTypeCodes
import LeanFX2.Algo.Progress.CanonicalInterval
import LeanFX2.Algo.Progress.CanonicalHoTTRefl
import LeanFX2.Algo.Progress.BetaIotaStepProvability
import LeanFX2.Algo.Progress.CongRuleLifters

/-! # LeanFX2.Algo.Progress.Headline.Prelude

Shared imports for the semantic progress-headline leaves.  The
relation datatypes and canonical-form helpers stay upstream; each
leaf proves one focused progress family and the public headline
imports only the final assembly module.
-/
