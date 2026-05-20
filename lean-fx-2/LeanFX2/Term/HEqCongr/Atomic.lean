import LeanFX2.Term.HEqCongr.Atomic.Base
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro

/-! # Term/HEqCongr/Atomic

Public shim for atomic HEq congruence leaves.  The semantic leaves keep
independent constructor families separately cacheable while preserving the
existing import surface for downstream proof cascades. -/
