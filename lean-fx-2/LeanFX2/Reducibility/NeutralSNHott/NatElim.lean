import LeanFX2.Reducibility.NeutralSNHott.ElimVarShape
import LeanFX2.Reducibility.SN.Helpers

/-! # LeanFX2.Reducibility.NeutralSNHott.NatElim

The two theorems formerly shipped from this file
(`RawTerm.natElim_isStronglyNormalizing` and
`Term.natElim_isStronglyNormalizing`) carried a universally-
quantified `succAppIsSN : ∀ {predecessor}, SN predecessor → SN
(app succBranch predecessor)` Pi-type hypothesis describing the raw
ι contractum's SN status.  At the raw layer this hypothesis is not
provable in general (untyped applications need not be SN); it was a
hypothesis-as-postulate, banned by `CLAUDE.md` "Forbidden reasoning
patterns".  Both theorems have been DELETED.

The honest path to non-vacuous natElim SN is the M04 fundamental
strong-normalization theorem, which builds reducibility by
induction on the typing derivation and backward-closes Ty.nat's
predicate under ι reduction so the contractum-SN obligation is a
real consequence (not a hypothesis).  Until M04 lands these
helpers cannot ship without resorting to the banned pattern.

This file is kept so existing imports continue to resolve; only the
import line of `ElimVarShape` (the live `natSucc` SN atom) remains. -/

namespace LeanFX2

end LeanFX2
