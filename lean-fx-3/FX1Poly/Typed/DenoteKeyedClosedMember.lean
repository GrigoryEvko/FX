import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Core.RawTermSubstIdentity

/-! # FX1Poly/Typed/DenoteKeyedClosedMember
    — closed-term reducibility from the denote fundamental-theorem conclusion (route-E / SN-D6 precursor toward SN-043)

The bridge from the denote fundamental theorem's conclusion AT THE EMPTY CONTEXT to closed-term reducibility:
once the denote fundamental theorem is established (the SN-D5 wiring, assembling the var / universeFormation /
conv / piElim / piIntro / genFormationPi arms), this corollary turns its closed instance into the closed subject's
denote-reducible membership of its closed classifier — the step the route-E "wire-to-SN" (SN-D6) composes with
denote CR1 to obtain closed-term strong normalization, i.e. SN-043.

The mechanism is the canonical closing of an empty-context judgment: a `FundamentalConclusionAtDenote` at the
empty context quantifies over every closing substitution; instantiate it at the IDENTITY substitution
(`RawTermSubst.identity`) and the empty environment (`ReducibleEnvAtDenote.empty`, vacuous since `Fin 0` is
uninhabited).  The identity-substitution cancellation `RawTerm.subst_identity_apply` (`subst identity t = t`, the
polynomial monad's right-unit law) collapses `subst identity classifier`/`subst identity subject` back to
`classifier`/`subject`, yielding the closed membership directly.

This is `closedTermReducibility`'s denote analogue (the fuel-layer `ReducibleEnvAt`-at-identity reflection,
`HasTypeDescPiStronglyNormalizingFromFundamental`), and the SN-D6 ingredient that — fed the eventual
unconditional denote fundamental theorem (#744, modulo #752 + B1') — closes the closed-term SN headline.

## Zero-axiom verification

Instantiate the conclusion at `RawTermSubst.identity` and `ReducibleEnvAtDenote.empty`, then rewrite by
`RawTerm.subst_identity_apply` twice.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Closed-term reducibility from the empty-context fundamental-theorem conclusion.**  A closed subject
satisfying the denote fundamental-theorem conclusion at the empty context (and classifier) is a denote-reducible
member of its closed classifier — instantiate the conclusion at the identity substitution and the empty
environment, then cancel `subst identity = id`.  Composed with denote CR1, this is the route-E wire-to-SN step
for the closed-term SN headline (SN-043). -/
theorem closedMemberAtDenote {profile : PolyProfile} (env : Nat → Nat) (level : Nat)
    {subject classifier : RawTerm 0}
    (conclusion : FundamentalConclusionAtDenote env level
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    IsReducibleMemberAtDenote env level classifier subject := by
  have member := conclusion RawTermSubst.identity
    (ReducibleEnvAtDenote.empty (profile := profile) RawTermSubst.identity)
  rw [RawTerm.subst_identity_apply, RawTerm.subst_identity_apply] at member
  exact member

end FX1Poly.Typed
