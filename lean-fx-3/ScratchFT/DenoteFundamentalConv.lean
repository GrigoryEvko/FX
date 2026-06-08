import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.DenoteKeyedConvMember
import FX1Poly.Typed.HasTypeDescPi

/-! Scratch SN-D5a: the FT conv arm.  SOLE residual = the target type's reducibility at the AMBIENT level
`IsReducibleTypeAtDenote env level (subst σ reclassifier)`: the subject IH gives the subject a member of
`subst σ classifier` at `level`, and `convMemberUnderClosingSubstitution` transports it across `Conv classifier
reclassifier` — but it needs `subst σ reclassifier` reducible AT `level`.  The reclassifier IH delivers
reducibility only at the DECODED level `denote levelExpr env` (universe membership), so bridging to the ambient
level is the general type-level level-irrelevance (A2 residual).  Isolate it as the explicit `reclassifierReducible`
premise (the wiring discharges it via A2); the REST of the conv arm closes unconditionally. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem fundamentalConvAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope) {subject classifier reclassifier : RawTerm scope}
    (converts : Conv classifier reclassifier)
    (subjectConclusion : FundamentalConclusionAtDenote env level context subject classifier)
    (reclassifierReducible : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env level (RawTerm.subst substitution reclassifier)) :
    FundamentalConclusionAtDenote env level context subject reclassifier := by
  intro _targetScope substitution envReducible
  exact convMemberUnderClosingSubstitution env level
    (subjectConclusion substitution envReducible)
    (reclassifierReducible substitution envReducible)
    converts

end FX1Poly.Typed

#print axioms FX1Poly.Typed.fundamentalConvAtDenote
