import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Core.ConvSubstRename

/-! Scratch: the denote conv member arm. (1) relation-internal: a denote-reducible member of `typeLeft`, with
`Conv typeLeft typeRight` and `typeRight` denote-reducible, is a denote-reducible member of `typeRight` (via the
shipped convTransfer). (2) FT-shaped under a closing substitution via Conv.subst. -/

namespace FX1Poly.Typed
open FX1Poly.Core

theorem memberConvAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    {typeLeft typeRight term : RawTerm scope}
    (memberLeft : IsReducibleMemberAtDenote env level typeLeft term)
    (typeRightReducible : IsReducibleTypeAtDenote env level typeRight)
    (conv : Conv typeLeft typeRight) :
    IsReducibleMemberAtDenote env level typeRight term := by
  obtain ⟨candidateLeft, reducibleLeft, memberInLeft⟩ := memberLeft
  obtain ⟨candidateRight, reducibleRight⟩ := typeRightReducible
  exact ⟨candidateRight, reducibleRight,
    ReducibleTypeAtDenote.convTransfer reducibleLeft reducibleRight conv memberInLeft⟩

theorem convMemberUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    {typeLeft typeRight term : RawTerm scope} {substitution : RawTermSubst scope targetScope}
    (memberLeft : IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution typeLeft) (RawTerm.subst substitution term))
    (typeRightReducible : IsReducibleTypeAtDenote env level (RawTerm.subst substitution typeRight))
    (conv : Conv typeLeft typeRight) :
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution typeRight) (RawTerm.subst substitution term) :=
  memberConvAtDenote env level memberLeft typeRightReducible (Conv.subst substitution conv)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.memberConvAtDenote
#print axioms FX1Poly.Typed.convMemberUnderClosingSubstitution
