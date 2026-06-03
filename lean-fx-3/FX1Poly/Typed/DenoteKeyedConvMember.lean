import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/DenoteKeyedConvMember
    — the denote fundamental theorem's CONVERSION member arm

The conversion typing rule (`Γ ⊢ t : T`, `T ≡ T'`, `Γ ⊢ T' : type` ⟹ `Γ ⊢ t : T'`) at the denote-reducibility
member level: a denote-reducible member of `typeLeft` transports across `Conv typeLeft typeRight` to a
denote-reducible member of `typeRight`, given `typeRight` is itself denote-reducible (the well-formedness premise
the conversion rule carries).

`memberConvAtDenote` is the relation-internal form: the member's candidate (for `typeLeft`) and `typeRight`'s
candidate agree on the term by `ReducibleTypeAtDenote.convTransfer` (the shipped conversion-transfer: convertible
reducible types have pointwise-iff candidates, via `convInvariant`/`deterministic`).  No `funext`, no new
machinery.  `convMemberUnderClosingSubstitution` is the fundamental-theorem-shaped form: it takes `Conv typeLeft
typeRight` between the RAW context types and applies `Conv.subst` to push the conversion under the closing
substitution before transporting — exactly the shape the FT's conversion case has (the IH gives a member of
`subst σ typeLeft`, the conversion premise is `Conv typeLeft typeRight`, and the goal is a member of
`subst σ typeRight`).

## Zero-axiom verification

`obtain` destructuring of the member and the right-type witness, then a single `convTransfer` application inside
an anonymous-constructor witness; the substitution form composes with `Conv.subst`.  No tactic recursion.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The denote conversion member arm (relation-internal).**  A denote-reducible member of `typeLeft`, with
`Conv typeLeft typeRight` and `typeRight` denote-reducible, is a denote-reducible member of `typeRight` — the
member's candidate transports to `typeRight`'s candidate by `ReducibleTypeAtDenote.convTransfer`. -/
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

/-- **The denote conversion fundamental-theorem arm under a closing substitution.**  From a denote-reducible
member of `subst substitution typeLeft`, the denote-reducibility of `subst substitution typeRight`, and the raw
conversion `Conv typeLeft typeRight`, conclude a denote-reducible member of `subst substitution typeRight`.  The
raw conversion is pushed under the substitution by `Conv.subst` and then transported by `memberConvAtDenote`. -/
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
