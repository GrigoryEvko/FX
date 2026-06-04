import FX1Poly.Typed.DenoteKeyedBoundedFundamentalMotive
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/DenoteKeyedBoundedConvArm
    — the bounded fundamental theorem's CONVERSION member arm + FT arm (#753 toward SN-043)

The bound-carrying analogue of `DenoteKeyedConvMember.lean` + `DenoteKeyedFundamentalConv.lean` (the conversion
typing rule at the reducibility-member level): a bound-reducible member of `typeLeft` transports across
`Conv typeLeft typeRight` to a bound-reducible member of `typeRight`, given `typeRight` is itself bound-reducible.

## The forget-bridge transfer (the key economy)

The whole arm rests on `ReducibleTypeAtBounded.convTransfer`, and that is a ~3-line FORGET-BRIDGE transfer: a
bounded derivation forgets (`ReducibleTypeStepBounded.toReducibleTypeStepDenote`) to a denote derivation at the
SAME `lowerAt` (`denoteBelowFamilyBounded env bound`), and `ReducibleTypeStepDenote.convTransfer` is PARAMETRIC on
`lowerAt` — so the denote conversion-transfer applies verbatim to the forgotten derivations.  This is the
canonical pattern the forget bridge was built for: metatheory that produces FACTS-about-candidates (here, "this
term is in that candidate") transfers without re-porting; only derivation-PRODUCING lemmas (forward closure,
CR1/2/3) needed direct ports.

## The arm

`fundamentalConvAtBounded` is premise-isolating exactly as `fundamentalConvAtDenote`: it carries the target type's
ambient-`bound` reducibility (`reclassifierReducible`) as an explicit premise (the A2-shaped residual the FT
assembly discharges from the `reclassifierTyped` IH + the universe-membership→bound bridge).  The transport itself
is `convMemberUnderClosingSubstitutionBounded`, which pushes the raw `Conv` under the closing substitution by
`Conv.subst` and applies `memberConvAtBounded`.

## Zero-axiom verification

`convTransfer` is the forget-bridge composition; `memberConv` an `obtain` + anonymous constructor; the
substitution form composes with `Conv.subst`; the FT arm is one `convMemberUnderClosingSubstitutionBounded`.  No
induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`
(checked: depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Bounded conversion-transfer (via the forget bridge).**  Convertible bound-reducible types have candidates
that agree on every term: a member of `typeLeft`'s candidate is a member of `typeRight`'s.  Forgets both bounded
derivations to denote derivations (same `lowerAt`) and applies the `lowerAt`-parametric
`ReducibleTypeStepDenote.convTransfer` — no re-porting of the conv metatheory. -/
theorem ReducibleTypeAtBounded.convTransfer {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeAtBounded env bound typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeAtBounded env bound typeRight candidateRight)
    (conv : Conv typeLeft typeRight)
    {term : RawTerm scope} (membership : candidateLeft term) :
    candidateRight term :=
  ReducibleTypeStepDenote.convTransfer
    reducibleLeft.toReducibleTypeStepDenote
    reducibleRight.toReducibleTypeStepDenote
    conv membership

/-- **The bounded conversion member arm (relation-internal).**  A bound-reducible member of `typeLeft`, with
`Conv typeLeft typeRight` and `typeRight` bound-reducible, is a bound-reducible member of `typeRight` — the
member's candidate transports to `typeRight`'s candidate by `ReducibleTypeAtBounded.convTransfer`. -/
theorem memberConvAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {typeLeft typeRight term : RawTerm scope}
    (memberLeft : IsReducibleMemberAtBounded env bound typeLeft term)
    (typeRightReducible : IsReducibleTypeAtBounded env bound typeRight)
    (conv : Conv typeLeft typeRight) :
    IsReducibleMemberAtBounded env bound typeRight term := by
  obtain ⟨candidateLeft, reducibleLeft, memberInLeft⟩ := memberLeft
  obtain ⟨candidateRight, reducibleRight⟩ := typeRightReducible
  exact ⟨candidateRight, reducibleRight,
    ReducibleTypeAtBounded.convTransfer reducibleLeft reducibleRight conv memberInLeft⟩

/-- **The bounded conversion fundamental-theorem arm under a closing substitution.**  From a bound-reducible
member of `subst substitution typeLeft`, the bound-reducibility of `subst substitution typeRight`, and the raw
conversion `Conv typeLeft typeRight`, conclude a bound-reducible member of `subst substitution typeRight`.  The
raw conversion is pushed under the substitution by `Conv.subst` and transported by `memberConvAtBounded`. -/
theorem convMemberUnderClosingSubstitutionBounded {scope targetScope : Nat} (env : Nat → Nat) (bound : Nat)
    {typeLeft typeRight term : RawTerm scope} {substitution : RawTermSubst scope targetScope}
    (memberLeft : IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution typeLeft) (RawTerm.subst substitution term))
    (typeRightReducible : IsReducibleTypeAtBounded env bound (RawTerm.subst substitution typeRight))
    (conv : Conv typeLeft typeRight) :
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution typeRight) (RawTerm.subst substitution term) :=
  memberConvAtBounded env bound memberLeft typeRightReducible (Conv.subst substitution conv)

/-- **The bounded `conv` fundamental-theorem arm (modulo the A2 ambient-bound reducibility premise).**  Given the
subject's fundamental-theorem conclusion (a member of `classifier`), a conversion `Conv classifier reclassifier`,
and the target type's reducibility at the ambient `bound` under every closing substitution (the isolated A2
residual the FT wiring supplies from the `reclassifierTyped` IH + the universe-membership→bound bridge), the
subject satisfies the fundamental-theorem conclusion at the reclassifier.  The transport itself is
`convMemberUnderClosingSubstitutionBounded`. -/
theorem fundamentalConvAtBounded {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope) {subject classifier reclassifier : RawTerm scope}
    (converts : Conv classifier reclassifier)
    (subjectConclusion : FundamentalConclusionAtBounded env bound context subject classifier)
    (reclassifierReducible : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env bound (RawTerm.subst substitution reclassifier)) :
    FundamentalConclusionAtBounded env bound context subject reclassifier := by
  intro _targetScope substitution envReducible
  exact convMemberUnderClosingSubstitutionBounded env bound
    (subjectConclusion substitution envReducible)
    (reclassifierReducible substitution envReducible)
    converts

end FX1Poly.Typed
