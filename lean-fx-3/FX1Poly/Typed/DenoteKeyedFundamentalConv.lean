import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.DenoteKeyedConvMember
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/DenoteKeyedFundamentalConv
    — the denote fundamental theorem's CONVERSION dispatcher arm (SN-D5a; toward SN-043/#672)

The arm for the `HasTypeDescPi.conv` constructor: from the fundamental-theorem conclusion of the subject (a
member of `classifier`) and a conversion `Conv classifier reclassifier`, conclude the fundamental-theorem
conclusion of the subject at the reclassifier.

The real content is the conversion transport: `convMemberUnderClosingSubstitution` (SN-shipped) takes the
subject's membership of `subst σ classifier`, pushes the raw `Conv classifier reclassifier` under the closing
substitution (`Conv.subst`), and transports the member to `subst σ reclassifier` via `convTransfer`.

THE SOLE RESIDUAL is supplying `IsReducibleTypeAtDenote env level (subst σ reclassifier)` — the target type's
reducibility AT THE AMBIENT `level`.  This is genuinely the obstruction the single-level denote motive creates:
the `conv` constructor's `reclassifierTyped` premise yields (via its FT IH) `subst σ reclassifier` as a member
of `universeCodeCell levelExpr flag`, but universe membership decodes reducibility at the DECODED level
`denote levelExpr env`, NOT at the ambient `level`.  Bridging decoded-level reducibility to ambient-level
reducibility for an arbitrary type code is the general denote type-level LEVEL-IRRELEVANCE (the A2 residual,
`DenoteKeyedLevelIrrelevance.ofReducibleTypeStepDenote` modulo its `piArm`).  Reducibility candidates are NOT
backward-closed under arbitrary `Step` (only weak-head, `whnfExpand`), so there is no conv-transport that would
produce the reclassifier's reducibility directly from the subject's classifier reducibility — confirmed by the
shipped `convInvariant` being determinism-only (both sides reducible ⟹ `PointwiseIff`), at both the denote and
fuel layers.

So this arm isolates that residual as the explicit `reclassifierReducible` premise (the established
`ofReducibleTypeStepDenote`/`piArm` discipline): the conv dispatcher is UNCONDITIONAL given the target type's
ambient-level reducibility, and the SN-D5 wiring discharges that premise from the `reclassifierTyped` FT IH plus
the A2 universe-membership→ambient-reducibility bridge (which carries the `denote levelExpr env < level`
side condition).  The piIntro arm's domain candidate hits the SAME A2 bridge; piElim sidesteps it (it threads
candidates already at the ambient level).

## Zero-axiom verification

`intro` the substitution / environment, then one `convMemberUnderClosingSubstitution` fed the subject's instantiated
conclusion, the (premised) target reducibility, and the raw conversion.  No induction, no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The denote `conv` fundamental-theorem arm (modulo the A2 ambient-level reducibility bridge).**  Given the
subject's fundamental-theorem conclusion (a member of `classifier`), a conversion `Conv classifier reclassifier`,
and the target type's reducibility at the ambient `level` under every closing substitution (the isolated A2
residual — the wiring supplies it from the `reclassifierTyped` FT IH plus the universe-membership→ambient bridge),
the subject satisfies the fundamental-theorem conclusion at the reclassifier.  The transport itself is
`convMemberUnderClosingSubstitution`. -/
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
