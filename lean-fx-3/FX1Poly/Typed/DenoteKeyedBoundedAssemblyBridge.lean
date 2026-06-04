import FX1Poly.Typed.DenoteKeyedBoundedGenFormationPiDischarge
import FX1Poly.Typed.DenoteKeyedBoundedConvArm

/-! # FX1Poly/Typed/DenoteKeyedBoundedAssemblyBridge
    — the A2 membership→reducible-type bridge + the wired conv recursor arm (toward the bounded FT assembly, #753 → SN-043)

The bounded grown-engine fundamental theorem will be assembled by `HasTypeDescPi.rec` over the shipped bounded arms
(`fundamentalConvAtBounded` / `fundamentalPiIntroAtBounded` / `fundamentalPiElimAtBounded` /
`fundamentalGenFormationPiAtBounded` + the discharge).  Several of those arms consume an "A2 residual": a classifier
arrives from the recursor as a fundamental MEMBER of a universe `Type@levelExpr`, but the arm needs it as a reducible
TYPE at the ambient bound.  Pre-cumulativity that extraction was the model-obstructed step; with the cumulativity
payoff (`isReducibleBounded_cumulative`) it is now a clean one-liner.  This file ships that bridge and the first
recursor arm it fully wires (conv).

## The A2 bridge

`reducibleTypeAtBoundFromUniverseMemberBounded`: a bound-reducible member of `Type@levelExpr` (decoded level below
the bound) is a bound-reducible TYPE at the bound.  `universeMemberReducibleAsTypeAtDecodedLevelBounded` decodes the
member to a reducible type at its OWN decoded level `denote levelExpr env`; `isReducibleBounded_cumulative` lifts it
from that level (≤ bound, since it is `< bound`) up to the bound.  The under-substitution wrapper
`reducibleTypeAtBoundUnderSubstFromMembershipBounded` applies it to the FundamentalConclusion shape the recursor's
universe-typing IHs produce.

## The wired conv arm

`fundamentalConvArmBounded` is the bounded grown-engine `conv` recursor arm in recursor-ready form: from the subject's
fundamental conclusion at `classifier`, a conversion `Conv classifier reclassifier`, and the reclassifier's
fundamental membership of `Type@levelExpr`, the subject satisfies the fundamental conclusion at `reclassifier`.  It
composes `fundamentalConvAtBounded` (the transport) with the A2 bridge (the reclassifier reducibility), so the eventual
`HasTypeDescPi.rec` conv arm is a single application.

## Scope note (the piIntro residual)

The `piIntro` recursor arm additionally needs member→SN (CR1) at an ARBITRARY target scope for its
`domainArgumentsSN` premise, but `ReducibleTypeAtBounded.isReducibilityCandidate` is stated at `scope + 1` (the
arrow-CR1 var-0 inhabitant), so a general bounded member-SN is not available directly.  That CR1-at-arbitrary-scope
extraction (via the forget bridge to the denote CR1, or a per-shape argument) is the next residual; the conv arm here
needs no CR1 and so wires cleanly now.

## Zero-axiom verification

The bridge is `isReducibleBounded_cumulative ∘ universeMemberReducibleAsTypeAtDecodedLevelBounded` with `Nat.le_of_lt`;
the wrapper distributes `subst` by `subst_universeCodeCell`; the conv arm composes the shipped `fundamentalConvAtBounded`
with the wrapper.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The A2 bridge: bound-reducible universe membership ⟹ bound-reducible type (via free cumulativity).**  A
bound-reducible member `typeCode` of `Type@levelExpr` (decoded level `denote levelExpr env < bound`) is a
bound-reducible TYPE at the bound.  `universeMemberReducibleAsTypeAtDecodedLevelBounded` decodes the member to a
reducible type at the decoded level; `isReducibleBounded_cumulative` lifts that to the bound (the decoded level is
`< bound`, hence `≤ bound`).  The residual extractor the conv / piIntro / genFormationPi recursor arms all consume. -/
theorem reducibleTypeAtBoundFromUniverseMemberBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (universeCodeCell levelExpr flag) typeCode)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    IsReducibleTypeAtBounded env bound typeCode :=
  isReducibleBounded_cumulative
    (universeMemberReducibleAsTypeAtDecodedLevelBounded member belowBound)
    (Nat.le_of_lt belowBound)

/-- **The A2 bridge under a closing substitution.**  A classifier whose fundamental conclusion is a member of
`Type@levelExpr` (decoded level below the bound) is a bound-reducible type under every closing substitution: apply the
conclusion, fix the closed universe code by `subst_universeCodeCell`, then the A2 bridge.  This is exactly the
`reclassifierReducible`/`domainReducibleAtBound`-shaped premise the shipped FT arms consume. -/
theorem reducibleTypeAtBoundUnderSubstFromMembershipBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {classifier : RawTerm scope} (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound)
    (classifierConclusion : FundamentalConclusionAtBounded env bound context classifier
      (universeCodeCell levelExpr flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env bound (RawTerm.subst substitution classifier) := by
  intro _targetScope substitution envReducible
  have member := classifierConclusion substitution envReducible
  rw [subst_universeCodeCell] at member
  exact reducibleTypeAtBoundFromUniverseMemberBounded env bound member belowBound

/-- **The bounded grown-engine `conv` recursor arm (recursor-ready).**  From the subject's fundamental conclusion at
`classifier`, a conversion `Conv classifier reclassifier`, and the reclassifier's fundamental membership of its
universe `Type@levelExpr` (decoded level below the bound), the subject satisfies the fundamental conclusion at
`reclassifier`.  Composes `fundamentalConvAtBounded` (the conv transport) with the A2 bridge
(`reducibleTypeAtBoundUnderSubstFromMembershipBounded`, supplying the reclassifier reducibility) — so the eventual
`HasTypeDescPi.rec` conv arm is a single application of this lemma to the recursor's two sub-conclusions. -/
theorem fundamentalConvArmBounded {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope) {subject classifier reclassifier : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound)
    (converts : Conv classifier reclassifier)
    (subjectConclusion : FundamentalConclusionAtBounded env bound context subject classifier)
    (reclassifierConclusion : FundamentalConclusionAtBounded env bound context reclassifier
      (universeCodeCell levelExpr flag)) :
    FundamentalConclusionAtBounded env bound context subject reclassifier :=
  fundamentalConvAtBounded env bound context converts subjectConclusion
    (reducibleTypeAtBoundUnderSubstFromMembershipBounded env bound context levelExpr flag belowBound
      reclassifierConclusion)

/-- **Bounded CR1 in member form, at the non-empty closing scope `scope + 1`.**  A bound-reducible member of any type
is strongly normalizing — `obtain` the candidate, then `ReducibleTypeAtBounded.isReducibilityCandidate.strongly\
Normalizing` (CR1).  The `scope + 1` index is structural, not incidental: the bounded reducibility-candidate bundle is
stated at `scope + 1` because its arrow-CR1 arm instantiates the codomain at the var-0 inhabitant `gen_var ⟨0, _⟩`,
which only exists at a non-empty scope.  This is exactly the scope the fundamental theorem closes into — the denote
vector assembly likewise closes every binder-local premise into `targetScope + 1` and reads CR1 there.  The bounded
member relation keys reducibility on the ambient `bound`; the denote layer keys it on a positive fuel level, but both
share the same structural need for a fresh variable in the arrow CR1, hence the `+ 1`.  This is the
`domainArgumentsSN` discharge for the piIntro recursor arm ONCE that arm closes into `scope + 1` (the motive-level
decision deferred to the assembly). -/
theorem stronglyNormalizing_of_memberAtBoundedSucc {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode term : RawTerm (scope + 1)}
    (member : IsReducibleMemberAtBounded env bound typeCode term) :
    IsStronglyNormalizing term := by
  obtain ⟨_candidate, candidateReducible, termInCandidate⟩ := member
  exact candidateReducible.isReducibilityCandidate.stronglyNormalizing termInCandidate

/-- **The +1-closing bounded fundamental-theorem conclusion.**  Identical to `FundamentalConclusionAtBounded` except
the closing substitution lands in a NON-EMPTY scope `targetScope + 1`.  This is the motive the grown-FT assembly must
use so the binder (piIntro) arm can read member→SN via the scope+1 bounded CR1 (`stronglyNormalizing_of_memberAt\
BoundedSucc`) — the denote vector assembly likewise closes every binder-local premise into `targetScope + 1`. -/
def FundamentalConclusionAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
    ReducibleEnvAtBounded env bound context substitution →
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject)

/-- **Down-cast: an arbitrary-scope conclusion gives the +1-closing conclusion.**  `FundamentalConclusionAtBounded`
quantifies over EVERY closing scope, so it specializes to the `targetScope + 1` scopes the +1-motive uses — one
instantiation.  This lifts the shipped arbitrary-scope arms (var / universeFormation / conv / piElim / genFormationPi
— none of which introduce a binder) into the +1-closing motive for free; only the piIntro arm needs the genuinely-new
+1 treatment below. -/
theorem FundamentalConclusionAtBounded.toSucc {profile : PolyProfile} {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (conclusion : FundamentalConclusionAtBounded env bound context subject classifier) :
    FundamentalConclusionAtBoundedSucc env bound context subject classifier :=
  fun substitution envReducible => conclusion substitution envReducible

/-- **The +1-closing piIntro (λ) fundamental-theorem arm — domainArgumentsSN AUTO-DISCHARGED.**  Because the +1-motive
closes into `targetScope + 1`, the domain arguments live at `targetScope + 1`, where the bounded CR1 applies — so the
`domainArgumentsSN` premise that `fundamentalPiIntroAtBounded` carried is now discharged INTERNALLY via
`stronglyNormalizing_of_memberAtBoundedSucc`, and disappears from the signature.  Routes through
`abstractionMemberUnderClosingSubstitutionBounded` (the shipped binder-crux lemma) at the +1 scope with the canonical
member-predicate candidates; the body IH threads through `ReducibleEnvAtBounded.cons`.  This is the last grown-FT arm
that needed binder-specific work; all others lift via `FundamentalConclusionAtBounded.toSucc`. -/
theorem fundamentalPiIntroAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainReducibleAtBound : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env bound (RawTerm.subst substitution domainCode))
    (codomainReducibleAtBound : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ argument : RawTerm (targetScope + 1),
          IsReducibleMemberAtBounded env bound (RawTerm.subst substitution domainCode) argument →
          IsReducibleTypeAtBounded env bound
            (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (bodyConclusion :
        FundamentalConclusionAtBoundedSucc env bound (context.cons domainCode) body codomainCode) :
    FundamentalConclusionAtBoundedSucc env bound context (lamCell body)
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution envReducible
  exact abstractionMemberUnderClosingSubstitutionBounded
    (domainCandidate := IsReducibleMemberAtBounded env bound (RawTerm.subst substitution domainCode))
    (codomainCandidate := fun argument =>
      IsReducibleMemberAtBounded env bound
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    env bound
    (domainReducibleAtBound substitution envReducible).reducibleMemberCandidate
    (fun argument argumentMember =>
      (codomainReducibleAtBound substitution envReducible argument argumentMember).reducibleMemberCandidate)
    (fun _argument argumentMember => stronglyNormalizing_of_memberAtBoundedSucc argumentMember)
    (fun argument argumentMember =>
      bodyConclusion (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtBounded.cons envReducible argumentMember))

end FX1Poly.Typed
