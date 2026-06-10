import FX1Poly.Typed.PiFormerMembership

/-! # FX1Poly/Typed/LiftedChildNormalizationFromClosure
   — the reusable fresh-variable instantiation: cons-closure ⟹ lifted-open child SN (GTL-06 kernel, brick 1)

The GTL-06 dispatch-shape collapse (#820) needs ONE genuinely new lemma family: from telescope
reducibility, strong normalization of EVERY substituted child of a former cell — including
binder-children, whose lifted-OPEN substituted form `subst (lift σ) child` is not directly a
telescope output (the telescope closes over CONSED arguments, not over the fresh variable).

The spike verdict is GO: the binder-child dance is already shipped INSIDE
`sigmaFormerOfChildMemberships` / `piFormerOfChildMemberships` as a four-step idiom —
`tarskiDecode` the domain membership one level up, mine the fresh variable from the candidate
(`containsVariable`), feed the cons-closure at variable 0, finish with
`IsStronglyNormalizing.openBodyOfConsSubstMember` (which needs NO classifier specifics — it
projects the membership's CR1 SN and reflects the cons to a lift).  This module EXTRACTS that
idiom as a standalone lemma, strictly generalized: the domain is any term with a one-level-up
universe membership (not necessarily a substituted code), and the child's classifier is
ARBITRARY (not necessarily a universe code) — `openBodyOfConsSubstMember` never looks at it.

## The remaining #820 assembly (recorded; next bricks)

With this lemma the per-child SN extraction is uniform over the CURRENT formation table:
  * depth-0 children — head membership at any positive level, CR1 (`.stronglyNormalizing`);
  * shift-1 children (the Π/Σ codomain position) — THIS lemma on the telescope's tail closure;
  * shift ≥ 2 children — would need the k-fold generalization (iterated fresh-variable
    instantiation + a k-fold `openBodyOfConsSubst`); NO current `typingRuleDescOf` row has one
    (the table's telescopes are nullary, 1-child `[0]`, or 2-child `[0,1]`), so the k-fold form
    is a named non-blocker, to be built if a ≥3-child former row ever lands.
The kernel lemma (telescope induction collecting per-child SN into cell SN via the N-child
accessibility combinator from the cascade-free generic former SN work) is the next brick; with
it + `formationGenerator_noWeakHeadStep` + `formationOutputData` + `dataFormerInUniverse`, the
six dispatch files collapse to a Π arm + ONE table-generic arm.

## Zero-axiom verification

A verbatim extraction of four shipped steps (`tarskiDecode`, `containsVariable`, the closure
application, `openBodyOfConsSubstMember`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Lifted-open child SN from a cons-closure at the fresh variable.**  If some term (the
"domain") is a reducible universe member one level above, and the binder-child's CONSED
substitution instances are reducible members (of an ARBITRARY classifier) for every reducible
argument of that domain, then the LIFTED-open substituted child is strongly normalizing: mine
the fresh variable from the domain's candidate, feed the closure at variable 0, and reflect
cons to lift.  The reusable form of the idiom shipped inside
`sigmaFormerOfChildMemberships`/`piFormerOfChildMemberships` — the one genuinely new piece the
GTL-06 table-generic dispatch arm needs at shift-1 children. -/
theorem IsStronglyNormalizing.liftedSubstOfConsClosureAtFreshVariable
    {scope targetScope : Nat} {predLevel : Nat}
    {domainLevel : LevelExpr} {flag : UniverseFlag}
    {substitution : RawTermSubst scope (targetScope + 1)}
    {substitutedDomain : RawTerm (targetScope + 1)} {child : RawTerm (scope + 1)}
    {childClassifier : RawTerm (targetScope + 1)}
    (domainMemberAbove : IsReducibleMemberAt (predLevel + 2)
      (universeCodeCell domainLevel flag) substitutedDomain)
    (childClosure : ∀ argument : RawTerm (targetScope + 1),
      IsReducibleMemberAt (predLevel + 1) substitutedDomain argument →
      IsReducibleMemberAt (predLevel + 1) childClassifier
        (RawTerm.subst (RawTermSubst.cons argument substitution) child)) :
    IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) child) := by
  obtain ⟨domainCandidateAbove, domainReducibleAbove⟩ := domainMemberAbove.tarskiDecode
  have freshVariableInDomain :
      domainCandidateAbove (.mkGen .gen_var ⟨0, Nat.succ_pos _⟩ .childNil) :=
    domainReducibleAbove.isReducibilityCandidate.containsVariable ⟨0, Nat.succ_pos _⟩
  exact IsStronglyNormalizing.openBodyOfConsSubstMember
    (childClosure (.mkGen .gen_var ⟨0, Nat.succ_pos _⟩ .childNil)
      ⟨domainCandidateAbove, domainReducibleAbove, freshVariableInDomain⟩)

end FX1Poly.Typed
