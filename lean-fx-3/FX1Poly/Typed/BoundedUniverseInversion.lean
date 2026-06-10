import FX1Poly.Typed.DenoteKeyedBoundedReducibility

/-! # FX1Poly/Typed/BoundedUniverseInversion
    — the universe gate inversion (toward open strong normalization)

`belowBound_of_reducibleUniverse`: if a universe code `Type@levelExpr` is bound-reducible-as-type at `bound`
(with some candidate), then its decoded level is strictly below the bound — `denote levelExpr env < bound`.
This recovers the `belowBound` gate that the bound-carrying model
(`DenoteKeyedBoundedReducibility.lean`) hides inside its `universeCode` arm.

## Why the inversion holds (the four impossible arms + the gate arm)

`ReducibleTypeAtBounded env bound (Type@levelExpr) candidate` can only be derived five ways, and a universe
code forces four of them shut:

  * **whnfExpand** — needs `WeakHeadStep (Type@levelExpr) reduct`, but a universe code is weak-head-normal
    (no head redex), so there is no such step.
  * **neutral** — carries `rootGenerator ≠ gen_universeCode`, contradicted since the root IS `gen_universeCode`.
  * **piType** — its conclusion index is a `gen_piTyCode` cell; `gen_universeCode ≠ gen_piTyCode` refutes the
    index unification.
  * **universeCode** — the ONLY surviving arm; it carries exactly `belowBound : denote levelExpr env < bound`,
    recovered after a payload `injection` pins `levelExpr' = levelExpr`.
  * **ofPointwiseIff** — wraps an inner derivation of the SAME index; the induction recurses.

## Why the bounded fundamental theorem needs it

The decode lemma `universeMemberReducibleAsTypeAtDecodedLevelBounded` (the universe-member → reducible-type
bridge) takes `belowBound` as a premise.  A context binding type's reducibility comes from the grown FT
applied to its `IsTypeDescPi` (= `HasTypeDescPi … (universeCodeCell …)`) derivation, which yields a universe
MEMBER whose candidate is a `ReducibleTypeAtBounded` of the universe code — and THIS inversion extracts the
`belowBound` the decode then consumes (and cumulativity reuses to lift the decoded-level reducibility to the
uniform bound).

## Zero-axiom verification

Index-inversion via `generalize` of the universe-code cell + `induction` on `ReducibleTypeStepBounded`, threading
the cell equality `hTypeCode`; the surviving `universeCode` arm closes by `injection` (payload) + `rw`.  Checked
to depend on NO axioms — `propext`-clean (no wildcard match, full-arm induction with constant motive).  No
`sorry`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The universe gate inversion.**  A bound-reducible-as-type universe code `Type@levelExpr` has its
decoded level strictly below the bound: `denote levelExpr env < bound`.  The four non-universe arms are
impossible for a universe code (weak-head-normal, not neutral, not a Π cell); the `universeCode` arm carries the
gate directly; `ofPointwiseIff` recurses.  Recovers the `belowBound` premise the universe-member decode
(`universeMemberReducibleAsTypeAtDecodedLevelBounded`) consumes. -/
theorem belowBound_of_reducibleUniverse {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) candidate) :
    LevelExpr.denote levelExpr env < bound := by
  generalize hTypeCode :
    (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope) = typeCode at reducible
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible _ih =>
      subst hTypeCode
      exact absurd weakHeadStep (by exact fun weakHeadStepFromUniverse => nomatch weakHeadStepFromUniverse)
  | neutral _noStep _notPi notUniverse _notEmpty _notFlat =>
      subst hTypeCode
      exact absurd rfl notUniverse
  | piType _codomainCandidate _domainReducible _codomainReducible _ihDomain _ihCodomain =>
      exact nomatch hTypeCode
  | universeCode levelExpr' flag' belowBound' =>
      injection hTypeCode with _scopeEq _genEq payloadEq _childEq
      injection payloadEq with levelEq _flagEq
      rw [levelEq]
      exact belowBound'
  | dataEmpty =>
      exact nomatch hTypeCode
  | dataFlat flatPinned =>
      rw [← hTypeCode] at flatPinned
      exact nomatch flatPinned
  | ofPointwiseIff _innerReducible _pointwiseIff inductiveHypothesis =>
      exact inductiveHypothesis hTypeCode

end FX1Poly.Typed
