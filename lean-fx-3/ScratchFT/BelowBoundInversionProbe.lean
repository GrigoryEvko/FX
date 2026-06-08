import FX1Poly.Typed.DenoteKeyedBoundedReducibility

/-! Probe (NEVER committed): OB-2a — the universe gate inversion.
    `ReducibleTypeAtBounded env bound (Type@levelExpr) candidate → denote levelExpr env < bound`.
    A universe code is weak-head-normal (no whnfExpand), neutral-excluded (notUniverse), non-Π (piType
    index mismatch), so the derivation must be the gated `universeCode` arm — which carries `belowBound`.
    ofPointwiseIff recurses on the same index. Index-inversion via generalize+induction with the threaded
    `hTypeCode` equality; watch for propext leaks on the cell-index injection. -/

namespace FX1Poly.Typed.Spike
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

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
      exact absurd weakHeadStep (by exact fun s => nomatch s)
  | neutral _noStep _notPi notUniverse =>
      subst hTypeCode
      exact absurd rfl notUniverse
  | piType _codomainCandidate _domainReducible _codomainReducible _ihD _ihC =>
      exact nomatch hTypeCode
  | universeCode levelExpr' flag' belowBound' =>
      injection hTypeCode with _scopeEq _genEq payloadEq _childEq
      injection payloadEq with levelEq _flagEq
      rw [levelEq]
      exact belowBound'
  | ofPointwiseIff _innerReducible _pointwiseIff ih =>
      exact ih hTypeCode

end FX1Poly.Typed.Spike

#print axioms FX1Poly.Typed.Spike.belowBound_of_reducibleUniverse
