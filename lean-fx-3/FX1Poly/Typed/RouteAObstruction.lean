import FX1Poly.Typed.ReducibleTypeAtAllLevelsInduction

/-! # FX1Poly/Typed/RouteAObstruction
    — the fuel-0 universe-vacuity obstruction, pinned as committed theorems (SN-001)

The "all-levels / member-extension" route to strong normalization (Route A) tries to bootstrap
`IsReducibleTypeAtAllLevels` from a single fuel level via the type-level-irrelevance induction
(`ReducibleTypeAtAllLevelsInduction`).  That route is DEAD at its base, for a precise structural reason
recorded only in prose in `ReducibleTypeAtAllLevelsInduction`'s frontier note.  This file turns that note
into committed, audit-gated THEOREMS.

The external-`Nat`-fuel relation has `ReducibleTypeAt 0 = ReducibleTypeStep (fun _ _ => False)` — an EMPTY
lower relation.  Two facts pin the obstruction:

* `IsReducibleMemberAt.universeCodeHasNoMemberAtZero` (shipped, `FX1Poly.Core`): at fuel 0 the universe
  candidate `universeReducibilityPredicate (fun _ _ => False)` is the EMPTY predicate — no term inhabits
  `Type@e` at fuel 0, because its `∃ candidate, (fun _ _ => False) _ candidate` conjunct is `∃ _, False`,
  uninhabited.

* `universeDomainPiVacuouslyReducibleAtZero` (here): consequently a universe-DOMAIN Π type
  `Π (x : Type@e). C` is reducible at fuel 0 for EVERY codomain `C` — VACUOUSLY: the `piType` arm's
  codomain obligation ranges over the empty domain candidate, so it is discharged carrying NO information
  about `C`.

* `universeDomainPiTrivialCandidateAtZero` (here, the sharpening): the fuel-0 candidate of such a Π is
  pointwise-equivalent to the TRIVIAL predicate `fun _ => True` — every term is a fuel-0 "member".

Together: fuel-0 reducibility of `Π (x : Type@e). C` is independent of `C` (it holds uniformly, with the
trivial candidate), so it cannot feed the level-1 codomain obligation that
`ReducibleTypeAtAllLevelsInduction`'s `piArm` needs.  The `0 ↔ 1` base of any monotonicity /
level-irrelevance argument (`StratifiedReducibleLevelCongr.existsCongr`'s degenerate base) is therefore
unbridgeable WITHIN the fuel model.  This is the formal input justifying the pivot to the
classifier-universe-level / validity-derivation-indexed reformulation explored from SN-002 onward.

## Zero-axiom verification

Theorem 1 fires the `piType` arm over the `universeCode` domain arm with a vacuous codomain premise (the
empty-domain existential discharged by `False.elim`).  Theorem 2 wraps it through `ofPointwiseIff` with the
trivially-true pointwise equivalence (built by `Iff.intro` / `constructor`, never `rw [← iff]`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The fuel-0 universe-vacuity obstruction (positive witness).**  A universe-DOMAIN Π type
`Π (x : Type@e). C` is reducible at fuel level 0 for EVERY codomain `C` — VACUOUSLY.  The domain candidate
at fuel 0 is `universeReducibilityPredicate (fun _ _ => False)`, whose `∃ candidate, (fun _ _ => False) _
candidate` component is uninhabited, so the `piType` arm's per-argument codomain obligation is discharged
with NO constraint on `C` (by `False.elim`).  Holding uniformly in `C`, fuel-0 reducibility carries no
information that could feed a level-1 codomain obligation — the structural reason the all-levels /
member-extension route (Route A) cannot bootstrap (cf.
`IsReducibleMemberAt.universeCodeHasNoMemberAtZero`, the empty-membership fact this rests on). -/
theorem universeDomainPiVacuouslyReducibleAtZero {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (codomainCode : RawTerm (scope + 1)) :
    IsReducibleTypeAt 0 (piTyCodeCell (universeCodeCell levelExpr flag) codomainCode) := by
  refine ⟨_, ReducibleTypeStep.piType (fun _ _ => True)
    (ReducibleTypeStep.universeCode levelExpr flag) ?_⟩
  intro argument argumentInDomain
  obtain ⟨_candidate, contra⟩ := argumentInDomain.2
  exact contra.elim

/-- **The fuel-0 candidate is trivial (the "carries no information" sharpening).**  The fuel-0 candidate of
a universe-domain Π type `Π (x : Type@e). C` is pointwise-equivalent to `fun _ => True` — every term is a
fuel-0 "member", because the membership predicate quantifies over the empty domain candidate.  This makes
the vacuity precise: the fuel-0 relation places NO constraint on inhabitants of a universe-domain Π. -/
theorem universeDomainPiTrivialCandidateAtZero {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (codomainCode : RawTerm (scope + 1)) :
    ReducibleTypeAt 0 (piTyCodeCell (universeCodeCell levelExpr flag) codomainCode)
      (fun _functionTerm => True) := by
  refine ReducibleTypeStep.ofPointwiseIff
    (ReducibleTypeStep.piType (fun _ _ => True)
      (ReducibleTypeStep.universeCode levelExpr flag)
      (fun _argument argumentInDomain => ?_)) (fun _functionTerm => ?_)
  · obtain ⟨_candidate, contra⟩ := argumentInDomain.2
    exact contra.elim
  · constructor
    · intro _membership
      trivial
    · intro _trueWitness _argument _argumentInDomain
      trivial

end FX1Poly.Typed
