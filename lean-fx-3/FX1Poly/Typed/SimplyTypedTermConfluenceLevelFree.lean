import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree
import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Typed/SimplyTypedTermConfluenceLevelFree
    — Church-Rosser and normal-form uniqueness for simply-typed terms (the SN payoff continued)

The strong-normalization result for simply-typed terms (`SimplyTypedTermFundamentalLevelFree`) feeds the
Newman bridge to give CONFLUENCE (Church-Rosser) and NORMAL-FORM UNIQUENESS for the simply-typed fragment —
the foundation for deciding conversion between simply-typed terms.

  * `reductsJoinUnderSubst` — Church-Rosser: any two `StepStar` reducts of a simply-typed term (closed by a
    reducible substitution) join.  This is `confluence_of_localJoin_and_accessible` (the per-term Newman lift:
    strong normalization + the `cd_lemma` local join ⇒ global confluence below the term) fed the term's
    strong normalization from `SimplyTypedTermLF.stronglyNormalizingUnderSubst`.

  * `normalFormUniqueUnderSubst` / `normalFormUniqueClosed` — normal-form uniqueness: any two NORMAL forms
    (no outgoing `Step`) reachable from a simply-typed term are equal.  The two reducts join (Church-Rosser);
    `StepStar.eq_of_noStep` forces each normal endpoint to equal the common reduct, so the endpoints agree.

Together with a future weak-normalization witness (strong normalization ⇒ a normal form is reachable, the
`Acc`-descent existence half), these give a canonical normal form per simply-typed term and hence decidable
conversion on the fragment (`Conv.iff_eq_of_noStep` on the normal forms).

## Zero-axiom verification

`reductsJoinUnderSubst` is the shipped `confluence_of_localJoin_and_accessible` applied to the fundamental
theorem's strong-normalization corollary; the uniqueness theorems destructure the resulting `Join` and apply
`StepStar.eq_of_noStep` to each rigid endpoint.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **Church-Rosser for simply-typed terms.**  Any two `StepStar` reducts of a simply-typed term, closed by a
reducible substitution, join — the per-term Newman lift (`confluence_of_localJoin_and_accessible`: strong
normalization + the `cd_lemma` local join ⇒ confluence below the term) fed the term's strong normalization
from the fundamental theorem. -/
theorem SimplyTypedTermLF.reductsJoinUnderSubst {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {term type : RawTerm scope}
    (typed : SimplyTypedTermLF context term type) {targetScope : Nat}
    (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnv context substitution)
    {leftReduct rightReduct : RawTerm (targetScope + 1)}
    (leftChain : StepStar (RawTerm.subst substitution term) leftReduct)
    (rightChain : StepStar (RawTerm.subst substitution term) rightReduct) :
    Join leftReduct rightReduct :=
  confluence_of_localJoin_and_accessible
    (typed.stronglyNormalizingUnderSubst substitution envReducible) leftChain rightChain

/-- **Normal-form uniqueness for simply-typed terms.**  Any two normal forms (no outgoing `Step`) reachable
from a simply-typed term — closed by a reducible substitution — are equal.  The two reducts join
(`reductsJoinUnderSubst`); `StepStar.eq_of_noStep` forces each rigid normal endpoint to equal the common
reduct. -/
theorem SimplyTypedTermLF.normalFormUniqueUnderSubst {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {term type : RawTerm scope}
    (typed : SimplyTypedTermLF context term type) {targetScope : Nat}
    (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnv context substitution)
    {leftNormal rightNormal : RawTerm (targetScope + 1)}
    (leftChain : StepStar (RawTerm.subst substitution term) leftNormal)
    (rightChain : StepStar (RawTerm.subst substitution term) rightNormal)
    (leftNoStep : ∀ reduct : RawTerm (targetScope + 1), Step leftNormal reduct → False)
    (rightNoStep : ∀ reduct : RawTerm (targetScope + 1), Step rightNormal reduct → False) :
    leftNormal = rightNormal := by
  obtain ⟨commonTerm, leftToCommon, rightToCommon⟩ :=
    typed.reductsJoinUnderSubst substitution envReducible leftChain rightChain
  have commonIsLeft : commonTerm = leftNormal := StepStar.eq_of_noStep leftNoStep leftToCommon
  have commonIsRight : commonTerm = rightNormal := StepStar.eq_of_noStep rightNoStep rightToCommon
  exact commonIsLeft.symm.trans commonIsRight

/-- **Normal-form uniqueness for closed simply-typed terms.**  The tangible specialization: a closed
simply-typed term has at most one normal form (the empty environment is vacuously reducible). -/
theorem SimplyTypedTermLF.normalFormUniqueClosed {profile : PolyProfile}
    {term type : RawTerm 0} (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1))
    {leftNormal rightNormal : RawTerm (targetScope + 1)}
    (leftChain : StepStar (RawTerm.subst substitution term) leftNormal)
    (rightChain : StepStar (RawTerm.subst substitution term) rightNormal)
    (leftNoStep : ∀ reduct : RawTerm (targetScope + 1), Step leftNormal reduct → False)
    (rightNoStep : ∀ reduct : RawTerm (targetScope + 1), Step rightNormal reduct → False) :
    leftNormal = rightNormal :=
  typed.normalFormUniqueUnderSubst substitution (ReducibleEnv.empty substitution)
    leftChain rightChain leftNoStep rightNoStep

end FX1Poly.Typed
