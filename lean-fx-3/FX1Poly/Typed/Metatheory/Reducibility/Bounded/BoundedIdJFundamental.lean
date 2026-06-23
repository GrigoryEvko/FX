import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Core.Eliminators.Core.IdentityEliminatorGeneralCandidateMember
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Canonicity.BasedReflCandidate
import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Typed.Cell.UnionCellSubstitution

/-! # FX1Poly/Typed/BoundedIdJFundamental
    — the bounded DEPENDENT `idJ` member engine (DEP-ID bridge, table-independent, engine half)

The identity-eliminator analogue of `fundamentalFstAtBoundedSucc` (`BoundedPairProjectionFundamental`).  `idJ` is
the PATH-INDUCTION eliminator: from a witness `p : Id A e e` (a reflexive identity), a base case `d : resultType`,
and a (vestigial, two-binder) motive, the recursor `idJ motive d p` contracts DIRECTLY to the base case on `refl`
(`idJ motive d (refl w) ↝ d`).  Like `fst` and unlike the recursive eliminators, the result type is NON-DEPENDENT
in the table presentation — `idJElimRule.outputType` is the `resultType` PARAM (its own universe obligation), and
the base case inhabits that same `resultType` directly — so the base-case discharge is a STRAIGHT determinism
transport (no scrutinee-reduction lockstep, no application residue).

## What DEP-ID buys

The scrutinee arrives via `idMemberAtBounded_dataTaitCandidate` as the TWO-ENDPOINT based candidate
`dataTaitCandidate (termIndexedCodeValuePredicate gen_idCode e e) = dataTaitCandidate (isReflValueBetween e e)` —
the model flip that routed `gen_idCode` through the `dataTermIndexed` arm.  The Core member
`idJDependentReducibleMember` consumes the weaker endpoint-blind `dataTaitCandidate isReflValue`, so this engine
weakens the based member down to `isReflValue` (`isReflValue_ofIsReflValueBetween`, pointwise) before feeding it —
the based endpoint conversions are what the GENUINE motive-reclassification consistency leg will consume, but the
table-presentation row needs only the head shape.

## The residues (vs `fst`)

Two standing residues threaded to the closed-term consistency leg, neither dischargeable from the three
`idJElimRule` obligations (witness, base case, result type):

  * the **vestigial-motive strong normalization** (`motiveStronglyNormalizing`): the motive is the arity-3 cell's
    first child (binderShift 2) but carries NO obligation in `idJElimRule`, so its SN — needed for the idJ cell's
    spine SN — is supplied where the full typing derivation provides motive well-formedness (the `optionMatch`
    application-SN residue analogue);
  * the **reach-conditioned base-case member** (`baseCaseMemberIfReachesRefl`): in the table presentation the base
    case inhabits `resultType` directly, so the row discharges it OUTRIGHT from the base-case obligation IH (no
    condition needed) — but the engine states it conditioned (on the scrutinee reaching `refl`) to match the Core
    member's shape, the `fst` component-residue idiom.

## Scope note (the `+1` index)

Stated at the successor closing scope `closingScope + 1` because the result type's member weak-head expansion
(`ReducibleTypeAtBounded.memberWeakHeadExpansion`) and CR1 are stated at `scope + 1` — exactly as
`fstMemberAtBounded`.  The `+1`-closing fundamental-theorem motive always closes into `targetScope + 1`, so the FT
arm supplies this scope.

## Zero-axiom verification

`idJMemberAtBounded` composes the Core `idJDependentReducibleMember` with the shipped bounded `memberWeakHead\
Expansion` / `isReducibilityCandidate` / `deterministic`.  `fundamentalIdJAtBoundedSucc` recovers the result type
from the `resultType` universe obligation (A2 bridge + `universeCodeReducibleAtBounded_belowBound`), extracts the
based scrutinee `dataTaitCandidate` via `idMemberAtBounded_dataTaitCandidate` and weakens it pointwise via
`isReflValue_ofIsReflValueBetween`, and threads the two residues.  No induction, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **The bounded `idJ` member arm.**  Given the result type `resultType` is bound-reducible (candidate
`resultCandidate`), the motive / base case are strongly normalizing, the witness is a head-expansion-closed
`dataTaitCandidate isReflValue` member, and the base case is a result member WHEN the witness reaches a `refl`,
the `idJ` cell is a bound-reducible member of `resultType`.  Instantiates the Core `idJDependentReducibleMember`
at `resultCandidate`: the head-expansion / SN-neutral closures are the result candidate's `memberWeakHeadExpansion`
/ `isReducibilityCandidate.memberOfStronglyNormalizingNeutral`, and the conditioned base member is transported
into `resultCandidate` by `ReducibleTypeAtBounded.deterministic` (the `fst`-arm direct transport — J contracts to
the base case directly, no branch application). -/
theorem idJMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {motive : RawTerm (closingScope + 1 + 2)}
    {witness baseCase resultType : RawTerm (closingScope + 1)}
    {resultCandidate : RawTerm (closingScope + 1) → Prop}
    (resultReducible : ReducibleTypeAtBounded env bound resultType resultCandidate)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (baseCaseStronglyNormalizing : IsStronglyNormalizing baseCase)
    (scrutineeMember : dataTaitCandidate isReflValue witness)
    (baseCaseMemberIfReachesRefl : ∀ reflWitness : RawTerm (closingScope + 1),
        StepStar witness (reflCell reflWitness) →
        IsReducibleMemberAtBounded env bound resultType baseCase) :
    IsReducibleMemberAtBounded env bound resultType (idJCell motive baseCase witness) := by
  refine ⟨resultCandidate, resultReducible, ?_⟩
  refine idJDependentReducibleMember resultCandidate
    (fun weakHeadStep contractumMember redexStronglyNormalizing =>
      ReducibleTypeAtBounded.memberWeakHeadExpansion resultReducible weakHeadStep
        redexStronglyNormalizing contractumMember)
    (fun neutralStronglyNormalizing neutral =>
      (ReducibleTypeAtBounded.isReducibilityCandidate resultReducible).memberOfStronglyNormalizingNeutral
        neutralStronglyNormalizing neutral)
    motiveStronglyNormalizing baseCaseStronglyNormalizing
    scrutineeMember
    (fun reflWitness reaches => ?_)
  obtain ⟨candidateBase, candidateBaseReducible, baseInCandidate⟩ :=
    baseCaseMemberIfReachesRefl reflWitness reaches
  exact (ReducibleTypeAtBounded.deterministic candidateBaseReducible resultReducible baseCase).mp baseInCandidate

/-- **The `+1`-closing dependent `idJ` fundamental-theorem arm (table-independent engine).**  From the witness's
`idTypeCell typeCode endpoint endpoint` membership (a reflexive identity), the base case's `resultType` membership,
and the result type's universe membership, `idJ motive baseCase witness` satisfies the `+1`-closing fundamental
conclusion at the NON-DEPENDENT result type `resultType`.  As in `fundamentalFstAtBoundedSucc`, the result-type
reducibility is recovered straight from the `resultType` universe obligation by the A2 bridge
`reducibleTypeAtBoundFromUniverseMemberBounded`; the scrutinee `dataTaitCandidate` is the based
`idMemberAtBounded_dataTaitCandidate`, weakened pointwise to `isReflValue`.  The vestigial-motive SN residue and
the (outright-dischargeable) reach-conditioned base-case member residue thread to the closed-term consistency leg.
The elim-FT row wires it from `idJElimRule`'s three obligation IHs. -/
theorem fundamentalIdJAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {typeCode endpoint resultType : RawTerm scope}
    {motive : RawTerm (scope + 2)} {witness baseCase : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (witnessConclusion : FundamentalConclusionAtBoundedSucc env bound context witness
      (idTypeCell typeCode endpoint endpoint))
    (baseCaseConclusion : FundamentalConclusionAtBoundedSucc env bound context baseCase resultType)
    (resultTypeConclusion : FundamentalConclusionAtBoundedSucc env bound context resultType
      (universeCodeCell levelExpr flag))
    (motiveStronglyNormalizing : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        IsStronglyNormalizing (RawTerm.subst (iterateLiftRaw substitution 2) motive)) :
    FundamentalConclusionAtBoundedSucc env bound context (idJCell motive baseCase witness) resultType := by
  intro _targetScope substitution envReducible
  have witnessIdMember := witnessConclusion substitution envReducible
  have baseCaseMember := baseCaseConclusion substitution envReducible
  have resultTypeUniverseMember := resultTypeConclusion substitution envReducible
  rw [subst_universeCodeCell] at resultTypeUniverseMember
  obtain ⟨universeCandidate, universeCandidateReducible, resultTypeInUniverse⟩ := resultTypeUniverseMember
  obtain ⟨resultCandidate, resultReducible⟩ :=
    reducibleTypeAtBoundFromUniverseMemberBounded env bound
      ⟨universeCandidate, universeCandidateReducible, resultTypeInUniverse⟩
      (universeCodeReducibleAtBounded_belowBound universeCandidateReducible)
  -- The based scrutinee candidate `dataTaitCandidate (isReflValueBetween e e)` weakens pointwise to the
  -- endpoint-blind `dataTaitCandidate isReflValue` the Core member consumes.
  have scrutineeBased := idMemberAtBounded_dataTaitCandidate witnessIdMember
  have scrutineeMember : dataTaitCandidate isReflValue (RawTerm.subst substitution witness) :=
    ⟨scrutineeBased.1, fun normalForm reaches normal =>
      (scrutineeBased.2 normalForm reaches normal).imp isReflValue_ofIsReflValueBetween id⟩
  rw [subst_idJCell]
  exact idJMemberAtBounded env bound resultReducible
    (motiveStronglyNormalizing substitution envReducible)
    (stronglyNormalizing_of_memberAtBoundedSucc baseCaseMember)
    scrutineeMember
    (fun _reflWitness _reaches => baseCaseMember)

end FX1Poly.Typed
