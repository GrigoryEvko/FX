import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Core.Eliminators.Core.PairProjectionGeneralCandidateMember
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Typed.Ledger.Cell.CellConstructors
import FX1Poly.Typed.Ledger.Cell.CellSubstitution
import FX1Poly.Typed.Ledger.Cell.UnionCellSubstitution

/-! # FX1Poly/Typed/BoundedPairProjectionFundamental
    — the bounded `fst` / `snd` member engines (DEP-PROJ bridge, table-independent, engine half)

The Σ-projection analogue of `eitherMatchMemberAtBounded` (`BoundedEitherMatchFundamental`).  Projection is the
PROJECTING shape — structurally simpler than the match eliminators: `fst` / `snd` are SINGLE-child cells (no
motive, no branch terms), the ι contracts to a DIRECT child (`fst (pair a b) ↝ a`), and — unlike the match
eliminators — the result type is NON-DEPENDENT: `fst`'s output is the first component TYPE `firstType` (its own
universe obligation), not a motive instantiated at the scrutinee.  So this engine carries NO motive premise and NO
subst0 plumbing; the result-type reducibility comes straight from the component-type obligation via the A2 bridge
`reducibleTypeAtBoundFromUniverseMemberBounded` (the same recovery the formation FT arms use), and the scrutinee
arrives as a `dataTaitCandidate isPairValue` member (via the carrier-aware `productMemberAtBounded_dataTaitCandidate`).

## The single threaded residue (vs `eitherMatch`)

Like `eitherMatch`'s inl/inr member residues, the conditioned component-membership premise
(`firstMemberIfReachesPair : ∀ first second, scrutinee ↠ pair first second → member first`) is NOT dischargeable at
the open/bounded level: the scrutinee arrives as the WEAK `dataTaitCandidate isPairValue` (the carrier content is
forgotten when the Core member consumes it), so extracting `first ∈ ⟦firstType⟧` for a non-normal reachable pair
needs the substitution-SN content the fundamental theorem itself supplies — available at the closed-term
consistency leg where the closed scrutinee reduces to a canonical (normal) pair.  So this arm THREADS exactly one
member residue (no branch-application-SN residue — projection extracts a DIRECT child, not a branch application).

## Scope note (the `+1` index)

Stated at the successor closing scope `closingScope + 1` because the result type's member weak-head expansion
(`ReducibleTypeAtBounded.memberWeakHeadExpansion`) and CR1 are stated at `scope + 1` — exactly as
`eitherMatchMemberAtBounded`.  The `+1`-closing fundamental-theorem motive always closes into `targetScope + 1`,
so the FT arm supplies this scope.

## Zero-axiom verification

`fst`/`sndMemberAtBounded` compose the Core `fst`/`sndDependentReducibleMember` with the shipped bounded
`memberWeakHeadExpansion` / `isReducibilityCandidate` / `deterministic`.  `fundamentalFst`/`SndAtBoundedSucc`
recover the result type from the component-type universe obligation (A2 bridge + `universeCodeReducibleAtBounded_\
belowBound`), extract the scrutinee `dataTaitCandidate` (carrier-aware inversion), and thread the one component
residue.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **The bounded `fst` member arm.**  Given the first component type `firstType` is bound-reducible (candidate
`resultCandidate`), the scrutinee is a head-expansion-closed `dataTaitCandidate isPairValue` member, and the first
component is a result member WHEN the scrutinee reaches a pair, the `fst` cell is a bound-reducible member of
`firstType`.  Instantiates the Core `fstDependentReducibleMember` at `resultCandidate`: the head-expansion /
SN-neutral closures are the result candidate's `memberWeakHeadExpansion` /
`isReducibilityCandidate.memberOfStronglyNormalizingNeutral`, and the conditioned component member is transported
into `resultCandidate` by `ReducibleTypeAtBounded.deterministic`.  The projecting twin of
`eitherMatchMemberAtBounded`, with one DIRECT-component residue (no branch-application SN). -/
theorem fstMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {scrutinee firstType : RawTerm (closingScope + 1)}
    {resultCandidate : RawTerm (closingScope + 1) → Prop}
    (resultReducible : ReducibleTypeAtBounded env bound firstType resultCandidate)
    (scrutineeMember : dataTaitCandidate isPairValue scrutinee)
    (firstMemberIfReachesPair : ∀ first second : RawTerm (closingScope + 1),
        StepStar scrutinee (pairCell first second) →
        IsReducibleMemberAtBounded env bound firstType first) :
    IsReducibleMemberAtBounded env bound firstType (fstCell scrutinee) := by
  refine ⟨resultCandidate, resultReducible, ?_⟩
  refine fstDependentReducibleMember resultCandidate
    (fun weakHeadStep contractumMember redexStronglyNormalizing =>
      ReducibleTypeAtBounded.memberWeakHeadExpansion resultReducible weakHeadStep
        redexStronglyNormalizing contractumMember)
    (fun neutralStronglyNormalizing neutral =>
      (ReducibleTypeAtBounded.isReducibilityCandidate resultReducible).memberOfStronglyNormalizingNeutral
        neutralStronglyNormalizing neutral)
    scrutineeMember
    (fun first second reachesPair => ?_)
  obtain ⟨candidateFirst, candidateFirstReducible, firstInCandidate⟩ :=
    firstMemberIfReachesPair first second reachesPair
  exact (ReducibleTypeAtBounded.deterministic candidateFirstReducible resultReducible first).mp firstInCandidate

/-- **The bounded `snd` member arm.**  Symmetric to `fstMemberAtBounded`, projecting the SECOND component: the
conditioned premise gives the second component a result member of `secondType` WHEN the scrutinee reaches a pair,
transported into `resultCandidate` by `ReducibleTypeAtBounded.deterministic`.  Shares every pair helper with `fst`
— the single-constructor projecting eliminator's two halves. -/
theorem sndMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {scrutinee secondType : RawTerm (closingScope + 1)}
    {resultCandidate : RawTerm (closingScope + 1) → Prop}
    (resultReducible : ReducibleTypeAtBounded env bound secondType resultCandidate)
    (scrutineeMember : dataTaitCandidate isPairValue scrutinee)
    (secondMemberIfReachesPair : ∀ first second : RawTerm (closingScope + 1),
        StepStar scrutinee (pairCell first second) →
        IsReducibleMemberAtBounded env bound secondType second) :
    IsReducibleMemberAtBounded env bound secondType (sndCell scrutinee) := by
  refine ⟨resultCandidate, resultReducible, ?_⟩
  refine sndDependentReducibleMember resultCandidate
    (fun weakHeadStep contractumMember redexStronglyNormalizing =>
      ReducibleTypeAtBounded.memberWeakHeadExpansion resultReducible weakHeadStep
        redexStronglyNormalizing contractumMember)
    (fun neutralStronglyNormalizing neutral =>
      (ReducibleTypeAtBounded.isReducibilityCandidate resultReducible).memberOfStronglyNormalizingNeutral
        neutralStronglyNormalizing neutral)
    scrutineeMember
    (fun first second reachesPair => ?_)
  obtain ⟨candidateSecond, candidateSecondReducible, secondInCandidate⟩ :=
    secondMemberIfReachesPair first second reachesPair
  exact (ReducibleTypeAtBounded.deterministic candidateSecondReducible resultReducible second).mp secondInCandidate

/-- **The `+1`-closing `fst` fundamental-theorem arm (table-independent engine).**  From the scrutinee's
`productTypeCell firstType secondType` membership and the first component type's universe membership, `fst pairTerm`
satisfies the `+1`-closing fundamental conclusion at the NON-DEPENDENT result type `firstType`.  Unlike the match
eliminators, there is no motive: the result-type reducibility is recovered straight from the `firstType` universe
obligation by the A2 bridge `reducibleTypeAtBoundFromUniverseMemberBounded` (with `belowBound` from
`universeCodeReducibleAtBounded_belowBound`); the scrutinee `dataTaitCandidate` extraction is the carrier-aware
`productMemberAtBounded_dataTaitCandidate`.  The one conditioned component-member residue threads to the closed-term
consistency leg.  The elim-FT row wires it from `fstElimRule`'s two obligation IHs. -/
theorem fundamentalFstAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {firstType secondType pairTerm : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (pairTermConclusion : FundamentalConclusionAtBoundedSucc env bound context pairTerm
      (productTypeCell firstType secondType))
    (firstTypeConclusion : FundamentalConclusionAtBoundedSucc env bound context firstType
      (universeCodeCell levelExpr flag))
    (firstMemberIfReachesPair : ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ first second : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution pairTerm) (pairCell first second) →
          IsReducibleMemberAtBounded env bound (RawTerm.subst substitution firstType) first) :
    FundamentalConclusionAtBoundedSucc env bound context (fstCell pairTerm) firstType := by
  intro _targetScope substitution envReducible
  have pairMember := pairTermConclusion substitution envReducible
  have firstTypeUniverseMember := firstTypeConclusion substitution envReducible
  rw [subst_universeCodeCell] at firstTypeUniverseMember
  obtain ⟨universeCandidate, universeCandidateReducible, firstTypeInUniverse⟩ := firstTypeUniverseMember
  obtain ⟨resultCandidate, resultReducible⟩ :=
    reducibleTypeAtBoundFromUniverseMemberBounded env bound
      ⟨universeCandidate, universeCandidateReducible, firstTypeInUniverse⟩
      (universeCodeReducibleAtBounded_belowBound universeCandidateReducible)
  rw [subst_fstCell]
  exact fstMemberAtBounded env bound resultReducible
    (productMemberAtBounded_dataTaitCandidate pairMember)
    (firstMemberIfReachesPair substitution envReducible)

/-- **The `+1`-closing `snd` fundamental-theorem arm (table-independent engine).**  Symmetric to
`fundamentalFstAtBoundedSucc`, at the NON-DEPENDENT result type `secondType` recovered from the second component
type's universe obligation, projecting the second component.  The elim-FT row wires it from `sndElimRule`'s two
obligation IHs. -/
theorem fundamentalSndAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {firstType secondType pairTerm : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (pairTermConclusion : FundamentalConclusionAtBoundedSucc env bound context pairTerm
      (productTypeCell firstType secondType))
    (secondTypeConclusion : FundamentalConclusionAtBoundedSucc env bound context secondType
      (universeCodeCell levelExpr flag))
    (secondMemberIfReachesPair : ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ first second : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution pairTerm) (pairCell first second) →
          IsReducibleMemberAtBounded env bound (RawTerm.subst substitution secondType) second) :
    FundamentalConclusionAtBoundedSucc env bound context (sndCell pairTerm) secondType := by
  intro _targetScope substitution envReducible
  have pairMember := pairTermConclusion substitution envReducible
  have secondTypeUniverseMember := secondTypeConclusion substitution envReducible
  rw [subst_universeCodeCell] at secondTypeUniverseMember
  obtain ⟨universeCandidate, universeCandidateReducible, secondTypeInUniverse⟩ := secondTypeUniverseMember
  obtain ⟨resultCandidate, resultReducible⟩ :=
    reducibleTypeAtBoundFromUniverseMemberBounded env bound
      ⟨universeCandidate, universeCandidateReducible, secondTypeInUniverse⟩
      (universeCodeReducibleAtBounded_belowBound universeCandidateReducible)
  rw [subst_sndCell]
  exact sndMemberAtBounded env bound resultReducible
    (productMemberAtBounded_dataTaitCandidate pairMember)
    (secondMemberIfReachesPair substitution envReducible)

end FX1Poly.Typed
