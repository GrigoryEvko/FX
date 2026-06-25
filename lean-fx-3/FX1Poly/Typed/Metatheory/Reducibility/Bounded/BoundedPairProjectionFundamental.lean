import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Core.Eliminators.Core.PairProjectionGeneralCandidateMember
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Typed.Cell.CellSubstitution
import FX1Poly.Typed.Cell.UnionCellSubstitution

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

/-- **The bounded `fst` member arm (projection candidate, residue-free).**  Given the first component type
`firstType` is bound-reducible (candidate `firstCandidate`) and the scrutinee rides in the Σ-projection candidate
`projectionPairCandidate firstCandidate secondCandidate`, the `fst` cell is a bound-reducible member of `firstType`
— DIRECTLY: the projection candidate's second conjunct IS `firstCandidate (fstSpineCell scrutinee) =
firstCandidate (fstCell scrutinee)` (defeq).  No head-expansion / SN-neutral / reach-conditioned plumbing: the
Geuvers Σ-projection model records `fc (fst t)` forward at the type, so the once-threaded
`firstMemberIfReachesPair` residue VANISHES (`projectionPairCandidate_reachableComponentMembers` already lives
inside the membership).  The Σ-swap payoff. -/
theorem fstMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {scrutinee firstType : RawTerm (closingScope + 1)}
    {firstCandidate secondCandidate : RawTerm (closingScope + 1) → Prop}
    (firstReducible : ReducibleTypeAtBounded env bound firstType firstCandidate)
    (scrutineeMember : projectionPairCandidate firstCandidate secondCandidate scrutinee) :
    IsReducibleMemberAtBounded env bound firstType (fstCell scrutinee) :=
  ⟨firstCandidate, firstReducible, scrutineeMember.2.1⟩

/-- **The bounded `snd` member arm (projection candidate, residue-free).**  Symmetric to `fstMemberAtBounded`,
projecting the SECOND component: `projectionPairCandidate firstCandidate secondCandidate scrutinee`'s third
conjunct IS `secondCandidate (sndSpineCell scrutinee) = secondCandidate (sndCell scrutinee)` (defeq), so the `snd`
cell is a bound-reducible member of `secondType` directly — no reach-conditioned `secondMemberIfReachesPair`
residue.  Shares the Σ-swap payoff with `fst`. -/
theorem sndMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {scrutinee secondType : RawTerm (closingScope + 1)}
    {firstCandidate secondCandidate : RawTerm (closingScope + 1) → Prop}
    (secondReducible : ReducibleTypeAtBounded env bound secondType secondCandidate)
    (scrutineeMember : projectionPairCandidate firstCandidate secondCandidate scrutinee) :
    IsReducibleMemberAtBounded env bound secondType (sndCell scrutinee) :=
  ⟨secondCandidate, secondReducible, scrutineeMember.2.2⟩

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
    {firstType secondType pairTerm : RawTerm scope}
    (pairTermConclusion : FundamentalConclusionAtBoundedSucc env bound context pairTerm
      (productTypeCell firstType secondType)) :
    FundamentalConclusionAtBoundedSucc env bound context (fstCell pairTerm) firstType := by
  intro _targetScope substitution envReducible
  have pairMember := pairTermConclusion substitution envReducible
  rw [subst_fstCell]
  obtain ⟨firstCandidate, _secondCandidate, firstReducible, _secondReducible, projMember⟩ :=
    productMemberAtBounded_carrierAware pairMember
  exact fstMemberAtBounded env bound firstReducible projMember

/-- **The `+1`-closing `snd` fundamental-theorem arm (table-independent engine).**  Symmetric to
`fundamentalFstAtBoundedSucc`, at the NON-DEPENDENT result type `secondType` recovered from the second component
type's universe obligation, projecting the second component.  The elim-FT row wires it from `sndElimRule`'s two
obligation IHs. -/
theorem fundamentalSndAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {firstType secondType pairTerm : RawTerm scope}
    (pairTermConclusion : FundamentalConclusionAtBoundedSucc env bound context pairTerm
      (productTypeCell firstType secondType)) :
    FundamentalConclusionAtBoundedSucc env bound context (sndCell pairTerm) secondType := by
  intro _targetScope substitution envReducible
  have pairMember := pairTermConclusion substitution envReducible
  rw [subst_sndCell]
  obtain ⟨_firstCandidate, secondCandidate, _firstReducible, secondReducible, projMember⟩ :=
    productMemberAtBounded_carrierAware pairMember
  exact sndMemberAtBounded env bound secondReducible projMember

end FX1Poly.Typed
