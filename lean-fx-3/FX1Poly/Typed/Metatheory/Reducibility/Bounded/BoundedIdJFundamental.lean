import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Core.Eliminators.Core.IdentityEliminatorGeneralCandidateMember
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Canonicity.BasedReflCandidate
import FX1Poly.Core.Metatheory.Canonicity.BasedReflEndpointExtraction
import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Typed.Cell.UnionCellSubstitution
import FX1Poly.Typed.Cell.IdJDependentMotiveType

/-! # FX1Poly/Typed/BoundedIdJFundamental
    — the bounded DEPENDENT `idJ` member engine (DEP-ID bridge, table-independent, engine half)

The identity-eliminator analogue of `fundamentalFstAtBoundedSucc` (`BoundedPairProjectionFundamental`).  `idJ` is
the PATH-INDUCTION eliminator: from a witness `p : Id A left right`, a base case, and a two-binder motive
`C : (b : A) -> Id A left b -> U`, the recursor `idJ motive d p` contracts DIRECTLY to the base case on `refl`
(`idJ motive d (refl w) ↝ d`).

The LIVE engine is the GENUINE Paulin-Mohring bridge `fundamentalIdJGenuineAtBoundedSucc` (§ "JMAX-3" below),
matching the post-JMAX-3 table where `idJElimRule.outputType = idJMotiveAt motive right witness` (the dependent
instantiation `C[b := right, p := witness]`) and the base case inhabits the diagonal
`idJMotiveAt motive left (refl left)`.  This is what the elim-FT row (`fundamentalIdJRowAtBoundedSucc`) consumes.
The shared member arm `idJMemberAtBounded` (composing the Core `idJDependentReducibleMember` with the bounded
head-expansion / SN-neutral closures) is below.  The pre-JMAX-3 degenerate non-dependent engine
(`fundamentalIdJAtBoundedSucc`, a `resultType`-param loop-induction member) was RETIRED at JMAX-4.

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
Expansion` / `isReducibilityCandidate` / `deterministic`.  The genuine `fundamentalIdJGenuineAtBoundedSucc`
recovers the dependent OUTPUT type `idJMotiveAt motive right witness` from the two-binder motive's universe
obligation (`idJGenuineOutputTypeReducibleAtBounded`: extend the env twice at `b := right` / `p := witness`, run
the A2 bridge, reshape via `substTwoConsEqIdJMotiveAt`), extracts the based scrutinee `dataTaitCandidate` via
`idMemberAtBounded_dataTaitCandidate` weakened pointwise via `isReflValue_ofIsReflValueBetween`, and threads the
base-case residue.  No induction, no `funext`.  No `axiom`, `sorry`,
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

/-! The degenerate non-dependent `idJ` engine `fundamentalIdJAtBoundedSucc` (a loop-induction member at a
`resultType` param, the `fst`-style direct-determinism transport) was RETIRED at JMAX-4 — fully superseded by the
GENUINE Paulin-Mohring bridge below, which the elim-FT row consumes.  The shared member arm `idJMemberAtBounded`
(above) survives: both engines instantiate it. -/

/-! ## JMAX-3: the GENUINE Paulin-Mohring `idJ` bridge (dependent output, additive)

The degenerate `fundamentalIdJAtBoundedSucc` above pins a non-dependent `resultType` (loop induction).  The
genuine Paulin-Mohring engine below carries a real two-binder motive `C : (b : A) -> Id A left b -> U`: the
output type is `C[b := right, p := witness]` (`idJMotiveAt motive right witness`) and the base case is typed at
`C[b := left, p := refl left]` (`idJMotiveAt motive left (refl left)`).  It is ADDITIVE — it references
`idJCell` / `idJMotiveAt` / the generic Core member `idJMemberAtBounded`, never the degenerate rule — so it
compiles against the current green table and is wired by the JMAX-3 rule flip's elim-FT row. -/

/-- The motive's SECOND binder type `Id A left b` substitutes (with `b := rightImage`) to the closed identity
code `Id (A[sub]) (left[sub]) rightImage` — the witness obligation's type.  `subst_idTypeCell` is `rfl`, so the
two weakened carriers cancel the `cons`-head (`weaken_subst_cons`) and the `var 0` lands on `rightImage`. -/
theorem subst_cons_idJMotiveSecondBinderType {scope targetScope : Nat}
    (typeCode leftEndpoint : RawTerm scope) (rightImage : RawTerm targetScope)
    (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons rightImage substitution)
        (idJMotiveSecondBinderType typeCode leftEndpoint)
      = idTypeCell (RawTerm.subst substitution typeCode) (RawTerm.subst substitution leftEndpoint)
          rightImage := by
  unfold idJMotiveSecondBinderType
  rw [subst_idTypeCell, RawTerm.weaken_eq_rename, RawTerm.weaken_subst_cons,
    RawTerm.weaken_eq_rename, RawTerm.weaken_subst_cons]
  rfl

/-- Substituting a two-binder body through the doubly-extended environment `cons path (cons point sub)` is the
`idJMotiveAt` instantiation of the doubly-lifted body at `point` / `path` — the two-binder analogue of
`subst_cons_eq_subst0_lift` (which the dependent `boolElim` bridge uses at one binder).  The two `cons` slots
fill the motive's two binders; the doubly-lifted substitution crosses them and `subst_compose` realigns. -/
theorem substTwoConsEqIdJMotiveAt {scope targetScope : Nat} (motive : RawTerm (scope + 2))
    (point path : RawTerm targetScope) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons path (RawTermSubst.cons point substitution)) motive
      = idJMotiveAt (RawTerm.subst (iterateLiftRaw substitution 2) motive) point path := by
  have liftEq : iterateLiftRaw substitution 2
      = RawTermSubst.lift (RawTermSubst.lift substitution) := rfl
  unfold idJMotiveAt RawTerm.substPair
  rw [liftEq, RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
    cases positionValue with
    | zero => rfl
    | succ priorValue =>
        cases priorValue with
        | zero => rfl
        | succ deepValue =>
            dsimp only [RawTermSubst.compose, RawTermSubst.pair, RawTermSubst.cons,
              RawTermSubst.lift, RawTermSubst.singleton]
            rw [RawTerm.weaken_eq_rename
              (RawTerm.weaken (substitution ⟨deepValue,
                Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ positionBound)⟩))]
            rw [RawTerm.weaken_subst_cons
              (RawTerm.weaken (substitution ⟨deepValue,
                Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ positionBound)⟩))
              path (RawTermSubst.singleton point)]
            exact (RawTerm.weaken_subst_singleton
              (substitution ⟨deepValue,
                Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ positionBound)⟩) point).symm

/-- **The genuine `idJ` output-type reducibility (the two-binder motive-side recovery).**  From the motive's
universe membership in the 2-extended context `(context.cons typeCode).cons (idJMotiveSecondBinderType typeCode
left)`, the right endpoint's membership in `typeCode`, and the witness's membership in `Id A left right`, the
dependent OUTPUT type `idJMotiveAt motive right witness` is bound-reducible.  The two-binder analogue of
`dependentMotiveResultTypeReducibleAtBounded`: extend the environment twice (`b := right`, `p := witness`),
instantiate the motive's universe membership, run the A2 bridge, and reshape the doubly-`cons`-substituted
motive into the `idJMotiveAt` output via `substTwoConsEqIdJMotiveAt` + `subst_idJMotiveAt_iterateLift`. -/
theorem idJGenuineOutputTypeReducibleAtBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {typeCode leftEndpoint rightEndpoint : RawTerm scope}
    {motive : RawTerm (scope + 2)} {witness : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      ((context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint)) motive
      (universeCodeCell levelExpr flag))
    {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnvAtBounded env bound context substitution)
    (rightMember : IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution typeCode) (RawTerm.subst substitution rightEndpoint))
    (witnessIdMember : IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution (idTypeCell typeCode leftEndpoint rightEndpoint))
      (RawTerm.subst substitution witness)) :
    IsReducibleTypeAtBounded env bound
      (RawTerm.subst substitution (idJMotiveAt motive rightEndpoint witness)) := by
  have envWithEndpoint := ReducibleEnvAtBounded.cons envReducible rightMember
  have witnessSecondBinderMember :
      IsReducibleMemberAtBounded env bound
        (RawTerm.subst (RawTermSubst.cons (RawTerm.subst substitution rightEndpoint) substitution)
          (idJMotiveSecondBinderType typeCode leftEndpoint))
        (RawTerm.subst substitution witness) := by
    rw [subst_cons_idJMotiveSecondBinderType, ← subst_idTypeCell]
    exact witnessIdMember
  have envWithWitness := ReducibleEnvAtBounded.cons envWithEndpoint witnessSecondBinderMember
  have motiveUniverseMember := motiveConclusion
    (RawTermSubst.cons (RawTerm.subst substitution witness)
      (RawTermSubst.cons (RawTerm.subst substitution rightEndpoint) substitution))
    envWithWitness
  rw [subst_universeCodeCell] at motiveUniverseMember
  obtain ⟨universeCandidate, universeCandidateReducible, motiveInUniverse⟩ := motiveUniverseMember
  obtain ⟨outputCandidate, outputReducible⟩ :=
    reducibleTypeAtBoundFromUniverseMemberBounded env bound
      ⟨universeCandidate, universeCandidateReducible, motiveInUniverse⟩
      (universeCodeReducibleAtBounded_belowBound universeCandidateReducible)
  rw [substTwoConsEqIdJMotiveAt, ← subst_idJMotiveAt_iterateLift] at outputReducible
  exact ⟨outputCandidate, outputReducible⟩

/-- **The genuine `idJ` motive under-two-binders strong normalization (the elim ROW's vestigial-motive SN residue,
DISCHARGED from the obligation IHs).**  The identity-eliminator analogue of
`dependentSuccBranchUnderTwoBindersStronglyNormalizing` (`BoundedNatElimFundamentalBridge`): the genuine motive
`C : (b : A) -> Id A left b -> U` sits under TWO binders, and its open strong normalization
`subst (lift² substitution) motive` is what the genuine engine's old `motiveStronglyNormalizing` premise demanded.
Post-JMAX-3 the motive is a REAL obligation (the elim rule's 4th obligation), so — exactly as `natElim`'s succ
branch — the residue discharges from the obligation IHs with NO renaming-stability and NO free SN premise: fill the
two binders with CONCRETE reducible members and reflect SN along substitution.

  * the `b : A` binder is filled with the right endpoint's reducible member (`subst substitution rightEndpoint`,
    obligation #2);
  * the `p : Id A left b` binder (whose type substitutes to `Id A left right` by `subst_cons_idJMotiveSecondBinder\
    Type`) is filled with the witness's reducible member (`subst substitution witness`, obligation #1);
  * the motive obligation's fundamental conclusion at this doubly-filled environment yields a reducible member,
    hence a strongly-normalizing subject `subst (cons witness (cons rightEndpoint substitution)) motive`;
  * `subst_consSingleton_substLiftLift` factors that subject as
    `subst (cons witness (singleton rightEndpoint)) (subst (lift² substitution) motive)`, and
    `IsStronglyNormalizing.ofSubst` reflects its SN back to the open `subst (lift² substitution) motive`
    (= `subst (iterateLiftRaw substitution 2) motive`, the `liftEq` being `rfl`).

This is the JMAX-6 closure: the genuine motive obligation makes the old free SN premise derivable, so the elim row
no longer threads a lone `motiveStronglyNormalizing` arm — it matches the uniform `premisesFundamental`-only elim
shape (like `boolElim`). -/
theorem idJMotiveUnderTwoBindersStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {typeCode leftEndpoint rightEndpoint : RawTerm scope}
    {motive : RawTerm (scope + 2)} {witness : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      ((context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint)) motive
      (universeCodeCell levelExpr flag))
    (rightEndpointConclusion : FundamentalConclusionAtBoundedSucc env bound context rightEndpoint typeCode)
    (witnessConclusion : FundamentalConclusionAtBoundedSucc env bound context witness
      (idTypeCell typeCode leftEndpoint rightEndpoint))
    {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnvAtBounded env bound context substitution) :
    IsStronglyNormalizing (RawTerm.subst (iterateLiftRaw substitution 2) motive) := by
  have rightMember := rightEndpointConclusion substitution envReducible
  have witnessIdMember := witnessConclusion substitution envReducible
  have envWithEndpoint := ReducibleEnvAtBounded.cons envReducible rightMember
  have witnessSecondBinderMember :
      IsReducibleMemberAtBounded env bound
        (RawTerm.subst (RawTermSubst.cons (RawTerm.subst substitution rightEndpoint) substitution)
          (idJMotiveSecondBinderType typeCode leftEndpoint))
        (RawTerm.subst substitution witness) := by
    rw [subst_cons_idJMotiveSecondBinderType, ← subst_idTypeCell]
    exact witnessIdMember
  have envWithWitness := ReducibleEnvAtBounded.cons envWithEndpoint witnessSecondBinderMember
  have motiveUniverseMember := motiveConclusion
    (RawTermSubst.cons (RawTerm.subst substitution witness)
      (RawTermSubst.cons (RawTerm.subst substitution rightEndpoint) substitution))
    envWithWitness
  have subjectStronglyNormalizing := stronglyNormalizing_of_memberAtBoundedSucc motiveUniverseMember
  have liftEq : iterateLiftRaw substitution 2
      = RawTermSubst.lift (RawTermSubst.lift substitution) := rfl
  rw [liftEq]
  rw [← subst_consSingleton_substLiftLift motive (RawTerm.subst substitution witness)
      (RawTerm.subst substitution rightEndpoint) substitution] at subjectStronglyNormalizing
  exact IsStronglyNormalizing.ofSubst subjectStronglyNormalizing

/-- **★ The `+1`-closing GENUINE Paulin-Mohring `idJ` fundamental-theorem arm (table-independent engine).**
From the witness's `Id A left right` membership, the right endpoint's `A` membership, the base case's membership
at `C[left, refl left]`, and the motive's universe membership in the 2-extended context, `idJ motive baseCase
witness` satisfies the `+1`-closing fundamental conclusion at the DEPENDENT output `idJMotiveAt motive right
witness`.  Takes EXACTLY the four obligation IHs — NO free motive-SN premise (JMAX-6): the motive's under-2-binder
SN is discharged INTERNALLY from the motive obligation by `idJMotiveUnderTwoBindersStronglyNormalizing` (fill the
`b` / `p` binders with the right endpoint / witness members, reflect SN), exactly as `boolElim` discharges its
under-binder motive SN.  The output type is recovered by the two-binder motive recovery
(`idJGenuineOutputTypeReducibleAtBounded`); the based scrutinee supplies the endpoint conversions
(`isReflValueBetween_endpointConvOfReaches`, JMAX-3 A1) so the base case — typed at `C[left, refl left]` —
transfers to the output `C[right, witness]` along `convSubstPairArgs` (JMAX-2) when the witness reaches `refl`.
The genuine-J analogue of `fundamentalBoolElimAtBoundedSucc`; the JMAX-3 elim-FT row wires it from the rule's
obligation IHs. -/
theorem fundamentalIdJGenuineAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {typeCode leftEndpoint rightEndpoint : RawTerm scope}
    {motive : RawTerm (scope + 2)} {witness baseCase : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (witnessConclusion : FundamentalConclusionAtBoundedSucc env bound context witness
      (idTypeCell typeCode leftEndpoint rightEndpoint))
    (rightEndpointConclusion : FundamentalConclusionAtBoundedSucc env bound context rightEndpoint typeCode)
    (baseCaseConclusion : FundamentalConclusionAtBoundedSucc env bound context baseCase
      (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)))
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      ((context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint)) motive
      (universeCodeCell levelExpr flag)) :
    FundamentalConclusionAtBoundedSucc env bound context (idJCell motive baseCase witness)
      (idJMotiveAt motive rightEndpoint witness) := by
  intro _targetScope substitution envReducible
  have witnessIdMember := witnessConclusion substitution envReducible
  have rightMember := rightEndpointConclusion substitution envReducible
  have baseCaseMember := baseCaseConclusion substitution envReducible
  obtain ⟨outputCandidate, outputReducible⟩ :=
    idJGenuineOutputTypeReducibleAtBounded env bound context motiveConclusion substitution envReducible
      rightMember witnessIdMember
  have scrutineeBased := idMemberAtBounded_dataTaitCandidate witnessIdMember
  rw [termIndexedCodeValuePredicate_idCode] at scrutineeBased
  have scrutineeMember : dataTaitCandidate isReflValue (RawTerm.subst substitution witness) :=
    ⟨scrutineeBased.1, fun normalForm reaches normal =>
      (scrutineeBased.2 normalForm reaches normal).imp isReflValue_ofIsReflValueBetween id⟩
  rw [subst_idJCell]
  refine idJMemberAtBounded env bound outputReducible
    (idJMotiveUnderTwoBindersStronglyNormalizing env bound context motiveConclusion
      rightEndpointConclusion witnessConclusion substitution envReducible)
    (stronglyNormalizing_of_memberAtBoundedSucc baseCaseMember)
    scrutineeMember
    (fun reflWitness reaches => ?_)
  obtain ⟨convLeftReflWitness, convRightReflWitness⟩ :=
    isReflValueBetween_endpointConvOfReaches scrutineeBased reaches
  have transport :
      Conv (RawTerm.subst substitution (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)))
           (RawTerm.subst substitution (idJMotiveAt motive rightEndpoint witness)) := by
    rw [subst_idJMotiveAt_iterateLift, subst_idJMotiveAt_iterateLift, subst_reflCell]
    exact convSubstPairArgs (RawTerm.subst (iterateLiftRaw substitution 2) motive)
      ((Conv.gen_refl_cong convLeftReflWitness).trans (Conv.fromStepStar reaches).sym)
      (convLeftReflWitness.trans convRightReflWitness.sym)
  exact memberConvAtBounded env bound baseCaseMember ⟨outputCandidate, outputReducible⟩ transport

end FX1Poly.Typed
