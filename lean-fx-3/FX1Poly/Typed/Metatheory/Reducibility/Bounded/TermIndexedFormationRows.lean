import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedFormationArityDispatch
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable
import FX1Poly.Typed.Engine.Formation.TermIndexedFormerStrongNormalization

/-! # FX1Poly/Typed/TermIndexedFormationRows
    — the term-indexed (Id / Bridge) formation FT members + rows over FREE levels (TYTAB-4 step 4)

The formation FT splits by family (`FormationRule`'s four constructors): base-type (pinned universe),
cumulative (binder-crossing Π/Σ + element List/Option), flat (the 5 data codes + 3 cohesion modalities), and
TERM-INDEXED — the identity former `Id A a b` (`gen_idCode`) and the bridge / internal-parametricity former
`Bridge A a b` (`gen_bridgeCode`), both arity-3 `[carrier, left, right]`.  This file discharges that last
sub-family.

## What distinguishes the term-indexed shape

A term-indexed former's obligation list is HETEROGENEOUS (unlike the flat / cumulative families, whose every
child is a universe member):

  * the HEAD child (the carrier) is typed at a universe code `Type@level` — a universe member, whose SN comes
    off `stronglyNormalizing_of_universeMemberAtBounded` (the carrier-level bound rides its candidate);
  * the TAIL children (the endpoints `a`, `b`) are typed at the CARRIER itself — ordinary members of an
    arbitrary type, whose SN comes off the bounded CR1 in member form
    (`stronglyNormalizing_of_memberAtBoundedSucc`): a member of any bound-reducible type is strongly
    normalizing.  This is exactly why the FT conclusion closes into the NON-EMPTY scope `targetScope + 1`
    (`FundamentalConclusionAtBoundedSucc`) — the bounded reducibility-candidate bundle reads CR1 there.

The output is the CARRIER's universe `Type@level` (the single carrier level, not the flat family's
`lmaxAll levels`), and the cell's reducibility-as-type is the `neutral` arm: a term-indexed former is NOT a
data code (`isFlatDataCode = false`) nor Π / universe / empty, so its only semantic content as a type is
strong normalization — the IDENTITY-COMPUTATION content (`Id_U ↝ Equiv`, the `idJ` / `idStrictRec` β rules)
is the SEPARATE iota layer, not this formation leg.

## The members + rows

`fundamental{Id,Bridge}FormationMemberAtBoundedSucc` are PER-FORMER (concrete `gen_idCode` / `gen_bridgeCode`),
so `RawTerm.subst` on the concrete `mkGen` head reduces by DEFINITIONAL reduction (the three shift-0 children
each take the bare substitution, no binder lift) — the substituted cell's SN matches
`termIndexedFormerCellStronglyNormalizingOfChildren` (the term-indexed SN driver) and its reducibility-as-type
is the `neutral` arm over the four table-generic root gates (`termIndexedFormationGenerator_noWeakHeadStep`,
root not Π / universe / empty by `decide`, `isFlatDataCode = false` by `rfl`).  The endpoint-type is left a
free parameter — the member only ever projects the endpoints' SN, never their classifier — so the row feeds
the carrier (the `FormationRule.obligations` arg) as that type without forcing carrier = head-child.

`fundamental{Id,Bridge}FormationRowAtBoundedSucc` match the arity-3 spine, read the three obligation IHs off
the `.termIndexed` obligation list (`carrier@Type@level`, `left@carrier`, `right@carrier` — the
`FormationRule_obligations_termIndexed_idCode` `rfl` shape) via `List.Mem.head` / `.tail`, and feed the
per-former member.  The fixed `{ outputType := termIndexedCarrierOutput }` rule is the only term-indexed rule
shape (`termIndexedFormerDescOf`), so the output `(.termIndexed _).outputType scope levels level flag` reduces
to `universeCodeCell level flag` by defeq.

## Zero-axiom verification

The members are `universeMembershipIntroAtBounded` fed the term-indexed SN driver + the `neutral`-arm
reducibility (`decide` / `rfl` gates) + the carrier universe-member SN + the endpoint bounded-CR1 SN; the rows
are `match` + `List.Mem` obligation extraction.  No induction (it lives in the support layer), no `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The identity-former (`Id A a b`) term-indexed formation FT member (TYTAB-4 step 4).**  From the carrier
obligation IH (a universe member at `level`) and the two endpoint obligation IHs (members of `endpointType`),
`Id carrierCode leftEndpoint rightEndpoint` is a bound-reducible member of `Type@level` under any closing
substitution.  The carrier's SN comes off the universe-member projection; the endpoints' SN off the bounded
CR1 in member form (which closes at `targetScope + 1`); the cell's SN off the term-indexed SN driver; its
reducibility-as-type is the `neutral` arm (`gen_idCode` is not a data / Π / universe / empty code), all riding
`subst`-defeq on the concrete `gen_idCode` head. -/
theorem fundamentalIdFormationMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {carrierCode leftEndpoint rightEndpoint : RawTerm scope} (endpointType : RawTerm scope)
    (level : LevelExpr) (flag : UniverseFlag)
    (carrierFundamental :
      FundamentalConclusionAtBoundedSucc env bound context carrierCode (universeCodeCell level flag))
    (leftFundamental :
      FundamentalConclusionAtBoundedSucc env bound context leftEndpoint endpointType)
    (rightFundamental :
      FundamentalConclusionAtBoundedSucc env bound context rightEndpoint endpointType) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_idCode ()
        (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil))))
      (universeCodeCell level flag) := by
  intro _targetScope substitution envReducible
  have carrierMember := carrierFundamental substitution envReducible
  rw [subst_universeCodeCell] at carrierMember
  have carrierBelowBound : LevelExpr.denote level env < bound := by
    obtain ⟨_, candidateReducible, _⟩ := carrierMember
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have carrierSN : IsStronglyNormalizing (RawTerm.subst substitution carrierCode) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound level flag _ carrierBelowBound carrierMember
  have leftSN : IsStronglyNormalizing (RawTerm.subst substitution leftEndpoint) :=
    stronglyNormalizing_of_memberAtBoundedSucc (leftFundamental substitution envReducible)
  have rightSN : IsStronglyNormalizing (RawTerm.subst substitution rightEndpoint) :=
    stronglyNormalizing_of_memberAtBoundedSucc (rightFundamental substitution envReducible)
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env level flag bound
    (.mkGen .gen_idCode ()
      (.childCons (RawTerm.subst substitution carrierCode)
        (.childCons (RawTerm.subst substitution leftEndpoint)
          (.childCons (RawTerm.subst substitution rightEndpoint) .childNil))))
    carrierBelowBound
    (termIndexedFormerCellStronglyNormalizingOfChildren termIndexedFormerDescOf_idCode
      ⟨carrierSN, leftSN, rightSN, True.intro⟩)
    -- DEP-ID: `idTypeCell` is TERM-INDEXED-reducible — the dedicated `dataTermIndexed` arm pins it to the
    -- two-endpoint based-refl candidate `termIndexedCodeValuePredicate gen_idCode left right`
    -- (`isReflValueBetween left right`), the genuine path-induction prerequisite, carved out of the flat
    -- `dataFlat` arm by the `isTermIndexedCode` gate (`gen_idCode.isTermIndexedCode = true`).  Sound because
    -- `gen_idCode` admits no bespoke `WeakHeadStep` (every `IotaHeadStep` is eliminator-rooted; the
    -- def-univalence `Id_U ↝ equivCode` lives in the orthogonal IotaRuleTable, not in `WeakHeadStep`).
    ⟨_, ReducibleTypeStepBounded.dataTermIndexed⟩

/-- **The bridge-former (`Bridge A a b`, internal parametricity) term-indexed formation FT member (TYTAB-4
step 4).**  The `gen_bridgeCode` twin of `fundamentalIdFormationMemberAtBoundedSucc` (same carrier-plus-
endpoints shape, same carrier-level output). -/
theorem fundamentalBridgeFormationMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {carrierCode leftEndpoint rightEndpoint : RawTerm scope} (endpointType : RawTerm scope)
    (level : LevelExpr) (flag : UniverseFlag)
    (carrierFundamental :
      FundamentalConclusionAtBoundedSucc env bound context carrierCode (universeCodeCell level flag))
    (leftFundamental :
      FundamentalConclusionAtBoundedSucc env bound context leftEndpoint endpointType)
    (rightFundamental :
      FundamentalConclusionAtBoundedSucc env bound context rightEndpoint endpointType) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_bridgeCode ()
        (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil))))
      (universeCodeCell level flag) := by
  intro _targetScope substitution envReducible
  have carrierMember := carrierFundamental substitution envReducible
  rw [subst_universeCodeCell] at carrierMember
  have carrierBelowBound : LevelExpr.denote level env < bound := by
    obtain ⟨_, candidateReducible, _⟩ := carrierMember
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have carrierSN : IsStronglyNormalizing (RawTerm.subst substitution carrierCode) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound level flag _ carrierBelowBound carrierMember
  have leftSN : IsStronglyNormalizing (RawTerm.subst substitution leftEndpoint) :=
    stronglyNormalizing_of_memberAtBoundedSucc (leftFundamental substitution envReducible)
  have rightSN : IsStronglyNormalizing (RawTerm.subst substitution rightEndpoint) :=
    stronglyNormalizing_of_memberAtBoundedSucc (rightFundamental substitution envReducible)
  rw [subst_universeCodeCell]
  obtain ⟨carrierCandidate, carrierTypeReducible⟩ :=
    universeMemberReducibleAsTypeAtDecodedLevelBounded carrierMember carrierBelowBound
  exact universeMembershipIntroAtBounded env level flag bound
    (.mkGen .gen_bridgeCode ()
      (.childCons (RawTerm.subst substitution carrierCode)
        (.childCons (RawTerm.subst substitution leftEndpoint)
          (.childCons (RawTerm.subst substitution rightEndpoint) .childNil))))
    carrierBelowBound
    (termIndexedFormerCellStronglyNormalizingOfChildren termIndexedFormerDescOf_bridgeCode
      ⟨carrierSN, leftSN, rightSN, True.intro⟩)
    ⟨bridgeReducibleCandidate IsStronglyNormalizing carrierCandidate,
      ReducibleTypeStepBounded.dataBridgeCarrierAware carrierTypeReducible⟩

/-- **The identity-former term-indexed formation FT row (TYTAB-4 step 4).**  `mkGen gen_idCode payload children`
is a bound-reducible member of the term-indexed output universe; the arity-3 spine collapses to
`[carrier, left, right]` and the `.termIndexed` obligation list (`carrier@Type@level`, `left@carrier`,
`right@carrier`) feeds the Id member.  The carrier of the endpoint obligations (the `obligations` `carrier`
arg) is passed as the member's endpoint-type — the member needs only the endpoints' SN. -/
theorem fundamentalIdFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_idCode.payload scope}
    {children : RawTermChildren Generator.gen_idCode.binderShifts scope}
    {levels : List LevelExpr} {carrier : RawTerm scope} {level : LevelExpr} {flag : UniverseFlag}
    (obligationsFundamental : ∀ obligation,
        obligation ∈ (FormationRule.termIndexed { outputType := termIndexedCarrierOutput }).obligations
          profile context children levels carrier level flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_idCode payload children)
      ((FormationRule.termIndexed { outputType := termIndexedCarrierOutput }).outputType
        scope levels level flag) := by
  match children with
  | .childCons carrierChild (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
    intro _targetScope substitution envReducible
    have carrierIH :
        FundamentalConclusionAtBoundedSucc env bound context carrierChild
          (universeCodeCell level flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := carrierChild,
          classifier := universeCodeCell level flag } (List.Mem.head _)
    have leftIH :
        FundamentalConclusionAtBoundedSucc env bound context leftEndpoint carrier :=
      obligationsFundamental
        { scope := scope, context := context, subject := leftEndpoint, classifier := carrier }
        (List.Mem.tail _ (List.Mem.head _))
    have rightIH :
        FundamentalConclusionAtBoundedSucc env bound context rightEndpoint carrier :=
      obligationsFundamental
        { scope := scope, context := context, subject := rightEndpoint, classifier := carrier }
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    exact fundamentalIdFormationMemberAtBoundedSucc env bound context carrier level flag
      carrierIH leftIH rightIH substitution envReducible

/-- **The bridge-former term-indexed formation FT row.**  The `gen_bridgeCode` twin of
`fundamentalIdFormationRowAtBoundedSucc`. -/
theorem fundamentalBridgeFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_bridgeCode.payload scope}
    {children : RawTermChildren Generator.gen_bridgeCode.binderShifts scope}
    {levels : List LevelExpr} {carrier : RawTerm scope} {level : LevelExpr} {flag : UniverseFlag}
    (obligationsFundamental : ∀ obligation,
        obligation ∈ (FormationRule.termIndexed { outputType := termIndexedCarrierOutput }).obligations
          profile context children levels carrier level flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_bridgeCode payload children)
      ((FormationRule.termIndexed { outputType := termIndexedCarrierOutput }).outputType
        scope levels level flag) := by
  match children with
  | .childCons carrierChild (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
    intro _targetScope substitution envReducible
    have carrierIH :
        FundamentalConclusionAtBoundedSucc env bound context carrierChild
          (universeCodeCell level flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := carrierChild,
          classifier := universeCodeCell level flag } (List.Mem.head _)
    have leftIH :
        FundamentalConclusionAtBoundedSucc env bound context leftEndpoint carrier :=
      obligationsFundamental
        { scope := scope, context := context, subject := leftEndpoint, classifier := carrier }
        (List.Mem.tail _ (List.Mem.head _))
    have rightIH :
        FundamentalConclusionAtBoundedSucc env bound context rightEndpoint carrier :=
      obligationsFundamental
        { scope := scope, context := context, subject := rightEndpoint, classifier := carrier }
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    exact fundamentalBridgeFormationMemberAtBoundedSucc env bound context carrier level flag
      carrierIH leftIH rightIH substitution envReducible

/-- **The term-indexed formation FT family arm (TYTAB-4 step 4).**  A generator carrying a term-indexed table
row (`termIndexedFormerDescOf generator = some termRule`) makes `mkGen generator payload children` a
bound-reducible member of the rule's output universe under any closing substitution, given the carrier /
endpoint obligation IHs.  Dispatches the two term-indexed formers (`gen_bridgeCode` / `gen_idCode`, the table
order) to their per-former rows; a non-term-indexed generator is impossible
(`termIndexedFormerDescOf … = none`).  The term-indexed sub-family of the native `formationFundamental`
premise — the analogue of `fundamentalBaseTypeRowAtBoundedSucc` (base-type family) for the carrier-plus-
endpoints family.  The `.termIndexed` arm of the eventual `cases FormationRule` assembly. -/
theorem fundamentalTermIndexedFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {termRule : TermIndexedFormerDesc} {levels : List LevelExpr} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (isTermIndexed : termIndexedFormerDescOf generator = some termRule)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ (FormationRule.termIndexed termRule).obligations
          profile context children levels carrier level flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (RawTerm.mkGen generator payload children)
      ((FormationRule.termIndexed termRule).outputType scope levels level flag) := by
  by_cases isBridge : generator = .gen_bridgeCode
  · subst isBridge
    obtain rfl : termRule = { outputType := termIndexedCarrierOutput } :=
      Option.some.inj (isTermIndexed.symm.trans termIndexedFormerDescOf_bridgeCode)
    exact fundamentalBridgeFormationRowAtBoundedSucc env bound context obligationsFundamental
  · by_cases isId : generator = .gen_idCode
    · subst isId
      obtain rfl : termRule = { outputType := termIndexedCarrierOutput } :=
        Option.some.inj (isTermIndexed.symm.trans termIndexedFormerDescOf_idCode)
      exact fundamentalIdFormationRowAtBoundedSucc env bound context obligationsFundamental
    · exfalso
      dsimp only [termIndexedFormerDescOf] at isTermIndexed
      rw [if_neg isBridge, if_neg isId] at isTermIndexed
      contradiction

end FX1Poly.Typed
