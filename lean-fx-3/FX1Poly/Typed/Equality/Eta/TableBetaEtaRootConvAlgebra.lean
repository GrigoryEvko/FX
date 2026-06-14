import FX1Poly.Typed.Equality.Eta.TableBetaEtaRootConvDecidable

/-! # TableBetaEtaRootConvAlgebra — the relational algebra for the
TABLE-NATIVE union beta-eta conversion `ConvTableBetaEtaRoot`

The purely-additive relational laws that lift the canonical union
conversion `ConvTableBetaEtaRoot` (join form over
`StepTable ∪ StepEtaRootTable`, defined in
`TableBetaEtaRootConvDecidable`) into an equivalence on the
well-formed-typed fragment — the exact interface mirror of the bespoke
`BetaEtaConv` algebra (`refl` / `sym` / `transAtTypedMiddle`) that the
`DefEqUnitEta` judgmental-equality consumer currently uses.  This brick
unblocks migrating that consumer off the bespoke
`Step.betaEta`-based join onto the table-native union join.

Everything here is pure assembly over already-shipped legs:

* `refl` / `sym` are the join's structural identity and chain-swap —
  no metatheory needed (the common reduct is the term itself, or the
  two conjuncts are swapped);
* `transAtTypedMiddle` discharges the union peak at the SHARED middle
  term by the native typed Church-Rosser
  (`tableBetaEtaRootConfluenceTypedNative`, fed the `WfContextDescPi`
  via `WfContextDescPi.ofWfContextDesc`) — typing is load-bearing
  exactly at the peak, because RAW union beta-eta confluence is false;
  the two outer legs then compose by `unionStarTrans`.  This mirrors
  `BetaEtaConv.transAtTypedMiddle` premise-for-premise: same
  `WfContextDesc` well-formedness, same `HasTypeDescPi` middle typing;
* `eq_of_bothNormal` collapses both join legs out of two union-normal
  terms by `unionStarEqOfNormal` (rigidity) — the discrimination
  helper the consumers' negative witnesses rest on — and
  `not_of_bothNormal_ne` is its contrapositive convenience form: two
  distinct union-normal terms are never convertible.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConvAlgebra.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## Identity and symmetry — the structural join laws -/

/-- **Reflexivity** of the union conversion: the shared common reduct
is the term itself, reached by the reflexive `UnionStar` constructor on
both legs. -/
theorem ConvTableBetaEtaRoot.refl {scope : Nat} (term : RawTerm scope) :
    ConvTableBetaEtaRoot term term :=
  ⟨term, .refl _, .refl _⟩

/-- **Symmetry** of the union conversion: a shared common reduct of
`leftTerm` and `rightTerm` is, by swapping the two join legs, equally a
shared common reduct of `rightTerm` and `leftTerm`. -/
theorem ConvTableBetaEtaRoot.sym {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (conv : ConvTableBetaEtaRoot leftTerm rightTerm) :
    ConvTableBetaEtaRoot rightTerm leftTerm :=
  Exists.elim conv
    (fun commonReduct legs => ⟨commonReduct, legs.2, legs.1⟩)

/-! ## Transitivity through a well-typed middle — the typed-fragment leg -/

/-- **Transitivity of union conversion through a WELL-TYPED middle
term** — the typed-fragment equivalence leg, the table-native mirror of
`BetaEtaConv.transAtTypedMiddle`.  Each conversion supplies a union
chain OUT OF `middleTerm` (to its own common reduct); because
`middleTerm` is typed in a well-formed context, the native typed
Church-Rosser joins those two reducts at an apex.  Composing each
side's outer leg with the apex join via `unionStarTrans` exhibits the
apex as a shared common reduct of `leftTerm` and `rightTerm`.  Raw
union beta-eta confluence is FALSE, so — exactly as in the bespoke
algebra — typing is load-bearing precisely at this peak. -/
theorem ConvTableBetaEtaRoot.transAtTypedMiddle {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {middleTerm middleClassifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (middleTyped : HasTypeDescPi profile context middleTerm middleClassifier)
    {leftTerm rightTerm : RawTerm scope}
    (leftToMiddle : ConvTableBetaEtaRoot leftTerm middleTerm)
    (middleToRight : ConvTableBetaEtaRoot middleTerm rightTerm) :
    ConvTableBetaEtaRoot leftTerm rightTerm := by
  obtain ⟨leftCommon, leftToLeftCommon, middleToLeftCommon⟩ := leftToMiddle
  obtain ⟨rightCommon, middleToRightCommon, rightToRightCommon⟩ := middleToRight
  obtain ⟨apex, leftCommonToApex, rightCommonToApex⟩ :=
    HasTypeDescPi.tableBetaEtaRootConfluenceTypedNative
      (WfContextDescPi.ofWfContextDesc contextWellFormed) middleTyped
      middleToLeftCommon middleToRightCommon
  exact ⟨apex,
    unionStarTrans leftToLeftCommon leftCommonToApex,
    unionStarTrans rightToRightCommon rightCommonToApex⟩

/-! ## Native lifters — beta/iota conversion and root eta expansion -/

/-- A beta/iota `StepStar` chain lifts to a union star (each beta/iota
step becomes a LEFT union step via the forward table adequacy
`Step.toTableStep`).  The bridge used by `ofConv` to embed a bespoke
`Conv` join into the union conversion WITHOUT any typed metatheory —
beta/iota reduction is sound on the union by construction. -/
theorem stepStarToUnionStarLeft {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : StepStar sourceTerm targetTerm) :
    UnionStar (StepTable (scope := scope)) StepEtaRootTable sourceTerm
      targetTerm := by
  induction chain with
  | refl term => exact .refl term
  | trans firstStep _restChain restUnion =>
      exact UnionStar.headLeft firstStep.toTableStep restUnion

/-- **Beta/iota conversion embeds into the union conversion** — each
join leg lifts through `stepStarToUnionStarLeft`.  This is the
table-native replacement for `BetaEtaConv.ofConv` followed by the typed
backward bridge: a purely beta/iota `Conv` is already a union
conversion, needing NO typing (the typed bridge was only required to
carry the bespoke eta legs across). -/
theorem ConvTableBetaEtaRoot.ofConv {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (convertible : Conv leftTerm rightTerm) :
    ConvTableBetaEtaRoot leftTerm rightTerm := by
  obtain ⟨commonReduct, leftToCommon, rightToCommon⟩ := convertible
  exact ⟨commonReduct, stepStarToUnionStarLeft leftToCommon,
    stepStarToUnionStarLeft rightToCommon⟩

/-- **A term is union-convertible to its function-eta expansion** —
table-native.  The eta-long source `etaLamSource domainAnn term`
union-reduces in one ROOT eta step (`etaLamRow`, raw-tier) back to
`term`; the join apex is `term` itself.  This replaces the bespoke
`BetaEtaConv` eta join used by the readback's eta-expansion arm: no
`Step.eta` is ever built, the contraction fires natively off the
`etaRuleTable` row. -/
theorem ConvTableBetaEtaRoot.etaLamExpansion {scope : Nat}
    (domainAnn term : RawTerm scope) :
    ConvTableBetaEtaRoot term (RawTerm.etaLamSource domainAnn term) :=
  ⟨term, .refl term,
    .tailRight (.refl _)
      (StepEtaRootOverTable.etaRedex etaLamRow_memTable rfl ()
        (etaLamRow_contractsOnSource domainAnn term))⟩

/-! ## Union-normal discrimination — the negative-witness helpers -/

/-- **Two union-normal convertible terms are equal**.  Each join leg
runs out of a union-normal term, so `unionStarEqOfNormal` (rigidity)
collapses it: `leftTerm = commonReduct` and `rightTerm = commonReduct`,
hence `leftTerm = rightTerm`.  The discrimination kernel the consumers'
negative witnesses rest on. -/
theorem ConvTableBetaEtaRoot.eq_of_bothNormal {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (leftIsNormal : ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRoot leftTerm next)
    (rightIsNormal : ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRoot rightTerm next)
    (conv : ConvTableBetaEtaRoot leftTerm rightTerm) :
    leftTerm = rightTerm := by
  obtain ⟨commonReduct, leftToCommon, rightToCommon⟩ := conv
  exact (unionStarEqOfNormal leftIsNormal leftToCommon).trans
    (unionStarEqOfNormal rightIsNormal rightToCommon).symm

/-- **Distinct union-normal terms are never convertible** — the
contrapositive convenience form of `eq_of_bothNormal`, the exact shape
consumers use to build negative conversion witnesses. -/
theorem ConvTableBetaEtaRoot.not_of_bothNormal_ne {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (leftIsNormal : ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRoot leftTerm next)
    (rightIsNormal : ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRoot rightTerm next)
    (distinct : leftTerm ≠ rightTerm) :
    ¬ ConvTableBetaEtaRoot leftTerm rightTerm :=
  fun conv =>
    distinct (ConvTableBetaEtaRoot.eq_of_bothNormal leftIsNormal rightIsNormal conv)

end FX1Poly.Typed
