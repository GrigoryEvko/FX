import FX1Poly.Core.EtaIotaCongRootAssembly
import FX1Poly.Typed.TableBetaEtaRootStrongNormalization
import FX1Poly.Typed.WfContextBetaEtaConfluenceUnconditional

/-! # FX1Poly/Typed/TableBetaEtaRootConfluence — ETA-T6 increment 7:
the table-generic typed beta-eta Church-Rosser (the Geuvers theorem
over table rows)

ON TYPED SUBJECTS the canonical table beta-eta-root union coincides
with the bespoke `Step.betaEta` relation in BOTH directions:

  * forward — a table iota step out of a typed subject IS a bespoke
    step (`tableStepToStep`; pathBeta is untypable in the fragment),
    and a raw-tier root contraction IS a bespoke eta
    (`stepEtaTableRootToBespokeEta`, no typing needed);
  * backward — a bespoke step embeds into the table
    (`Step.toStepTable`), and a bespoke eta on a TYPED subject is a
    raw-tier table contraction: the lam/pair/pathLam arms fire their
    rows' symbolic contraction equations, and the modal/Glue arms are
    REFUTED by untypability (`isUntypableHead_sound`) — exactly the
    gating the table fixes and typing enforces.

So the shipped unconditional Geuvers theorem transfers wholesale: any
two table-union reducts of a typed subject join by table-union stars.
Typing is threaded down both chains by the shipped subject reductions.
The full-congruence eta tier remains explicitly out of scope (the
eta-aware conversion / NbE seam); root-tier eta is the relation the
bespoke theorem governed, now quantified through the table rows.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConfluence.lean`. -/

namespace FX1Poly.Core

/-- Tail-append one step to a head-oriented beta-eta chain. -/
theorem Step.betaEtaStar.snoc {scope : Nat} :
    {first second third : RawTerm scope} →
    Step.betaEtaStar first second → Step.betaEta second third →
    Step.betaEtaStar first third
  | _, _, _, .refl _, lastStep => .trans lastStep (.refl _)
  | _, _, _, .trans firstStep rest, lastStep =>
      .trans firstStep (rest.snoc lastStep)

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core

/-- A bespoke eta step out of a TYPED subject is a raw-tier table root
contraction: the three faithfully-gated rows fire their symbolic
contraction equations; the modal/Glue arms are refuted by
untypability. -/
theorem HasTypeDescPi.bespokeEtaToTableRoot {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {source target classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context source classifier)
    (etaStep : Step.eta source target) :
    StepEtaRootTable source target := by
  cases etaStep with
  | etaLam domainAnn innerFunction =>
      exact .etaRedex etaLamRow_memTable rfl ()
        (etaLamRow_contractsOnSource _ _)
  | etaPair pairTerm =>
      exact .etaRedex etaPairRow_memTable rfl ()
        (etaPairRow_contractsOnSource _)
  | etaPathLam innerPath =>
      exact .etaRedex etaPathLamRow_memTable rfl ()
        (etaPathLamRow_contractsOnSource _)
  | etaModIntro modalTerm =>
      exact (isUntypableHead_sound rfl typed).elim
  | etaGlueIntro gluedTerm =>
      exact (isUntypableHead_sound rfl typed).elim

/-- **Forward star transfer**: a table-union chain out of a typed
subject is a bespoke beta-eta chain — typing recovered at every link
by the union star subject reduction. -/
theorem HasTypeDescPi.unionStarToBetaEtaStar {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (chain : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject reduct) :
    Step.betaEtaStar subject reduct := by
  induction chain with
  | refl => exact .refl _
  | tailLeft priorStar tableStep priorIH =>
      have typedAtMiddle :=
        HasTypeDescPi.subjectReductionTableBetaEtaRootStar wellFormed
          typed priorStar
      exact priorIH.snoc
        (Or.inl (HasTypeDescPi.tableStepToStep typedAtMiddle tableStep))
  | tailRight _priorStar rootStep priorIH =>
      refine priorIH.snoc (Or.inr ?_)
      cases rootStep with
      | etaRedex isRow isRawTier introPayload contracts =>
          exact stepEtaTableRootToBespokeEta isRow isRawTier
            introPayload contracts

/-- **Backward star transfer**: a bespoke beta-eta chain out of a
typed subject is a table-union chain — typing descends by the bespoke
beta-eta subject reduction. -/
theorem HasTypeDescPi.betaEtaStarToUnionStar {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (chain : Step.betaEtaStar subject reduct) :
    UnionStar (StepTable (scope := scope)) StepEtaRootTable subject
      reduct := by
  revert typed
  induction chain with
  | refl _term => intro _typed; exact .refl _
  | trans firstStep _rest chainIH =>
      intro typed
      have typedAtMiddle :=
        HasTypeDescPi.subjectReductionBetaEta wellFormed typed firstStep
      cases firstStep with
      | inl bespokeStep =>
          exact UnionStar.headLeft bespokeStep.toStepTable
            (chainIH typedAtMiddle)
      | inr etaStep =>
          exact UnionStar.headRight
            (HasTypeDescPi.bespokeEtaToTableRoot typed etaStep)
            (chainIH typedAtMiddle)

/-- ★★★ **The table-generic typed beta-eta Church-Rosser** (the
Geuvers theorem over table rows): any two table-union reducts of a
typed subject in a well-formed context join by table-union stars —
the unconditional bespoke theorem carried through the two-way typed
adequacy. -/
theorem HasTypeDescPi.tableBetaEtaRootConfluenceTyped
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (toLeft : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject leftReduct)
    (toRight : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject rightReduct) :
    ∃ commonReduct : RawTerm scope,
      UnionStar (StepTable (scope := scope)) StepEtaRootTable
        leftReduct commonReduct
      ∧ UnionStar (StepTable (scope := scope)) StepEtaRootTable
          rightReduct commonReduct := by
  have wellFormedPi := WfContextDescPi.ofWfContextDesc contextWellFormed
  obtain ⟨commonReduct, leftJoins, rightJoins⟩ :=
    HasTypeDescPi.subjectBetaEtaConfluenceTypedUnconditional
      contextWellFormed typed
      (HasTypeDescPi.unionStarToBetaEtaStar wellFormedPi typed toLeft)
      (HasTypeDescPi.unionStarToBetaEtaStar wellFormedPi typed toRight)
  exact ⟨commonReduct,
    HasTypeDescPi.betaEtaStarToUnionStar wellFormedPi
      (HasTypeDescPi.subjectReductionTableBetaEtaRootStar wellFormedPi
        typed toLeft)
      leftJoins,
    HasTypeDescPi.betaEtaStarToUnionStar wellFormedPi
      (HasTypeDescPi.subjectReductionTableBetaEtaRootStar wellFormedPi
        typed toRight)
      rightJoins⟩

/-- Union-star rigidity: a union chain out of a union-normal term is
trivial. -/
theorem unionStarEqOfNormal {scope : Nat}
    {startTerm endTerm : RawTerm scope}
    (isNormal : ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRoot startTerm next)
    (chain : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      startTerm endTerm) :
    startTerm = endTerm := by
  induction chain with
  | refl => rfl
  | tailLeft _priorStar tableStep priorIH =>
      exact absurd (Or.inl (priorIH ▸ tableStep) :
        StepTableBetaEtaRoot startTerm _) (isNormal _)
  | tailRight _priorStar rootStep priorIH =>
      exact absurd (Or.inr (priorIH ▸ rootStep) :
        StepTableBetaEtaRoot startTerm _) (isNormal _)

/-- ★★ **Unique table beta-eta-root normal forms on typed subjects**:
two union-normal reducts of a typed subject are equal — Church-Rosser
plus rigidity. -/
theorem HasTypeDescPi.tableBetaEtaRootUniqueNormalForm
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftNormalForm rightNormalForm : RawTerm scope}
    (toLeft : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject leftNormalForm)
    (leftIsNormal : ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRoot leftNormalForm next)
    (toRight : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject rightNormalForm)
    (rightIsNormal : ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRoot rightNormalForm next) :
    leftNormalForm = rightNormalForm := by
  obtain ⟨commonReduct, leftJoins, rightJoins⟩ :=
    HasTypeDescPi.tableBetaEtaRootConfluenceTyped contextWellFormed
      typed toLeft toRight
  exact (unionStarEqOfNormal leftIsNormal leftJoins).trans
    (unionStarEqOfNormal rightIsNormal rightJoins).symm

end FX1Poly.Typed
