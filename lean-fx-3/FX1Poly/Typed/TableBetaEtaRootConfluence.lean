import FX1Poly.Core.EtaIotaCongRootAssembly
import FX1Poly.Typed.TableBetaEtaRootStrongNormalization
import FX1Poly.Typed.TableBetaEtaRootChildJoinDispatch
import FX1Poly.Typed.WfContextDescPiFromWfContextDesc

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

/-- ★★★ **The table-generic typed beta-eta Church-Rosser** (the
Geuvers theorem over table rows): any two table-union reducts of a
typed subject in a well-formed context join by table-union stars.
Proved DIRECTLY through the native guarded-Newman route
(`tableBetaEtaRootConfluenceTypedNative`) — no bespoke `Step.betaEta`
round-trip; the `WfContextDesc` presupposition supplies the
`WfContextDescPi` the native headline consumes. -/
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
  exact HasTypeDescPi.tableBetaEtaRootConfluenceTypedNative
    (WfContextDescPi.ofWfContextDesc contextWellFormed) typed toLeft toRight

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
