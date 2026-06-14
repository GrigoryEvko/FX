import FX1Poly.Core.EtaIotaCongRootAssembly
import FX1Poly.Typed.TableBetaEtaRootStrongNormalization
import FX1Poly.Typed.TableBetaEtaRootChildJoinDispatch
import FX1Poly.Typed.WfContextDescPiFromWfContextDesc

/-! # FX1Poly/Typed/TableBetaEtaRootConfluence — ETA-T6 increment 7:
the table-generic typed beta-eta Church-Rosser (the Geuvers theorem
over table rows)

The table-generic typed beta-eta Church-Rosser holds DIRECTLY on the
canonical table beta-eta-root union via the native guarded-Newman route
(`tableBetaEtaRootConfluenceTypedNative`) — no bespoke `Step.betaEta`
round-trip: any two table-union reducts of a typed subject in a
well-formed context join by table-union stars.  Typing is threaded down
both chains by the shipped native subject reductions.  The
full-congruence eta tier remains explicitly out of scope (the eta-aware
conversion / NbE seam); root-tier eta is the relation the bespoke
theorem governed, now quantified through the table rows.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConfluence.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

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
