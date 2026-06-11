import FX1Poly.Typed.RecursiveElimUnionSpike

/-! # FX1Poly/Typed/RecursiveElimNativeUnion — NATIVE-32: the recursive-eliminator rows land IN the
    real union judgment (the NATIVE-27 GO verdict, integrated)

The NATIVE-27 spike (`RecursiveElimUnionSpike`) proved GO: the recursive eliminators `natElim` /
`natRec` ARE expressible as table rows over a union-style judgment whose scrutinee/base premises are
recursive in that judgment, with the succ-ι reduct typing INTERNALLY (no `reductTyped` escape hatch).
This file integrates that locked design into `HasTypeNativeUnion` proper — the two new arms
(`ofNatIntro`, `recursiveElim`) shipped in `HasTypeNativeUnion.lean`, restated here.

## What lands ON THE UNION

  * **`HasTypeDescNatElim.toNativeUnion` / `HasTypeDescNatRec.toNativeUnion`** — bespoke adequacy: every
    bespoke recursive-eliminator derivation maps into the union (the scrutinee through the NatIntro
    embedding arm, the base branch through the host embedding).  The NATIVE-33 fold's delete-safety
    direction, now into the SHIPPED union rather than the spike sibling.
  * **★ `recursiveElimSuccIotaDischargedInUnion`** — the GO TEST on the union: on the IH-return branch
    family, the succ-ι fires and the reduct types INTERNALLY through the union's own `recursiveElim`
    arm.  No `reductTyped` premise.  The NATIVE-04 residual, discharged inside the real judgment.
  * **★ `recursiveElimClosedComputationFullyTypedInUnion`** — the closed 2-step fully-typed computation
    chain (`natElim(Bool, true, var 0, succ zero) ↝ natElim(... zero) ↝ true`, every link union-typed).
  * **★ `RecursiveElimUnionSpike.toNativeUnion`** — the spike→union TRANSFER: every spike derivation
    maps to a `HasTypeNativeUnion` typing at the same subject/classifier (induction over the spike's 3
    arms; `ofUnion` embeds, `ofNatIntro` maps to the union embedding arm, `recursiveElimRow` maps to the
    union's `recursiveElim` arm via the table-inversion `recursiveElimRuleOf_cases` — the spike's row
    cells are DEFINITIONALLY the native rows' cells, so the arms coincide).

## Zero-axiom

Adequacy is a single-arm bespoke `cases` building the union arm; the GO theorems are direct
constructions + `Step.iotaNatElimSucc/Zero` with the contractum computing by `rfl`; the transfer is
`induction` over the spike's 3 arms with the table-inversion case lemma feeding the native arm at
definitionally-equal cells.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditNativeWaveRecursiveElim.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Bespoke adequacy: every bespoke recursive-eliminator derivation maps into the union -/

/-- **Bespoke natElim adequacy (into the union).**  Every `HasTypeDescNatElim` derivation translates to
a `HasTypeNativeUnion` typing at the same subject and classifier — the scrutinee through the NatIntro
embedding arm, the base branch through the host embedding.  The NATIVE-33 fold's delete-safety
direction, landing in the SHIPPED union. -/
theorem HasTypeDescNatElim.toNativeUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatElim profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  cases derivation with
  | natElimIntro motive scrutinee zeroBranch succBranch _resultTypeUnified
      scrutineeTyped zeroBranchTyped =>
      exact HasTypeNativeUnion.recursiveElim _ .gen_natElim natElimNativeRecursiveRule
        motive zeroBranch succBranch scrutinee classifier rfl
        (HasTypeNativeUnion.ofNatIntro scrutineeTyped)
        (HasTypeNativeUnion.ofGrown zeroBranchTyped)

/-- **Bespoke natRec adequacy (into the union)** — the recursor twin. -/
theorem HasTypeDescNatRec.toNativeUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatRec profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  cases derivation with
  | natRecIntro motive scrutinee zeroBranch succBranch _resultTypeUnified
      scrutineeTyped zeroBranchTyped =>
      exact HasTypeNativeUnion.recursiveElim _ .gen_natRec natRecNativeRecursiveRule
        motive zeroBranch succBranch scrutinee classifier rfl
        (HasTypeNativeUnion.ofNatIntro scrutineeTyped)
        (HasTypeNativeUnion.ofGrown zeroBranchTyped)

/-! ## ★ THE GO TEST ON THE UNION: the succ-ι reduct types internally -/

/-- **★★ THE GO THEOREM ON THE UNION (natElim): the succ-ι reduct types INTERNALLY.**  On the IH-return
branch family, for ANY union-typed predecessor and base branch: the succ-ι fires
(`Step.iotaNatElimSucc`, the contractum computing to the recursive call by `rfl`), and the reduct — the
recursive `natElimCell` at the predecessor — is typed by the UNION's own `recursiveElim` arm.  NO
`reductTyped` premise: the NATIVE-04 residual, discharged inside the real judgment. -/
theorem recursiveElimSuccIotaDischargedInUnion {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (predecessor zeroBranch resultType : RawTerm scope)
    (predecessorTyped : HasTypeNativeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeNativeUnion profile context zeroBranch resultType) :
    Step
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope)
        (natSuccCell predecessor))
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor) ∧
    HasTypeNativeUnion profile context
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor)
      resultType :=
  ⟨natElimSuccContractum_ihReturn motive zeroBranch predecessor ▸ Step.iotaNatElimSucc,
    HasTypeNativeUnion.recursiveElim context .gen_natElim natElimNativeRecursiveRule
      motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor resultType rfl
      predecessorTyped zeroBranchTyped⟩

/-- **★ The natRec twin of the GO theorem on the union.** -/
theorem recursiveRecSuccIotaDischargedInUnion {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (predecessor zeroBranch resultType : RawTerm scope)
    (predecessorTyped : HasTypeNativeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeNativeUnion profile context zeroBranch resultType) :
    Step
      (natRecCell motive zeroBranch (inductiveHypothesisReturnBranch scope)
        (natSuccCell predecessor))
      (natRecCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor) ∧
    HasTypeNativeUnion profile context
      (natRecCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor)
      resultType :=
  ⟨natRecSuccContractum_ihReturn motive zeroBranch predecessor ▸ Step.iotaNatRecSucc,
    HasTypeNativeUnion.recursiveElim context .gen_natRec natRecNativeRecursiveRule
      motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor resultType rfl
      predecessorTyped zeroBranchTyped⟩

/-! ## ★ End-to-end: a closed 2-step typed computation through the recursion loop, on the union -/

/-- **★ The closed eliminator computes through the recursion loop with every link union-typed.**
`natElim(Bool, true, var 0, succ zero) : Bool` (union-typed) ι-steps to
`natElim(Bool, true, var 0, zero) : Bool` (the recursive call, typed by the SAME union arm) ι-steps to
`true : Bool` (union-typed).  The full recursive computation chain inside the SHIPPED union. -/
theorem recursiveElimClosedComputationFullyTypedInUnion {profile : PolyProfile} :
    HasTypeNativeUnion profile (TypingContext.empty : TypingContext profile 0)
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
        (natSuccCell natZeroCell))
      boolTypeCell ∧
    Step
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
        (natSuccCell natZeroCell))
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0) natZeroCell) ∧
    HasTypeNativeUnion profile (TypingContext.empty : TypingContext profile 0)
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0) natZeroCell)
      boolTypeCell ∧
    Step
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0) natZeroCell)
      boolTrueCell ∧
    HasTypeNativeUnion profile (TypingContext.empty : TypingContext profile 0)
      boolTrueCell boolTypeCell := by
  have zeroScrutineeTyped : HasTypeNativeUnion profile
      (TypingContext.empty : TypingContext profile 0) natZeroCell natTypeCell :=
    HasTypeNativeUnion.ofNatIntro (HasTypeDescNatIntro.natZeroIntro TypingContext.empty)
  have trueBranchTyped : HasTypeNativeUnion profile
      (TypingContext.empty : TypingContext profile 0) boolTrueCell boolTypeCell :=
    HasTypeNativeUnion.ofDataIntro (HasTypeDescDataIntro.boolTrueTyped TypingContext.empty)
  refine ⟨?_, ?_, ?_, Step.iotaNatElimZero, trueBranchTyped⟩
  · exact HasTypeNativeUnion.recursiveElim TypingContext.empty .gen_natElim
      natElimNativeRecursiveRule boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
      (natSuccCell natZeroCell) boolTypeCell rfl
      (HasTypeNativeUnion.ofNatIntro
        (HasTypeDescNatIntro.natSuccIntro TypingContext.empty natZeroCell
          (HasTypeDescNatIntro.natZeroIntro TypingContext.empty)))
      trueBranchTyped
  · exact natElimSuccContractum_ihReturn boolTypeCell boolTrueCell natZeroCell ▸
      Step.iotaNatElimSucc
  · exact HasTypeNativeUnion.recursiveElim TypingContext.empty .gen_natElim
      natElimNativeRecursiveRule boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
      natZeroCell boolTypeCell rfl zeroScrutineeTyped trueBranchTyped

/-! ## ★ The spike→union transfer: every spike derivation maps into the real union -/

/-- **★ Every NATIVE-27 spike derivation maps to a `HasTypeNativeUnion` typing at the same subject and
classifier.**  Induction over the spike's 3 arms:

  * `ofUnion unionTyped` — the embedded union typing IS the witness.
  * `ofNatIntro natTyped` — the union's own `ofNatIntro` embedding arm.
  * `recursiveElimRow` — the spike's table hit `recursiveElimRuleOf generator = some rule` pins one of
    the two Nat rows (`recursiveElimRuleOf_cases`); the row's member cell and scrutinee type are
    DEFINITIONALLY the corresponding native row's, so the union's `recursiveElim` arm fires with the
    IH-translated scrutinee/base premises at the (defeq) native row.

The spike was the locked design surface for the union arm; this transfer certifies the integration is
faithful — the union admits everything the spike admitted. -/
theorem RecursiveElimUnionSpike.toNativeUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : RecursiveElimUnionSpike profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  induction derivation with
  | ofUnion unionTyped => exact unionTyped
  | ofNatIntro natTyped => exact HasTypeNativeUnion.ofNatIntro natTyped
  | recursiveElimRow generator rule motive baseBranch stepBranch scrutinee resultType
      isRecursiveElim _scrutineeTyped _baseBranchTyped scrutineeUnion baseBranchUnion =>
      rcases recursiveElimRuleOf_cases isRecursiveElim with
        ⟨_generatorEq, ruleEq⟩ | ⟨_generatorEq, ruleEq⟩
      · subst ruleEq
        exact HasTypeNativeUnion.recursiveElim _ .gen_natElim natElimNativeRecursiveRule
          motive baseBranch stepBranch scrutinee resultType rfl scrutineeUnion baseBranchUnion
      · subst ruleEq
        exact HasTypeNativeUnion.recursiveElim _ .gen_natRec natRecNativeRecursiveRule
          motive baseBranch stepBranch scrutinee resultType rfl scrutineeUnion baseBranchUnion

/-! ## The integration gate -/

/-- **The NATIVE-32 integration evidence record.**  Each field is a distinct live property of the
recursive-eliminator rows landed in the real union; an inhabitant certifies the integration: the
bespoke engines map in (premise parity, the fold's delete-safety), the succ-ι reduct types internally
on the recursion-isolating family (the NATIVE-04 residual discharge inside the union), the closed
recursive computation runs union-typed end-to-end, and the whole spike transfers. -/
structure RecursiveElimUnionResidencyEvidence (profile : PolyProfile) : Prop where
  /-- Every bespoke natElim derivation maps into the union. -/
  natElimAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescNatElim profile context subject classifier →
    HasTypeNativeUnion profile context subject classifier
  /-- Every bespoke natRec derivation maps into the union. -/
  natRecAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescNatRec profile context subject classifier →
    HasTypeNativeUnion profile context subject classifier
  /-- The succ-ι reduct types internally (no `reductTyped` premise) on the IH-return family. -/
  succIotaInternal : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (predecessor zeroBranch resultType : RawTerm scope),
    HasTypeNativeUnion profile context predecessor natTypeCell →
    HasTypeNativeUnion profile context zeroBranch resultType →
    Step
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope)
        (natSuccCell predecessor))
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor) ∧
    HasTypeNativeUnion profile context
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor)
      resultType
  /-- Every spike derivation transfers to the union. -/
  spikeTransfers : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    RecursiveElimUnionSpike profile context subject classifier →
    HasTypeNativeUnion profile context subject classifier

/-- **★ The NATIVE-32 integration gate** — inhabited by the shipped witnesses. -/
theorem recursiveElimUnionResidencyWitness {profile : PolyProfile} :
    RecursiveElimUnionResidencyEvidence profile where
  natElimAdequate := fun derivation => derivation.toNativeUnion
  natRecAdequate := fun derivation => derivation.toNativeUnion
  succIotaInternal := fun context motive predecessor zeroBranch resultType
    predecessorTyped zeroBranchTyped =>
    recursiveElimSuccIotaDischargedInUnion context motive predecessor zeroBranch resultType
      predecessorTyped zeroBranchTyped
  spikeTransfers := fun derivation => derivation.toNativeUnion

end FX1Poly.Typed
