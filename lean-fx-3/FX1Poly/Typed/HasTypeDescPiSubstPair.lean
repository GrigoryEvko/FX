import FX1Poly.Core.RawTermSubstConsCommute
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.NatElimFaithfulMul
import FX1Poly.Core.IotaHeadStep

/-! # FX1Poly/Typed/HasTypeDescPiSubstPair — the typed 2-VARIABLE substitution lemma
    (the substPair lemma the Phase-Z natElim/natRec migration flagged) + the mul-faithfulness discharge

The Phase-Z SUBSTITUTING succ-iota produces `succBranch[var 0 := recursiveCall, var 1 := predecessor]`
— a SIMULTANEOUS 2-variable substitution `RawTermSubst.cons recursiveCall (RawTermSubst.singleton
predecessor)` into the two-binder branch.  Three theorems shipped CONDITIONAL on the missing typed
2-variable substitution lemma; this file ships the lemma and discharges what it honestly can.

## What this ships

  * **`HasTypeDescPi.substPairUnderTwoBindings` (★)** — the GENERAL dependent 2-variable typed
    substitution: a grown derivation under two binders, an inner substituent typed at the
    outer-substituted inner binder type, and an outer substituent typed at the outer binder type give
    the substituted subject typed at the substituted classifier.  An instantiation of the shipped
    `substRespectingContext` at `cons innerArg (singleton outerArg)`; the pointwise side condition
    splits `Fin` 0 / 1 / k+2 and discharges by the two weakening-cancellation laws
    (`RawTerm.weaken_subst_cons` for the head drop, `subst_singleton_renameWeaken_cancel` for the
    tail drop) plus the var rule.
  * **`HasTypeDescPi.substPairNonDependent`** — the recursor-step-shaped corollary: a branch typed at
    a twice-weakened result type under two binders, substituted at typed arguments, is typed at the
    result type ON THE NOSE.  This is the shape of every Phase-Z recursive-eliminator succ branch
    (natElim/natRec with outer binder Nat; the idJ/idStrictRec shift-2 children are the same skeleton).
  * **`mulNatBranch_substituted`** — the raw 2-variable subst COMPUTES through `mulNatBranch`:
    motive/zero-accumulator/copy-branch children resolve by the cons/singleton/lift var-equations
    (definitionally), the embedded closed `natNumeralAt m` is fixed by `natNumeralAt_subst`.
  * **`mulStepReduces_proved`** — `IotaHeadStep.iotaNatElimSucc.toStep` rewritten by `mulNatBranch_substituted`
    discharges the `mulStepReduces` premise of `natElimMulFaithful` IN FULL.
  * **`natElimMulFaithful.unconditional` (★)** — native `gen_natElim` computes host `Nat.mul`
    UNCONDITIONALLY: `natElim(_, natZero, mulBranch m, rawNat n) ↝* rawNat (m * n)` for ALL `m n`,
    no premises.  Closes the HON-13 conditional flag.  Plus the `threeTimesTwoUnconditional` smoke.

## What remains conditional, honestly

`natElimSuccIotaComputesTyped`'s `reductTyped` premise asks for the iota-instance reduct typing, whose
inner substituent is the recursive `natElimCell` itself — and the grown engine deliberately does NOT
type `natElimCell` heads (`HasTypeDescPi.natElimCellUntypedViaDecision`), so
`substPairNonDependent` cannot fire at that instance within `HasTypeDescPi` alone.  The unconditional
discharge needs a UNION judgment closed under both the standalone eliminator intro and the grown rules,
with `substRespectingContext` re-proved over the union — the #832/#1138 table-residency follow-on.
Likewise `natElimComputesToNumeral`'s `substitutedReductProduces` stays an honest premise for ABSTRACT
branches (its concrete copy-branch instances were already discharged).  The substPair lemma is the
genuinely reusable new substrate: it is judgment-shape-generic and seeds the idJ/idStrictRec
(shift-2) migration.

## Zero-axiom verification

`substPairUnderTwoBindings` is `substRespectingContext` + `Fin` case-splitting + two rewrite laws;
the discharge chain is `IotaHeadStep.iotaNatElimSucc.toStep` + `rfl`-computing child substitution +
`natNumeralAt_subst`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTypedCellShapeSubstrate.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **★ The typed 2-variable substitution lemma** (the Phase-Z substPair lemma).  A grown derivation
under two binders — outer binder `outerType`, inner binder `innerType` (which may mention the outer
variable) — substituted simultaneously at `var 0 := innerArg, var 1 := outerArg` preserves
`HasTypeDescPi`, with subject and classifier substituted.  The inner substituent is typed at the
OUTER-SUBSTITUTED inner binder type (the dependency collapses once the outer variable is filled). -/
theorem HasTypeDescPi.substPairUnderTwoBindings {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {outerType : RawTerm scope}
    {innerType : RawTerm (scope + 1)} {subject classifier : RawTerm (scope + 2)}
    (innerArg outerArg : RawTerm scope)
    (derivation :
      HasTypeDescPi profile ((context.cons outerType).cons innerType) subject classifier)
    (innerArgTyped : HasTypeDescPi profile context innerArg
      (RawTerm.subst (RawTermSubst.singleton outerArg) innerType))
    (outerArgTyped : HasTypeDescPi profile context outerArg outerType) :
    HasTypeDescPi profile context
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) subject)
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) classifier) := by
  refine derivation.substRespectingContext context
    (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) ?_
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeDescPi profile context innerArg
        (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
          (RawTerm.rename RawRenaming.weaken innerType))
      rw [RawTerm.weaken_subst_cons]
      exact innerArgTyped
  | succ tailValue =>
      cases tailValue with
      | zero =>
          show HasTypeDescPi profile context outerArg
            (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
              (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken outerType)))
          rw [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel]
          exact outerArgTyped
      | succ priorValue =>
          show HasTypeDescPi profile context
            (variableCell ⟨priorValue,
              Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩)
            (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
              (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken
                (context.lookup ⟨priorValue,
                  Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩))))
          rw [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel]
          exact HasTypeDescPi.ofFormation
            (HasTypeDesc.var context ⟨priorValue,
              Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩)

/-- **The recursor-step-shaped substPair corollary.**  A branch typed at a TWICE-WEAKENED result type
under two binders (the Phase-Z succ-branch shape: inner binder = the once-weakened result type carrying
the recursive result, outer binder = the scrutinee's element type), substituted at a typed recursive
result and a typed outer argument, is typed at the result type on the nose — both weakenings cancel
against the two substituents. -/
theorem HasTypeDescPi.substPairNonDependent {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {outerType resultType : RawTerm scope}
    {branch : RawTerm (scope + 2)}
    (innerArg outerArg : RawTerm scope)
    (branchTyped : HasTypeDescPi profile
      ((context.cons outerType).cons (RawTerm.rename RawRenaming.weaken resultType))
      branch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (innerArgTyped : HasTypeDescPi profile context innerArg resultType)
    (outerArgTyped : HasTypeDescPi profile context outerArg outerType) :
    HasTypeDescPi profile context
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) branch)
      resultType := by
  have innerAtSubstituted : HasTypeDescPi profile context innerArg
      (RawTerm.subst (RawTermSubst.singleton outerArg)
        (RawTerm.rename RawRenaming.weaken resultType)) := by
    rw [subst_singleton_renameWeaken_cancel]
    exact innerArgTyped
  have substituted :=
    HasTypeDescPi.substPairUnderTwoBindings innerArg outerArg branchTyped
      innerAtSubstituted outerArgTyped
  rwa [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel] at substituted

/-- **The 2-variable substitution COMPUTES through the multiplication branch.**  The motive, the
accumulator zero-branch (`var 0` — the slot the recursive result fills), and the inner copy branch all
resolve by the cons/singleton/lift variable equations (definitionally); the embedded closed scrutinee
`natNumeralAt m` is fixed by `natNumeralAt_subst`.  The substituted branch IS the inner adder. -/
theorem mulNatBranch_substituted (m : Nat) (recursiveCall predecessor : RawTerm 0) :
    RawTerm.subst (RawTermSubst.cons recursiveCall (RawTermSubst.singleton predecessor))
        (mulNatBranch m)
      = mulBranchSubstitutedTarget m recursiveCall := by
  show natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) recursiveCall copyNatBranchAt
      (RawTerm.subst (RawTermSubst.cons recursiveCall (RawTermSubst.singleton predecessor))
        (natNumeralAt m))
    = mulBranchSubstitutedTarget m recursiveCall
  rw [natNumeralAt_subst]
  rfl

/-- **The `mulStepReduces` premise, DISCHARGED.**  The Phase-Z succ-iota fires
(`IotaHeadStep.iotaNatElimSucc.toStep`) and its substituted reduct is rewritten to the inner adder by
`mulNatBranch_substituted` — exactly the per-step reduction `natElimMulFaithful` consumes. -/
theorem mulStepReduces_proved (m n : Nat) :
    StepStar (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell
        (mulNatBranch m) (natNumeralAt (n + 1)))
      (mulBranchSubstitutedTarget m
        (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell (mulNatBranch m)
          (natNumeralAt n))) := by
  have iotaStep := (IotaHeadStep.iotaNatElimSucc (scope := 0)
    (motive := variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1))
    (predecessor := natNumeralAt n)
    (zeroBranch := natZeroCell)
    (succBranch := mulNatBranch m)).toStep
  rw [mulNatBranch_substituted] at iotaStep
  exact StepStar.single iotaStep

/-- **★ UNCONDITIONAL: the native `gen_natElim` recursor computes host `Nat.mul`.**
`natElim(_, natZero, mulBranch m, rawNat n) ↝* rawNat (m * n)` for ALL `m n : Nat`, no premises —
the `mulStepReduces` conditional of `natElimMulFaithful` discharged by `mulStepReduces_proved`.
Closes the HON-13 conditional flag: recursor faithfulness for multiplication now stands on the same
unconditional footing as `natElimAddFaithful` (addition). -/
theorem natElimMulFaithful.unconditional (m n : Nat) :
    StepStar (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell
        (mulNatBranch m) (natNumeralAt n))
      (natNumeralAt (m * n)) :=
  natElimMulFaithful m (fun stepIndex => mulStepReduces_proved m stepIndex) n

/-- Fully-concrete unconditional smoke: `natElim(_, natZero, mulBranch 3, 2) ↝* 6`. -/
theorem natElimMulFaithful.threeTimesTwoUnconditional :
    StepStar (natElimCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) natZeroCell
        (mulNatBranch 3) (natNumeralAt 2))
      (natNumeralAt 6) :=
  natElimMulFaithful.unconditional 3 2

end FX1Poly.Typed
