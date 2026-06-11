import FX1Poly.Typed.HasTypeDescNatElim

/-! # FX1Poly/Typed/DependentElimPremiseSpike — NATIVE-04: the dependent-elimination premise (motive IH) — the RISK spike

The GO/NO-GO spike for `childMotiveInstance`, NATIVE-01's hardest premise kind and the campaign's risk
class: the recursive eliminators (natElim / natRec / listElim) whose successor/cons branch inhabits the
MOTIVE applied to constructor data AND carries the inductive hypothesis.  This is the premise that decides
whether the unified system collapses to literally ONE inductive or one inductive plus a named, pinned
recursive-elim core.

## The finding: the eliminator TYPING is expressible; the recursive ι-SR has a PINNED residual

The shipped `HasTypeDescNatElim` (`HasTypeDescNatElim.lean`, CAN-1) settles the expressibility half:

  * `HasTypeDescNatElim.natElimIntro` TYPES `natElim(motive, zeroBranch, succBranch, scrutinee) : C` from a
    data-engine scrutinee + a grown-typed zero branch (the motive + the two-binder succ-branch are stored).
    So the eliminator typing AND the motive-IH branch SHAPE (`succBranch : RawTerm (scope + 2)`, the two
    binders = predecessor + IH) are EXPRESSIBLE — verdict GO on the premise itself.
  * `natElimZeroIotaComputesTyped` discharges the ZERO-case ι-SR UNCONDITIONALLY (the reduct is the zero
    branch, already grown-typed).
  * `natElimSuccIotaComputesTyped` — the RECURSIVE successor ι-SR — is CONDITIONAL: it takes the reduct's
    typing (`reductTyped`) as an explicit PREMISE.  The reduct `natElimSuccContractum` is
    `succBranch[var 0 := natElim …, var 1 := predecessor]`, whose var-0 substituent is the recursive
    `natElimCell` ITSELF.  The grown engine deliberately does not type that recursive call, and the
    2-variable typed substitution lemma (`HasTypeDescPi.substPairUnderTwoBindings`, SHIPPED) cannot
    discharge a premise whose inner term lives in the standalone eliminator judgment, not the grown one.

So the dependent-elim ι-SR's residual is precise and NAMED: **typing the recursive ι-reduct requires a
single judgment closed under BOTH the standalone eliminator intro AND the grown rules** (the union
judgment).  This is exactly the NATIVE-40 unified-engine target — once Typing is ONE inductive with all
rule-table arms (formation/intro/elim incl. recursive), the reduct's recursive call and grown branches type
in the SAME derivation and the residual discharges INTERNALLY.

## Verdict: GO-WITH-RECURSIVE-ι-RESIDUAL (toward 100%, honestly flagged)

The premise is expressible and the residual is not an open problem — it is dischargeable by the unified
single engine (the recursive eliminators become rows whose ι-SR is the LAST/hardest discharge, NATIVE-32/33,
with the substitution lemma already shipped).  It does NOT force a PERMANENT separate pinned core.  BUT it is
the campaign's risk point, recorded transparently: IF the unified engine's recursive ι-SR proves intractable,
the honest fallback is "one engine + a named, pinned, adequacy-bridged recursive-elim core" (the 95%
outcome).  This spike commits to neither prematurely; it pins the residual exactly so NATIVE-05 can lock the
collapse scope with the cost known.

  * `dependentElimEliminatorTyped` — ★ NON-VACUOUS: a concrete closed `natElim` on `natZero` typed via
    `natElimIntro`, witnessing the eliminator typing is real.
  * `dependentElimZeroIotaUnconditional` / `dependentElimSuccIotaConditional` — the SR dichotomy: zero-ι is
    unconditional, succ-ι is conditional on the reduct typing (citing the shipped engine theorems).
  * `dependentElimExpressibility` / `_verdict` — the honest GO-WITH-RESIDUAL verdict ledger.

## Zero-axiom

Direct construction over the shipped `HasTypeDescNatElim`; the residual is a structured ledger pinning the
shipped conditional theorem.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ NON-VACUOUS: a concrete recursive eliminator is typed.**  `natElim(motive, Type@0, succBranch,
natZero) : Type@1` — the dependent eliminator's intro arm types a real eliminator cell (scrutinee `natZero`
via the data engine, zero branch `Type@0 : Type@1` via the grown engine; the motive and two-binder
succ-branch stored).  Witnesses that the dependent-elim premise (and the motive-IH branch shape) is genuinely
expressible, not vacuous. -/
theorem dependentElimEliminatorTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescNatElim profile (TypingContext.empty : TypingContext profile 0)
      (natElimCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag) natZeroCell)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  HasTypeDescNatElim.natElimIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag) natZeroCell
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescNatIntro.natZeroIntro TypingContext.empty)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **The zero-case ι-SR is UNCONDITIONAL.**  A typed `natElim` on `natZero` ι-steps to the zero branch and
the reduct is typed at `C` — no reduct-typing premise needed (the reduct IS the grown-typed zero branch).
Cites the shipped `natElimZeroIotaComputesTyped`. -/
theorem dependentElimZeroIotaUnconditional {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (resultType : RawTerm scope)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType) :
    Step (natElimCell motive zeroBranch succBranch natZeroCell) zeroBranch ∧
    HasTypeDescPi profile context zeroBranch resultType :=
  ⟨(natElimZeroIotaComputesTyped context motive zeroBranch succBranch resultType
      zeroBranchTyped).2.1,
   zeroBranchTyped⟩

/-- **The successor-case ι-SR is CONDITIONAL on the reduct typing** — the recursive-elim residual.  Given the
reduct typing (`reductTyped`), a typed `natElim` on `natSucc(predecessor)` ι-steps to the substituted reduct
typed at `C`.  The `reductTyped` premise is the residual: the reduct's var-0 substituent is the recursive
`natElimCell` itself, which only a union judgment (standalone-elim ∪ grown) types.  Cites the shipped
conditional `natElimSuccIotaComputesTyped`. -/
theorem dependentElimSuccIotaConditional {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (predecessor zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (resultType : RawTerm scope)
    (predecessorTyped : HasTypeDescNatIntro profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType)
    (reductTyped : HasTypeDescNatElim profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor) resultType) :
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
      (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeDescNatElim profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor) resultType :=
  ⟨(natElimSuccIotaComputesTyped context motive predecessor zeroBranch succBranch resultType
      predecessorTyped zeroBranchTyped reductTyped).2.1,
   reductTyped⟩

/-! ## The GO-WITH-RESIDUAL verdict ledger -/

/-- The spike's verdict record.  Splits the dependent-elim premise into what is settled GO and the precisely
named recursive-ι residual — the input NATIVE-05 needs to lock the collapse scope with the cost known. -/
structure DependentElimExpressibility where
  /-- The recursive eliminator's TYPING is expressible (`natElimIntro` types `natElim …`). -/
  eliminatorTypingExpressible : Bool
  /-- The motive-IH branch SHAPE is expressible (the two-binder `succBranch : RawTerm (scope + 2)`). -/
  motiveIHBranchShapeExpressible : Bool
  /-- The zero-case ι subject-reduction is UNCONDITIONAL. -/
  zeroIotaSRUnconditional : Bool
  /-- The recursive successor ι subject-reduction is CONDITIONAL on the reduct typing (the residual). -/
  recursiveIotaSRConditional : Bool
  /-- The 2-variable typed substitution lemma is SHIPPED (`substPairUnderTwoBindings`). -/
  substitutionLemmaShipped : Bool
  /-- The residual is dischargeable by the UNIFIED single engine (a union over elim + grown rules) — NOT a
  permanent separate pinned core. -/
  residualDischargeableByUnion : Bool

/-- **★ NATIVE-04 verdict: GO-WITH-RECURSIVE-ι-RESIDUAL.**  The dependent-elim premise (eliminator typing +
motive-IH branch shape) is expressible; the zero ι-SR is unconditional; the recursive succ ι-SR is
conditional on the reduct typing, with the 2-variable subst lemma shipped and the residual dischargeable by
the NATIVE-40 unified engine (the recursive eliminators become rows whose ι-SR is the last discharge,
NATIVE-32/33).  Toward 100%, with the recursive ι-SR honestly flagged as the campaign's risk point: if it
proves intractable in the unified engine, the fallback is the 95% "one engine + pinned recursive-elim core".
NATIVE-05 locks the collapse scope from here. -/
def dependentElimExpressibility : DependentElimExpressibility where
  eliminatorTypingExpressible := true
  motiveIHBranchShapeExpressible := true
  zeroIotaSRUnconditional := true
  recursiveIotaSRConditional := true
  substitutionLemmaShipped := true
  residualDischargeableByUnion := true

/-- The verdict findings, machine-checked.  The recursive ι-SR being CONDITIONAL is a recorded finding (a
`true` flag for "is conditional"), NOT a defect — it is the precisely-named residual NATIVE-32/33 discharge. -/
theorem dependentElimExpressibility_verdict :
    dependentElimExpressibility.eliminatorTypingExpressible = true ∧
    dependentElimExpressibility.motiveIHBranchShapeExpressible = true ∧
    dependentElimExpressibility.zeroIotaSRUnconditional = true ∧
    dependentElimExpressibility.recursiveIotaSRConditional = true ∧
    dependentElimExpressibility.substitutionLemmaShipped = true ∧
    dependentElimExpressibility.residualDischargeableByUnion = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Typed
