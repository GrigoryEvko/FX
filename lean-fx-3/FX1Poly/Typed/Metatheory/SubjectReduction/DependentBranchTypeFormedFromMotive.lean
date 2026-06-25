import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstUnionTyped
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity
import FX1Poly.Typed.Cell.NatElimDependentSuccType

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/DependentBranchTypeFormedFromMotive
    — the dependent branch-type FORMEDNESS from the motive's universe typing (SR-DSL-2 type-SR content)

The eliminator-congruence subject reduction (gate 2, the `elim` arm of `UnionCongruenceCloser`) has one
genuinely hard child position — the MOTIVE.  When the motive steps `motive ⟶ motive'`, every dependent BRANCH
classifier built from the motive drifts (`subst0 motive C ⟶ subst0 motive' C`,
`natElimDependentSuccBranchType motive ⟶ … motive'`, …).  Re-typing a branch at its drifted classifier through
the union `conv` arm needs that drifted classifier to be a WELL-FORMED TYPE — the universe-code formedness of the
classifier built from `motive'`.

This file ships the genuinely-new content the congruence-SR motive arm needs and the validity layer did NOT
already provide: the formedness of the **multi-binder dependent branch types** from the motive's universe typing
ALONE (the `subst0 motive C` nullary-constructor branch classifiers are already discharged by
`UnionClassifierIsType.dependentMotiveOutputFormed_ofMotiveAndArgument`).  Each is the substitution master
`HasTypeUnion.substRespectingContext` applied to the motive at the branch type's defining re-basing
substitution, with the universe-code classifier surviving by `subst_universeCodeCell` (closed) — the type-SR
content `templateTypeStepPreservesUniverse` dispatches to per macro-arm.

This commit ships the `natElim` / `natRec` succ-branch type (the FIRST genuinely two-binder branch — the
representative crux).  The `option` / `either` / `list` (piTyCode-based) branch types follow.

## Zero-axiom verification

`HasTypeUnion.substRespectingContext` + the native `var` / `natSucc` intro arms + `subst_universeCodeCell` over
a `Fin` 0/successor split; the re-basing's variable images land via `RawTerm.weaken_subst_cons` +
`doubleWeaken_eq_substShiftBy2` and the context lookups.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- The succ-branch re-basing substitution: the source nat binder (`var 0`) maps to `natSucc (var 1)` (the
predecessor lifted past the IH binder) and every ambient context variable shifts up by two (past the two succ
binders).  This is the substitution `natElimDependentSuccBranchType` applies to the motive (its defining
re-basing). -/
def succBranchRebasing (scope : Nat) : RawTermSubst (scope + 1) (scope + 2) :=
  RawTermSubst.cons
    (natSuccCell (.mkGen .gen_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩ .childNil))
    (fun position => .mkGen .gen_var ⟨position.val + 2, Nat.add_lt_add_right position.isLt 2⟩ .childNil)

/-- **The succ-branch re-basing substitution is union-typed** from `context.cons natTypeCell` into the
doubly-extended succ-branch context `(context.cons natTypeCell).cons motive`.  Position `0` (the source nat
binder) maps to `natSucc (var 1)` typed at `natTypeCell` (the predecessor binder); position `k+1` maps to
`var (k+2)` (the ambient context var skipped past the two succ binders), typed at the doubly-weakened lookup.
The `SubstUnionTyped` premise `HasTypeUnion.substRespectingContext` consumes to push the motive's typing
through the succ-branch re-basing. -/
theorem succBranchRebasing_isSubstUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (motive : RawTerm (scope + 1)) :
    HasTypeUnion.SubstUnionTyped (context.cons natTypeCell)
      ((context.cons natTypeCell).cons motive) (succBranchRebasing scope) := by
  intro index
  match index with
  | ⟨0, _⟩ =>
      -- The image is `natSucc (var 1)`; the substituted lookup is the closed `natTypeCell`.
      show HasTypeUnion profile ((context.cons natTypeCell).cons motive)
        (natSuccCell (.mkGen .gen_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩ .childNil))
        (RawTerm.subst (succBranchRebasing scope)
          ((context.cons natTypeCell).lookup ⟨0, Nat.zero_lt_succ scope⟩))
      rw [TypingContext.lookup_cons_zero, rename_natTypeCell, subst_natTypeCell]
      -- `natSucc (var 1) : natTypeCell` via the native `natSucc` intro; its sole obligation is `var 1 : nat`.
      refine HasTypeUnion.intro ((context.cons natTypeCell).cons motive) .gen_natSucc natSuccIntroRule
        (.childCons (.mkGen .gen_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩ .childNil) .childNil)
        .childNil LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
      intro obligation hmem
      cases hmem with
      | head =>
          -- `var 1 : ((context.cons natTypeCell).cons motive).lookup 1 = natTypeCell`.
          have varTyped := HasTypeUnion.var ((context.cons natTypeCell).cons motive)
            ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩
          rwa [show ((context.cons natTypeCell).cons motive).lookup
              ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩ = natTypeCell by
            rw [TypingContext.lookup_cons_succ, TypingContext.lookup_cons_zero, rename_natTypeCell,
              rename_natTypeCell]] at varTyped
      | tail _ tailMem => cases tailMem
  | ⟨Nat.succ priorIndex, indexBound⟩ =>
      -- The image is `var (priorIndex + 2)`; the substituted lookup is the doubly-weakened ambient lookup.
      show HasTypeUnion profile ((context.cons natTypeCell).cons motive)
        (.mkGen .gen_var ⟨priorIndex + 2, Nat.add_lt_add_right (Nat.lt_of_succ_lt_succ indexBound) 2⟩
          .childNil)
        (RawTerm.subst (succBranchRebasing scope)
          ((context.cons natTypeCell).lookup ⟨priorIndex + 1, indexBound⟩))
      -- `lookup (k+1)` is the `rename weaken` of the ambient lookup; `weaken_subst_cons` strips the cons head.
      unfold succBranchRebasing
      rw [TypingContext.lookup_cons_succ, RawTerm.weaken_subst_cons]
      -- The native `var` arm: `var (priorIndex + 2) : lookup (priorIndex + 2)`; that lookup IS `subst shiftBy2`.
      have varTyped := HasTypeUnion.var ((context.cons natTypeCell).cons motive)
        ⟨priorIndex + 2, Nat.add_lt_add_right (Nat.lt_of_succ_lt_succ indexBound) 2⟩
      rwa [show ((context.cons natTypeCell).cons motive).lookup
          ⟨priorIndex + 2, Nat.add_lt_add_right (Nat.lt_of_succ_lt_succ indexBound) 2⟩
          = RawTerm.subst
              (fun position : Fin scope => RawTerm.mkGen Generator.gen_var
                ⟨position.val + 2, Nat.add_lt_add_right position.isLt 2⟩ .childNil)
              (context.lookup ⟨priorIndex, Nat.lt_of_succ_lt_succ indexBound⟩) by
        rw [TypingContext.lookup_cons_succ, TypingContext.lookup_cons_succ,
          ← RawTerm.weaken_eq_rename, ← RawTerm.weaken_eq_rename, doubleWeaken_eq_substShiftBy2]] at varTyped

/-- **★ The `natElim` / `natRec` succ-branch type is a well-formed type from the motive's universe typing.**
Given the motive typed at `universeCodeCell levelExpr flag` under one `natTypeCell` binder,
`natElimDependentSuccBranchType motive` is union-typed at the SAME universe code under the two succ binders
`(context.cons natTypeCell).cons motive`.  The substitution master `HasTypeUnion.substRespectingContext` pushes
the motive's typing through the succ-branch re-basing (`succBranchRebasing_isSubstUnionTyped`); the universe-code
classifier survives (`subst_universeCodeCell`, closed).  This is the type-SR ingredient the congruence-SR motive
arm reclassifies the stepped step-branch through — the formedness the validity layer's `classifierIsType` could
only supply circularly (it needs the branch already typed at the drifted classifier). -/
theorem natElimDependentSuccBranchType_formed_ofMotive {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (motive : RawTerm (scope + 1))
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (motiveTyped : HasTypeUnion profile (context.cons natTypeCell) motive
      (universeCodeCell levelExpr flag)) :
    HasTypeUnion profile ((context.cons natTypeCell).cons motive)
      (natElimDependentSuccBranchType motive) (universeCodeCell levelExpr flag) := by
  have substituted := motiveTyped.substRespectingContext ((context.cons natTypeCell).cons motive)
    (succBranchRebasing scope) (succBranchRebasing_isSubstUnionTyped context motive)
  rw [subst_universeCodeCell] at substituted
  exact substituted

end FX1Poly.Typed
