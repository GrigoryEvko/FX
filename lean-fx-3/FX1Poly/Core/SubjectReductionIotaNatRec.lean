import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.SubstPreservationMutual
import FX1Poly.Core.NatEliminatorLayer
import FX1Poly.Core.HasCertifiedProjections
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaNatRec — nat elimination/recursor step iotas

The SR arms for the nat-successor compound iotas — now SUBSTITUTING.

  * iotaNatElimSucc :
      `natElim m z s (natSucc n) ↝ s[var 0 := natElim m z s n, var 1 := n]`
  * iotaNatRecSucc  :
      `natRec  m z s (natSucc n) ↝ s[var 0 := natRec  m z s n, var 1 := n]`

## What distinguishes these from the projecting / app-chain iotas

The Phase-Z motive shape moved the succ-branch under TWO binders (at
`scope + 2`, with var 0 the inductive hypothesis and var 1 the
predecessor).  The succ-iota now SUBSTITUTES directly into the
succ-branch rather than building a Church-encoded `gen_app` nest:

```
target = RawTerm.subst
           (RawTermSubst.cons recursiveCall (RawTermSubst.singleton predecessor))
           succBranch
```

where `recursiveCall = natElim motive zeroBranch succBranch predecessor`
(the SAME motive and branches threaded at the predecessor).  This is the
substrate's FIRST 2-variable substituting iota (beta's `subst0` is the
only prior substitution rule).

## Proof route — the substitution-stability lemma (mirrors beta-SR)

Exactly like `HasCertifiedCellDim0.preservedByBeta` routes through
`preservedBySubst0`, this arm routes through the GENERIC
`HasCertifiedCellDim0.preservedBySubst`.  The succ-branch is the
substitution SOURCE (its certified cell becomes `sourceCert`); the
2-entry `cons` substitution is certified pointwise by
`consPredecessorSubstDim0Cells`:

  * index 0 → the recursive-call cell (a fresh `gen_natElim`/`gen_natRec`
    spine certified via the layer intro);
  * index `k + 1` → the singleton's entry (`predecessor` at 0, a fresh
    `gen_var` above) via `PolyCell.singletonSubstDim0Cells`.

Because a sort-precise typed 2-variable substitution lemma DOES exist at
the certifier level (`preservedBySubst` is fully general over any
`RawTermSubst` whose every output is certified), the natElim/natRec
succ-iota SR is UNCONDITIONAL at the certifier layer — no
named-hypothesis variant is needed here.  (The TYPED-engine succ-iota,
which needs a 2-variable *typed* substitution lemma, is the place where
the conditional form may be required; see `FX1Poly/Typed`.)

## Audit-gated

`#assert_no_axioms` on both theorems.
-/

namespace FX1Poly.Core

/-- **Certify every output of the 2-entry `cons`-singleton substitution
used by the natElim/natRec succ-iota.**

The substitution `RawTermSubst.cons recursiveCall (RawTermSubst.singleton
predecessor)` (over `scope + 2` source variables, into `scope`) maps:

  * index 0 → `recursiveCall` (certified by `recursiveCallCell`);
  * index `k + 1` → `(RawTermSubst.singleton predecessor) k` (certified by
    `PolyCell.singletonSubstDim0Cells`).

Mirror of `PolyCell.singletonSubstDim0Cells` one binder deeper. -/
def PolyCell.consPredecessorSubstDim0Cells
    {profile : PolyProfile} {scope : Nat}
    (recursiveCall predecessor : RawTerm scope)
    (recursiveCallCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase recursiveCall))
    (predecessorCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase predecessor)) :
    ∀ variableIndex : Fin (scope + 2),
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          (RawTermSubst.cons recursiveCall
            (RawTermSubst.singleton predecessor) variableIndex)) := by
  intro variableIndex
  cases variableIndex with
  | mk variableIndexValue variableIndexBound =>
      cases variableIndexValue with
      | zero =>
          show PolyCell profile .term 0 scope CellBoundary.trivial
            (.termBase recursiveCall)
          exact recursiveCallCell
      | succ priorIndexValue =>
          show PolyCell profile .term 0 scope CellBoundary.trivial
            (.termBase
              (RawTermSubst.singleton predecessor
                (⟨priorIndexValue, Nat.lt_of_succ_lt_succ variableIndexBound⟩ :
                  Fin (scope + 1))))
          exact PolyCell.singletonSubstDim0Cells predecessor predecessorCell
            (⟨priorIndexValue, Nat.lt_of_succ_lt_succ variableIndexBound⟩ : Fin (scope + 1))

/-- **SR arm: `Step.iotaNatElimSucc` preserves `HasCertifiedCellDim0`.**

`natElim motive zeroBranch succBranch (natSucc predecessor)` reduces to
`succBranch[var 0 := recursiveCall, var 1 := predecessor]` with
`recursiveCall = natElim motive zeroBranch succBranch predecessor`.
Routes through the generic substitution-stability lemma
`HasCertifiedCellDim0.preservedBySubst` — the certifier's analogue of
beta-SR's `preservedBySubst0`. -/
theorem HasCertifiedCellDim0.preservedByIotaNatElimSucc
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {predecessor zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons
                  (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                  .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst
        (RawTermSubst.cons
          (.mkGen .gen_natElim ()
            (.childCons motive
              (.childCons zeroBranch
                (.childCons succBranch
                  (.childCons predecessor .childNil)))))
          (RawTermSubst.singleton predecessor))
        succBranch) := by
  obtain ⟨_, outerCell⟩ := sourceCert
  cases outerCell with
  | gen _ _ outerSpine =>
    -- Extract the four child cells (motive, zeroBranch, succBranch, natSucc wrapper).
    have motiveCell :
        PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
          (.termBase motive) :=
      outerSpine.headAtDim0 rfl
    have zeroBranchCell :
        PolyCell profile .term 0 scope CellBoundary.trivial
          (.termBase zeroBranch) :=
      outerSpine.tail.headAtDim0 rfl
    have succBranchCell :
        PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
          (.termBase succBranch) :=
      outerSpine.tail.tail.headAtDim0 rfl
    -- Extract the predecessor cell from the natSucc wrapper by drilling the spine at
    -- the FIXED sort .term (the existential-sort projection lemma loses the sort pin
    -- the natElim builder needs).
    have scrutineeWrapperCell :
        PolyCell profile .term 0 scope CellBoundary.trivial
          (.termBase (.mkGen .gen_natSucc () (.childCons predecessor .childNil))) :=
      outerSpine.tail.tail.tail.headAtDim0 rfl
    -- Extract the predecessor's .term cell from the wrapper.  The sort must be a FREE
    -- variable for `cases` to unify it with the generator-indexed sort match (dependent
    -- elimination on a .term-pinned cell fails), so the extraction is a sort-universal
    -- helper applied at .term.
    have predecessorCellOfAnySort :
        ∀ (wrapperSort : CellSort),
          PolyCell profile wrapperSort 0 scope CellBoundary.trivial
            (.termBase (.mkGen .gen_natSucc () (.childCons predecessor .childNil))) →
          PolyCell profile .term 0 scope CellBoundary.trivial (.termBase predecessor) := by
      intro wrapperSort wrapperCell
      cases wrapperCell with
      | gen _ _ wrapperSpine => exact wrapperSpine.headAtDim0 rfl
    have predecessorCell :
        PolyCell profile .term 0 scope CellBoundary.trivial
          (.termBase predecessor) :=
      predecessorCellOfAnySort .term scrutineeWrapperCell
    -- Build the recursive-call cell DIRECTLY at sort .term (the existential-wrapping
    -- builder loses the sort pin consPredecessorSubstDim0Cells needs):
    -- natElim motive zeroBranch succBranch predecessor.
    have recursiveCallCell :
        PolyCell profile .term 0 scope CellBoundary.trivial
          (.termBase
            (.mkGen .gen_natElim ()
              (.childCons motive
                (.childCons zeroBranch
                  (.childCons succBranch
                    (.childCons predecessor .childNil)))))) :=
      PolyCell.gen
        SupportedGenerator.gen_natElim
        (genPayloadEvidence (generator := .gen_natElim) (scope := scope) ())
        (CertifiedTermSpine.cons motiveCell
          (CertifiedTermSpine.cons zeroBranchCell
            (CertifiedTermSpine.cons succBranchCell
              (CertifiedTermSpine.cons predecessorCell
                CertifiedTermSpine.nil))))
    -- Apply the generic substitution-stability lemma.
    exact HasCertifiedCellDim0.preservedBySubst
      (RawTermSubst.cons
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons predecessor .childNil)))))
        (RawTermSubst.singleton predecessor))
      (PolyCell.consPredecessorSubstDim0Cells _ predecessor
        recursiveCallCell predecessorCell)
      ⟨.term, succBranchCell⟩

/-- **SR arm: `Step.iotaNatRecSucc` preserves `HasCertifiedCellDim0`.**

Symmetric to `preservedByIotaNatElimSucc`: the substrate treats
`gen_natElim` and `gen_natRec` identically (same arity, same
binderShifts).  Only differences: outer source generator is `gen_natRec`,
and the recursive call rebuilds with `gen_natRec`. -/
theorem HasCertifiedCellDim0.preservedByIotaNatRecSucc
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {predecessor zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons
                  (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                  .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst
        (RawTermSubst.cons
          (.mkGen .gen_natRec ()
            (.childCons motive
              (.childCons zeroBranch
                (.childCons succBranch
                  (.childCons predecessor .childNil)))))
          (RawTermSubst.singleton predecessor))
        succBranch) := by
  obtain ⟨_, outerCell⟩ := sourceCert
  cases outerCell with
  | gen _ _ outerSpine =>
    have motiveCell :
        PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
          (.termBase motive) :=
      outerSpine.headAtDim0 rfl
    have zeroBranchCell :
        PolyCell profile .term 0 scope CellBoundary.trivial
          (.termBase zeroBranch) :=
      outerSpine.tail.headAtDim0 rfl
    have succBranchCell :
        PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
          (.termBase succBranch) :=
      outerSpine.tail.tail.headAtDim0 rfl
    have scrutineeWrapperCell :
        PolyCell profile .term 0 scope CellBoundary.trivial
          (.termBase (.mkGen .gen_natSucc () (.childCons predecessor .childNil))) :=
      outerSpine.tail.tail.tail.headAtDim0 rfl
    -- Extract the predecessor's .term cell from the wrapper.  The sort must be a FREE
    -- variable for `cases` to unify it with the generator-indexed sort match (dependent
    -- elimination on a .term-pinned cell fails), so the extraction is a sort-universal
    -- helper applied at .term.
    have predecessorCellOfAnySort :
        ∀ (wrapperSort : CellSort),
          PolyCell profile wrapperSort 0 scope CellBoundary.trivial
            (.termBase (.mkGen .gen_natSucc () (.childCons predecessor .childNil))) →
          PolyCell profile .term 0 scope CellBoundary.trivial (.termBase predecessor) := by
      intro wrapperSort wrapperCell
      cases wrapperCell with
      | gen _ _ wrapperSpine => exact wrapperSpine.headAtDim0 rfl
    have predecessorCell :
        PolyCell profile .term 0 scope CellBoundary.trivial
          (.termBase predecessor) :=
      predecessorCellOfAnySort .term scrutineeWrapperCell
    have recursiveCallCell :
        PolyCell profile .term 0 scope CellBoundary.trivial
          (.termBase
            (.mkGen .gen_natRec ()
              (.childCons motive
                (.childCons zeroBranch
                  (.childCons succBranch
                    (.childCons predecessor .childNil)))))) :=
      PolyCell.gen
        SupportedGenerator.gen_natRec
        (genPayloadEvidence (generator := .gen_natRec) (scope := scope) ())
        (CertifiedTermSpine.cons motiveCell
          (CertifiedTermSpine.cons zeroBranchCell
            (CertifiedTermSpine.cons succBranchCell
              (CertifiedTermSpine.cons predecessorCell
                CertifiedTermSpine.nil))))
    exact HasCertifiedCellDim0.preservedBySubst
      (RawTermSubst.cons
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons predecessor .childNil)))))
        (RawTermSubst.singleton predecessor))
      (PolyCell.consPredecessorSubstDim0Cells _ predecessor
        recursiveCallCell predecessorCell)
      ⟨.term, succBranchCell⟩

/-- **SR arm: `Step.iotaListElimCons` preserves `HasCertifiedCellDim0`.**

Three nested `gen_app`s plus a recursive `gen_listElim` (Phase-Z motive shape:
motive heads the spine, scrutinee LAST, the recursive `gen_listElim` THREADS the
motive):

```
target =
  gen_app
    [ gen_app
        [ gen_app [consBranch, headVal]
        , tailVal
        ]
    , gen_listElim [motive, nilBranch, consBranch, tailVal]
    ]
```

The outer spine binds `motiveCell` (shift-1 head), `nilBranchCell`,
`consBranchCell`, then the `listCons` wrapper carrying head and tail. -/
theorem HasCertifiedCellDim0.preservedByIotaListElimCons
    {profile : PolyProfile} {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {headVal tailVal nilBranch consBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch
                (.childCons
                  (.mkGen .gen_listCons ()
                    (.childCons headVal (.childCons tailVal .childNil)))
                  .childNil))))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons consBranch (.childCons headVal .childNil)))
              (.childCons tailVal .childNil)))
          (.childCons
            (.mkGen .gen_listElim ()
              (.childCons motive
                (.childCons nilBranch
                  (.childCons consBranch
                    (.childCons tailVal .childNil)))))
            .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons motiveCell restAfterMotive =>
        cases restAfterMotive with
        | cons nilBranchCell restAfterNil =>
          cases restAfterNil with
          | cons consBranchCell restAfterCons =>
            cases restAfterCons with
            | cons listConsCell _ =>
              generalize hSort :
                  (ChildSpec.termSameScope.cellSort) = innerSort
                at listConsCell
              cases listConsCell with
              | gen _ _ listConsInnerSpine =>
                cases listConsInnerSpine with
                | cons headValCell restListConsInner =>
                  cases restListConsInner with
                  | cons tailValCell _ =>
                    -- Build innermost: app(consBranch, headVal).
                    let app1Cell :=
                      PolyCell.gen
                        SupportedGenerator.gen_app
                        (genPayloadEvidence (generator := .gen_app)
                                             (scope := scope) ())
                        (CertifiedTermSpine.cons consBranchCell
                          (CertifiedTermSpine.cons headValCell
                            CertifiedTermSpine.nil))
                    -- Build middle: app(app1, tailVal).
                    let app2Cell :=
                      PolyCell.gen
                        SupportedGenerator.gen_app
                        (genPayloadEvidence (generator := .gen_app)
                                             (scope := scope) ())
                        (CertifiedTermSpine.cons app1Cell
                          (CertifiedTermSpine.cons tailValCell
                            CertifiedTermSpine.nil))
                    -- Build recursive: listElim(motive, nilBranch, consBranch, tailVal).
                    let recCell :=
                      PolyCell.gen
                        SupportedGenerator.gen_listElim
                        (genPayloadEvidence (generator := .gen_listElim)
                                             (scope := scope) ())
                        (CertifiedTermSpine.cons motiveCell
                          (CertifiedTermSpine.cons nilBranchCell
                            (CertifiedTermSpine.cons consBranchCell
                              (CertifiedTermSpine.cons tailValCell
                                CertifiedTermSpine.nil))))
                    -- Outer: app(app2, recCell).
                    exact .intro .term
                      (PolyCell.gen
                        SupportedGenerator.gen_app
                        (genPayloadEvidence (generator := .gen_app)
                                             (scope := scope) ())
                        (CertifiedTermSpine.cons app2Cell
                          (CertifiedTermSpine.cons recCell
                            CertifiedTermSpine.nil)))

end FX1Poly.Core
