import FX1Poly.Core.Metatheory.Canonicity.NatCanonicalFormsCandidate
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.ApplicationStrongNormalizationForward
import FX1Poly.Core.Rewriting.Normalize.RawTermNF

/-! # FX1Poly/Core/NatShapedRecursorCellStrongNormalization
    — the GENERATOR-AGNOSTIC nat-shaped recursor cell-SN engines: one argument, parameterized over the cell
      spine and its six-way inversion, from which the `natElim` and `natRec` twins are derived verbatim

`gen_natElim` and `gen_natRec` share the v2 substrate's arity-4 metadata: the same Phase-Z motive shape
(motive at `scope + 1`, scrutinee LAST), the same 2-substituent succ-ι contractum, and the same six-way
inversion — `Step.from_natRec` is declared "Same shape as `from_natElim`" at its definition site
(`Rewriting/Reduction/Step/StepInversion.lean`), and the two spines `natElimCellSpine` / `natRecCellSpine`
differ only in the generator constant.  The cell-SN engines therefore do not depend on WHICH of the two
recursors is being eliminated: they depend only on the SHAPE.  This file states that shape once.

`NatShapedSpineInversion cellSpine` packages the six-way inversion as a hypothesis over an abstract spine.
Instantiating it at `natElimCellSpine` / `Step.from_natElim` and at `natRecCellSpine` / `Step.from_natRec`
re-derives each existing twin at its EXACT statement — the twins keep their names and types and become
one-line applications of the engines below.

Three engines, matching the three cell-SN shapes the consumers call:

* `natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee` — three nested `Acc.ndrec` on the branches,
  scrutinee fixed normal (so scrutinee-congruence is impossible), firing obligation conditioned on
  `scrutinee = natSuccCell predecessor`.
* `natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability` — the same three folds with a
  `StepStar` reachability witness threaded through every `Acc` motive, making the firing obligation
  SATISFIABLE (it receives the provenance of each stepped branch, not merely its SN).
* `natShapedCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN` — the four-fold
  generalization (scrutinee merely SN, recursed on as well), whose firing obligation is keyed on the scrutinee
  REACHING a successor cell and discharged through an abstract contractum reduction-congruence.

The engines are silent on the SATISFIABILITY of their firing obligations — that is the consumers' business and
is unchanged by this refactor.  Nothing here strengthens or weakens any shipped statement.

## Zero-axiom verification

`Acc.ndrec` / `Acc.intro` well-founded recursion, the abstract `NatShapedSpineInversion` hypothesis,
`RawTerm.isStepNormalForm_blocks_step`, `IsStronglyNormalizing.descendStepStar`, and `StepStar.single` /
`StepStar.trans_compose` / `StepStar.refl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration swept by `#audit_namespace FX1Poly.Core` in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

/-- **The six-way inversion shape shared by every nat-shaped recursor cell.**  A `Step` out of the cell
`cellSpine motive scrutinee zeroBranch succBranch` is one of: the zero-ι (scrutinee is `natZeroCell`, target is
the zero branch); the succ-ι (scrutinee is `natSuccCell predecessor`, target is the 2-substituent contractum
threading the recursive cell at the predecessor); a congruence step in the motive, the zero branch, or the succ
branch; or a congruence step in the scrutinee.

`Step.from_natElim` inhabits this at `cellSpine := natElimCellSpine`, and `Step.from_natRec` at
`cellSpine := natRecCellSpine` — the v2 substrate gives the two generators identical metadata, so the two
inversions are the same proposition modulo the generator constant. -/
abbrev NatShapedSpineInversion {scope : Nat}
    (cellSpine :
      RawTerm (scope + 1) → RawTerm scope → RawTerm scope → RawTerm (scope + 2) → RawTerm scope) : Prop :=
  ∀ {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)} {target : RawTerm scope},
    Step (cellSpine motive scrutinee zeroBranch succBranch) target →
    (scrutinee = natZeroCell ∧ target = zeroBranch)
    ∨ (∃ (predecessor : RawTerm scope),
        scrutinee = natSuccCell predecessor ∧
        target =
          RawTerm.subst
            (RawTermSubst.cons (cellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)
    ∨ (∃ (motiveAfter : RawTerm (scope + 1)),
        target = cellSpine motiveAfter scrutinee zeroBranch succBranch ∧ Step motive motiveAfter)
    ∨ (∃ (zeroAfter : RawTerm scope),
        target = cellSpine motive scrutinee zeroAfter succBranch ∧ Step zeroBranch zeroAfter)
    ∨ (∃ (succAfter : RawTerm (scope + 2)),
        target = cellSpine motive scrutinee zeroBranch succAfter ∧ Step succBranch succAfter)
    ∨ (∃ (scrutineeAfter : RawTerm scope),
        target = cellSpine motive scrutineeAfter zeroBranch succBranch ∧ Step scrutinee scrutineeAfter)

/-- **The nat-shaped contractum reduction-congruence shape.**  Branch-stepping the succ-ι contractum produces a
REDUCT of the contractum at the original branches (the firing predecessor held fixed).
`natElimSuccContractumReduces` / `natRecSuccContractumReduces` inhabit this at their respective spines; it is
what makes the reachability-threaded firing obligations dischargeable from the ORIGINAL contractum's SN. -/
abbrev NatShapedContractumCongruence {scope : Nat}
    (cellSpine :
      RawTerm (scope + 1) → RawTerm scope → RawTerm scope → RawTerm (scope + 2) → RawTerm scope) : Prop :=
  ∀ {motive motiveReduct : RawTerm (scope + 1)}
    {predecessor zeroBranch zeroBranchReduct : RawTerm scope}
    {succBranch succBranchReduct : RawTerm (scope + 2)},
    StepStar motive motiveReduct → StepStar zeroBranch zeroBranchReduct →
    StepStar succBranch succBranchReduct →
    StepStar
      (RawTerm.subst
        (RawTermSubst.cons (cellSpine motive predecessor zeroBranch succBranch)
          (RawTermSubst.singleton predecessor))
        succBranch)
      (RawTerm.subst
        (RawTermSubst.cons (cellSpine motiveReduct predecessor zeroBranchReduct succBranchReduct)
          (RawTermSubst.singleton predecessor))
        succBranchReduct)

/-- **The nat-shaped recursor cell-SN engine for a NORMAL scrutinee (firing-reduced).**  A nat-shaped cell with
a NORMAL scrutinee and strongly-normalizing branches is strongly normalizing, given the contractum is strongly
normalizing whenever the scrutinee is a successor (`succContractumSN`).  Three nested `Acc.ndrec` on
`(motive, zeroBranch, succBranch)`: scrutinee-congruence is impossible (the scrutinee is normal), ι-zero lands
on the current zero branch, ι-succ on `succContractumSN`, and the three branch congruences recurse.

This is a sound conditional that REDUCES cell SN to the single firing contractum; it does NOT discharge that
contractum.  The generator-agnostic core of `natElimCellSpine_isStronglyNormalizing_of_normalScrutinee` and its
`natRec` twin. -/
theorem natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee {scope : Nat}
    {cellSpine :
      RawTerm (scope + 1) → RawTerm scope → RawTerm scope → RawTerm (scope + 2) → RawTerm scope}
    (spineInversion : NatShapedSpineInversion cellSpine)
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succContractumSN :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
        IsStronglyNormalizing currentMotive → IsStronglyNormalizing currentZero →
        IsStronglyNormalizing currentSucc →
        scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons (cellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing (cellSpine motive scrutinee zeroBranch succBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun innerMotive =>
      ∀ {currentZero : RawTerm scope} {currentSucc : RawTerm (scope + 2)},
        IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
        IsStronglyNormalizing (cellSpine innerMotive scrutinee currentZero currentSucc))
    (m := fun currentMotive currentMotiveSuccessors motiveIH => by
      intro currentZero currentSucc currentZeroTerminates currentSuccTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            ∀ {laterSucc : RawTerm (scope + 2)},
              IsStronglyNormalizing laterSucc →
              IsStronglyNormalizing (cellSpine currentMotive scrutinee innerZero laterSucc))
          (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
            intro laterSucc laterSuccTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  IsStronglyNormalizing
                    (cellSpine currentMotive scrutinee currentInnerZero innerSucc))
                (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
                  apply Acc.intro
                  intro target step
                  rcases spineInversion step with
                    ⟨_scrutineeIsZero, targetIsZero⟩ |
                    ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                    ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                    ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                    ⟨succAfter, targetIsSuccStep, succStep⟩ |
                    ⟨scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩
                  · rw [targetIsZero]
                    exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                  · rw [targetIsContractum]
                    exact succContractumSN currentMotive currentInnerZero currentInnerSucc
                      predecessor
                      (Acc.intro currentMotive currentMotiveSuccessors)
                      (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                      (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                      scrutineeIsSucc
                  · rw [targetIsMotiveStep]
                    exact motiveIH motiveAfter motiveStep
                      (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                      (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                  · rw [targetIsZeroStep]
                    exact zeroIH zeroAfter zeroStep
                      (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                  · rw [targetIsSuccStep]
                    exact succIH succAfter succStep
                  · exact absurd scrutineeStep
                      (RawTerm.isStepNormalForm_blocks_step scrutineeNormal scrutineeAfter))
                laterSuccTerminates)
          currentZeroTerminates)
          currentSuccTerminates)
    motiveTerminates)
    zeroBranchTerminates succBranchTerminates

/-- **The reduct-tracking nat-shaped cell-SN engine (satisfiable firing premise).**  A nat-shaped cell with a
NORMAL scrutinee and strongly-normalizing branches is strongly normalizing, given the REACHABILITY-AWARE firing
obligation `firingContractumSN`: whenever the scrutinee is `natSuccCell predecessor` and the current branches
are reachable from the originals, the substituted succ-ι contractum at the current branches is strongly
normalizing.

Unlike `natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee`, whose firing obligation quantifies over
arbitrary SN currents and is therefore unsatisfiable at open scope, this obligation receives `StepStar`
witnesses (`motive` reaches `currentMotive`, etc.) — the PROVENANCE that makes it dischargeable from the
original contractum's SN through a `NatShapedContractumCongruence` + `descendStepStar`.  Three nested
`Acc.ndrec` on the branch accessibilities, each motive carrying its reachability witness.

The generator-agnostic core of `natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability` and
its `natRec` twin. -/
theorem natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability {scope : Nat}
    {cellSpine :
      RawTerm (scope + 1) → RawTerm scope → RawTerm scope → RawTerm (scope + 2) → RawTerm scope}
    (spineInversion : NatShapedSpineInversion cellSpine)
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeNormal : RawTerm.isStepNormalForm scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (firingContractumSN :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
        (currentSucc : RawTerm (scope + 2)) (predecessor : RawTerm scope),
        StepStar motive currentMotive → StepStar zeroBranch currentZero →
        StepStar succBranch currentSucc → scrutinee = natSuccCell predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons (cellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing (cellSpine motive scrutinee zeroBranch succBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun innerMotive =>
      StepStar motive innerMotive →
      ∀ {currentZero : RawTerm scope} {currentSucc : RawTerm (scope + 2)},
        StepStar zeroBranch currentZero → StepStar succBranch currentSucc →
        IsStronglyNormalizing (cellSpine innerMotive scrutinee currentZero currentSucc))
    (m := fun currentMotive _currentMotiveSuccessors motiveIH => by
      intro motiveChain currentZero currentSucc zeroChain succChain
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            StepStar zeroBranch innerZero →
            ∀ {laterSucc : RawTerm (scope + 2)},
              StepStar succBranch laterSucc →
              IsStronglyNormalizing (cellSpine currentMotive scrutinee innerZero laterSucc))
          (m := fun currentInnerZero _currentInnerZeroSuccessors zeroIH => by
            intro innerZeroChain laterSucc laterSuccChain
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  StepStar succBranch innerSucc →
                  IsStronglyNormalizing
                    (cellSpine currentMotive scrutinee currentInnerZero innerSucc))
                (m := fun currentInnerSucc _currentInnerSuccSuccessors succIH => by
                  intro innerSuccChain
                  apply Acc.intro
                  intro target step
                  rcases spineInversion step with
                    ⟨_scrutineeIsZero, targetIsZero⟩ |
                    ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                    ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                    ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                    ⟨succAfter, targetIsSuccStep, succStep⟩ |
                    ⟨scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩
                  · rw [targetIsZero]
                    exact IsStronglyNormalizing.descendStepStar zeroBranchTerminates innerZeroChain
                  · rw [targetIsContractum]
                    exact firingContractumSN currentMotive currentInnerZero currentInnerSucc
                      predecessor motiveChain innerZeroChain innerSuccChain scrutineeIsSucc
                  · rw [targetIsMotiveStep]
                    exact motiveIH motiveAfter motiveStep
                      (StepStar.trans_compose motiveChain (StepStar.single motiveStep))
                      innerZeroChain innerSuccChain
                  · rw [targetIsZeroStep]
                    exact zeroIH zeroAfter zeroStep
                      (StepStar.trans_compose innerZeroChain (StepStar.single zeroStep))
                      innerSuccChain
                  · rw [targetIsSuccStep]
                    exact succIH succAfter succStep
                      (StepStar.trans_compose innerSuccChain (StepStar.single succStep))
                  · exact absurd scrutineeStep
                      (RawTerm.isStepNormalForm_blocks_step scrutineeNormal scrutineeAfter))
                (IsStronglyNormalizing.descendStepStar succBranchTerminates laterSuccChain))
              laterSuccChain)
          (IsStronglyNormalizing.descendStepStar zeroBranchTerminates zeroChain))
        zeroChain succChain)
    motiveTerminates)
    (StepStar.refl motive) (StepStar.refl zeroBranch) (StepStar.refl succBranch)

/-- **The reduct-tracking nat-shaped cell-SN engine for a REDUCING scrutinee (satisfiable firing premise).**
The four-fold reachability generalization: the scrutinee need not be normal — it is merely strongly
normalizing — and the engine recurses on the scrutinee as well as the three branches, threading a `StepStar`
reachability witness through ALL FOUR `Acc.ndrec` levels.

The firing obligation is the satisfiable `originalContractumSN`, keyed on the scrutinee REACHING a successor
cell (`StepStar scrutinee (natSuccCell predecessor)`): at the firing the scrutinee reachability identifies the
predecessor, the original contractum SN comes from `originalContractumSN`, and the stepped-branch contractum is
its reduct by `contractumCongruence` + `descendStepStar`.

The generator-agnostic core of `natElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN`
and its `natRec` twin. -/
theorem natShapedCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN {scope : Nat}
    {cellSpine :
      RawTerm (scope + 1) → RawTerm scope → RawTerm scope → RawTerm (scope + 2) → RawTerm scope}
    (spineInversion : NatShapedSpineInversion cellSpine)
    (contractumCongruence : NatShapedContractumCongruence cellSpine)
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (originalContractumSN :
      ∀ (predecessor : RawTerm scope), StepStar scrutinee (natSuccCell predecessor) →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons (cellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsStronglyNormalizing (cellSpine motive scrutinee zeroBranch succBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      StepStar scrutinee currentScrutinee →
      ∀ {currentMotive : RawTerm (scope + 1)} {currentZero : RawTerm scope}
        {currentSucc : RawTerm (scope + 2)},
        StepStar motive currentMotive → StepStar zeroBranch currentZero →
        StepStar succBranch currentSucc →
        IsStronglyNormalizing (cellSpine currentMotive currentScrutinee currentZero currentSucc))
    (m := fun currentScrutinee _currentScrutineeSuccessors scrutineeIH => by
      intro scrutineeReaches currentMotive currentZero currentSucc motiveReaches zeroReaches succReaches
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            StepStar motive innerMotive →
            ∀ {innerZero : RawTerm scope} {innerSucc : RawTerm (scope + 2)},
              StepStar zeroBranch innerZero → StepStar succBranch innerSucc →
              IsStronglyNormalizing (cellSpine innerMotive currentScrutinee innerZero innerSucc))
          (m := fun currentInnerMotive _currentInnerMotiveSuccessors motiveIH => by
            intro motiveReaches' innerZero innerSucc zeroReaches' succReaches'
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerZeroVar =>
                  StepStar zeroBranch innerZeroVar →
                  ∀ {innerSuccVar : RawTerm (scope + 2)}, StepStar succBranch innerSuccVar →
                    IsStronglyNormalizing
                      (cellSpine currentInnerMotive currentScrutinee innerZeroVar innerSuccVar))
                (m := fun currentInnerZero _currentInnerZeroSuccessors zeroIH => by
                  intro zeroReaches'' innerSuccVar succReaches''
                  exact
                    (Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerSuccVar2 =>
                        StepStar succBranch innerSuccVar2 →
                        IsStronglyNormalizing
                          (cellSpine currentInnerMotive currentScrutinee currentInnerZero innerSuccVar2))
                      (m := fun currentInnerSucc _currentInnerSuccSuccessors succIH => by
                        intro succReaches'''
                        apply Acc.intro
                        intro target step
                        rcases spineInversion step with
                          ⟨_scrutineeIsZero, targetIsZero⟩ |
                          ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                          ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                          ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                          ⟨succAfter, targetIsSuccStep, succStep⟩ |
                          ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                        · rw [targetIsZero]
                          exact IsStronglyNormalizing.descendStepStar zeroBranchTerminates zeroReaches''
                        · rw [targetIsContractum]
                          have scrutineeReachesSucc : StepStar scrutinee (natSuccCell predecessor) := by
                            rw [scrutineeIsSucc] at scrutineeReaches; exact scrutineeReaches
                          exact IsStronglyNormalizing.descendStepStar
                            (originalContractumSN predecessor scrutineeReachesSucc)
                            (contractumCongruence motiveReaches' zeroReaches'' succReaches''')
                        · rw [targetIsMotiveStep]
                          exact motiveIH motiveAfter motiveStep
                            (StepStar.trans_compose motiveReaches' (StepStar.single motiveStep))
                            zeroReaches'' succReaches'''
                        · rw [targetIsZeroStep]
                          exact zeroIH zeroAfter zeroStep
                            (StepStar.trans_compose zeroReaches'' (StepStar.single zeroStep))
                            succReaches'''
                        · rw [targetIsSuccStep]
                          exact succIH succAfter succStep
                            (StepStar.trans_compose succReaches''' (StepStar.single succStep))
                        · rw [targetIsScrutineeStep]
                          exact scrutineeIH scrutineeAfter scrutineeStep
                            (StepStar.trans_compose scrutineeReaches (StepStar.single scrutineeStep))
                            motiveReaches' zeroReaches'' succReaches''')
                      (IsStronglyNormalizing.descendStepStar succBranchTerminates succReaches''))
                    succReaches'')
                (IsStronglyNormalizing.descendStepStar zeroBranchTerminates zeroReaches'))
              zeroReaches' succReaches')
          (IsStronglyNormalizing.descendStepStar motiveTerminates motiveReaches))
        motiveReaches zeroReaches succReaches)
    scrutineeTerminates)
    (StepStar.refl scrutinee) (StepStar.refl motive) (StepStar.refl zeroBranch) (StepStar.refl succBranch)

end StepStar
end FX1Poly.Core
