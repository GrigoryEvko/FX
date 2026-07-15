import FX1Poly.Core.Substrate.Neutral.NeutralTerm
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationSubst
import FX1Poly.Axis.Term.Core.RawTermFoldNonVarCommute

/-! # FX1Poly/Core/Substrate/Neutral/NeutralSubstReflection
    — no neutral term is the closed-term image of a substitution (reverse neutral reflection)

A term in the image of a substitution `RawTerm.subst sigma preimage` whose `preimage` is CLOSED
(`preimage : RawTerm 0`) cannot be neutral.  Intuitively: a neutral term is stuck at a free-variable head,
but the image of a closed term under any substitution has no free variable to be stuck at — the substitution
relocates the closed structure without introducing a head variable.

This is the reverse direction of `IsNeutral.rename` (forward: neutrality is preserved by renaming).  The
forward direction is trivial (renaming computes through `mkGen` definitionally); the reverse genuinely inverts
the substitution at each elimination form, recovering the principal child's preimage and recursing.

## The consistency consumer (the scope-1 wall of #1697)

The native consistency leg's reducibility bypass produces an `emptyTaitCandidate` member at the closing
weakening `RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject` (scope 1, a weakening of the closed
`subject`).  Refuting it needs `IsNeutral (subst Fin.elim0 normalForm) → False` for a closed `normalForm` —
exactly this lemma at the closing substitution.  `IsNeutral.noClosed` (scope 0) does not reach scope 1; this
reflection bridges the gap.

## Proof shape (the validated cell-inversion recipe)

`induction` on the `IsNeutral` derivation with a scope-polymorphic motive (`∀ preimage sigma, subst sigma
preimage = <armCell> → False`), mirroring `IsNeutral.elimEmptyScope`.  Each arm:
  * `cases preimage` into `mkGen generator payload children`;
  * `by_cases generator = gen_var` — the variable case is impossible at scope 0 (`payload : Fin 0`);
  * the non-variable case pins `generator` to the arm's head via `RawTerm.subst_rootGenerator_of_not_var`
    (substitution preserves a non-variable head) composed with the cell equation;
  * recover the children spine (`cases children`), distribute the substitution
    (`RawTerm.subst_mkGen_of_ne_var`), and `injection`-drill to the PRINCIPAL child's preimage equation
    `subst sigma principalChild = principal`, fed to the principal child's induction hypothesis.
The `var` arm closes by head-generator distinctness; the eliminator arms recurse on the neutral principal child.

## Zero-axiom verification

`RawTerm.subst_rootGenerator_of_not_var`, `RawTerm.subst_mkGen_of_ne_var`, structural `cases` / `injection`
(full-enumeration, no partial-index `propext` leak — the index is fixed by the constructor, the casts absorbed
as `_`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated
per-declaration in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

/-- **★ No neutral term is the closed-term image of a substitution.**  If `RawTerm.subst sigma preimage` is
neutral and `preimage` is closed (`preimage : RawTerm 0`), contradiction.  Stated scope-polymorphically so the
induction motive stays index-clean (every eliminator arm forwards the refutation to its neutral principal
child).  The reverse of `IsNeutral.rename`; the scope-1 reflection the native consistency bypass consumes. -/
theorem IsNeutral.noClosedSubstImage : ∀ {scope : Nat} {renamedTerm : RawTerm scope},
    IsNeutral renamedTerm → ∀ {preimage : RawTerm 0} (sigma : RawTermSubst 0 scope),
      RawTerm.subst sigma preimage = renamedTerm → False := by
  intro scope renamedTerm neutral
  induction neutral with
  | var index =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          exact hVar hroot.symm
  | app _headNeutral headIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_app := hroot.symm
          subst hgen
          cases children with
          | childCons headChild tailChildren =>
            cases tailChildren with
            | childCons argChild nilChildren =>
              cases nilChildren
              rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                (.childCons headChild (.childCons argChild .childNil))] at hEq
              injection hEq with _scopeEq _genEq _payloadEq childrenEq
              injection childrenEq with _scopeEq2 _shiftEq2 _restEq2 headEq _tailEq
              exact headIH sigma headEq
  | pathApp _functionNeutral functionIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_pathApp := hroot.symm
          subst hgen
          cases children with
          | childCons functionChild tailChildren =>
            cases tailChildren with
            | childCons argChild nilChildren =>
              cases nilChildren
              rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                (.childCons functionChild (.childCons argChild .childNil))] at hEq
              injection hEq with _scopeEq _genEq _payloadEq childrenEq
              injection childrenEq with _scopeEq2 _shiftEq2 _restEq2 functionEq _tailEq
              exact functionIH sigma functionEq
  | fst _argumentNeutral argumentIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_fst := hroot.symm
          subst hgen
          cases children with
          | childCons argumentChild nilChildren =>
            cases nilChildren
            rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
              (.childCons argumentChild .childNil)] at hEq
            injection hEq with _scopeEq _genEq _payloadEq childrenEq
            injection childrenEq with _scopeEq2 _shiftEq2 _restEq2 argumentEq _tailEq
            exact argumentIH sigma argumentEq
  | snd _argumentNeutral argumentIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_snd := hroot.symm
          subst hgen
          cases children with
          | childCons argumentChild nilChildren =>
            cases nilChildren
            rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
              (.childCons argumentChild .childNil)] at hEq
            injection hEq with _scopeEq _genEq _payloadEq childrenEq
            injection childrenEq with _scopeEq2 _shiftEq2 _restEq2 argumentEq _tailEq
            exact argumentIH sigma argumentEq
  | boolElim _scrutineeNeutral scrutineeIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_boolElim := hroot.symm
          subst hgen
          cases children with
          | childCons motiveChild restA =>
            cases restA with
            | childCons thenChild restB =>
              cases restB with
              | childCons elseChild restC =>
                cases restC with
                | childCons scrutineeChild nilChildren =>
                  cases nilChildren
                  rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                    (.childCons motiveChild (.childCons thenChild
                      (.childCons elseChild (.childCons scrutineeChild .childNil))))] at hEq
                  injection hEq with _scopeEq _genEq _payloadEq childrenEq
                  injection childrenEq with _i1 _i2 _i3 _motiveEq tailA
                  injection tailA with _j1 _j2 _j3 _thenEq tailB
                  injection tailB with _k1 _k2 _k3 _elseEq tailC
                  injection tailC with _l1 _l2 _l3 scrutineeEq _tailD
                  exact scrutineeIH sigma scrutineeEq
  | natElim _scrutineeNeutral scrutineeIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_natElim := hroot.symm
          subst hgen
          cases children with
          | childCons motiveChild restA =>
            cases restA with
            | childCons zeroChild restB =>
              cases restB with
              | childCons succChild restC =>
                cases restC with
                | childCons scrutineeChild nilChildren =>
                  cases nilChildren
                  rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                    (.childCons motiveChild (.childCons zeroChild
                      (.childCons succChild (.childCons scrutineeChild .childNil))))] at hEq
                  injection hEq with _scopeEq _genEq _payloadEq childrenEq
                  injection childrenEq with _i1 _i2 _i3 _motiveEq tailA
                  injection tailA with _j1 _j2 _j3 _zeroEq tailB
                  injection tailB with _k1 _k2 _k3 _succEq tailC
                  injection tailC with _l1 _l2 _l3 scrutineeEq _tailD
                  exact scrutineeIH sigma scrutineeEq
  | natRec _scrutineeNeutral scrutineeIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_natRec := hroot.symm
          subst hgen
          cases children with
          | childCons motiveChild restA =>
            cases restA with
            | childCons zeroChild restB =>
              cases restB with
              | childCons succChild restC =>
                cases restC with
                | childCons scrutineeChild nilChildren =>
                  cases nilChildren
                  rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                    (.childCons motiveChild (.childCons zeroChild
                      (.childCons succChild (.childCons scrutineeChild .childNil))))] at hEq
                  injection hEq with _scopeEq _genEq _payloadEq childrenEq
                  injection childrenEq with _i1 _i2 _i3 _motiveEq tailA
                  injection tailA with _j1 _j2 _j3 _zeroEq tailB
                  injection tailB with _k1 _k2 _k3 _succEq tailC
                  injection tailC with _l1 _l2 _l3 scrutineeEq _tailD
                  exact scrutineeIH sigma scrutineeEq
  | listElim _scrutineeNeutral scrutineeIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_listElim := hroot.symm
          subst hgen
          cases children with
          | childCons motiveChild restA =>
            cases restA with
            | childCons nilBranchChild restB =>
              cases restB with
              | childCons consBranchChild restC =>
                cases restC with
                | childCons scrutineeChild nilChildren =>
                  cases nilChildren
                  rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                    (.childCons motiveChild (.childCons nilBranchChild
                      (.childCons consBranchChild (.childCons scrutineeChild .childNil))))] at hEq
                  injection hEq with _scopeEq _genEq _payloadEq childrenEq
                  injection childrenEq with _i1 _i2 _i3 _motiveEq tailA
                  injection tailA with _j1 _j2 _j3 _nilEq tailB
                  injection tailB with _k1 _k2 _k3 _consEq tailC
                  injection tailC with _l1 _l2 _l3 scrutineeEq _tailD
                  exact scrutineeIH sigma scrutineeEq
  | optionMatch _scrutineeNeutral scrutineeIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_optionMatch := hroot.symm
          subst hgen
          cases children with
          | childCons motiveChild restA =>
            cases restA with
            | childCons noneBranchChild restB =>
              cases restB with
              | childCons someBranchChild restC =>
                cases restC with
                | childCons scrutineeChild nilChildren =>
                  cases nilChildren
                  rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                    (.childCons motiveChild (.childCons noneBranchChild
                      (.childCons someBranchChild (.childCons scrutineeChild .childNil))))] at hEq
                  injection hEq with _scopeEq _genEq _payloadEq childrenEq
                  injection childrenEq with _i1 _i2 _i3 _motiveEq tailA
                  injection tailA with _j1 _j2 _j3 _noneEq tailB
                  injection tailB with _k1 _k2 _k3 _someEq tailC
                  injection tailC with _l1 _l2 _l3 scrutineeEq _tailD
                  exact scrutineeIH sigma scrutineeEq
  | eitherMatch _scrutineeNeutral scrutineeIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_eitherMatch := hroot.symm
          subst hgen
          cases children with
          | childCons motiveChild restA =>
            cases restA with
            | childCons leftBranchChild restB =>
              cases restB with
              | childCons rightBranchChild restC =>
                cases restC with
                | childCons scrutineeChild nilChildren =>
                  cases nilChildren
                  rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                    (.childCons motiveChild (.childCons leftBranchChild
                      (.childCons rightBranchChild (.childCons scrutineeChild .childNil))))] at hEq
                  injection hEq with _scopeEq _genEq _payloadEq childrenEq
                  injection childrenEq with _i1 _i2 _i3 _motiveEq tailA
                  injection tailA with _j1 _j2 _j3 _leftEq tailB
                  injection tailB with _k1 _k2 _k3 _rightEq tailC
                  injection tailC with _l1 _l2 _l3 scrutineeEq _tailD
                  exact scrutineeIH sigma scrutineeEq
  | idJ _witnessNeutral witnessIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_idJ := hroot.symm
          subst hgen
          cases children with
          | childCons motiveChild restA =>
            cases restA with
            | childCons baseCaseChild restB =>
              cases restB with
              | childCons witnessChild nilChildren =>
                cases nilChildren
                rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                  (.childCons motiveChild (.childCons baseCaseChild
                    (.childCons witnessChild .childNil)))] at hEq
                injection hEq with _scopeEq _genEq _payloadEq childrenEq
                injection childrenEq with _i1 _i2 _i3 _motiveEq tailA
                injection tailA with _j1 _j2 _j3 _baseEq tailB
                injection tailB with _k1 _k2 _k3 witnessEq _tailC
                exact witnessIH sigma witnessEq
  | idStrictRec _witnessNeutral witnessIH =>
      intro preimage sigma hEq
      cases preimage with
      | mkGen generator payload children =>
        by_cases hVar : generator = .gen_var
        · subst hVar; exact payload.elim0
        · have hroot := RawTerm.subst_rootGenerator_of_not_var sigma
            (term := .mkGen generator payload children) hVar
          rw [hEq] at hroot
          have hgen : generator = Generator.gen_idStrictRec := hroot.symm
          subst hgen
          cases children with
          | childCons motiveChild restA =>
            cases restA with
            | childCons baseCaseChild restB =>
              cases restB with
              | childCons witnessChild nilChildren =>
                cases nilChildren
                rw [RawTerm.subst_mkGen_of_ne_var sigma hVar payload
                  (.childCons motiveChild (.childCons baseCaseChild
                    (.childCons witnessChild .childNil)))] at hEq
                injection hEq with _scopeEq _genEq _payloadEq childrenEq
                injection childrenEq with _i1 _i2 _i3 _motiveEq tailA
                injection tailA with _j1 _j2 _j3 _baseEq tailB
                injection tailB with _k1 _k2 _k3 witnessEq _tailC
                exact witnessIH sigma witnessEq

end FX1Poly.Core
