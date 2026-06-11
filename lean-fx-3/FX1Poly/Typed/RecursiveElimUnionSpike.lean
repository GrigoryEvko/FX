import FX1Poly.Typed.HasTypeNativeUnion
import FX1Poly.Typed.HasTypeDescNatElim

/-! # FX1Poly/Typed/RecursiveElimUnionSpike — NATIVE-27 [GO/NO-GO]: recursive-eliminator rows
    on the seed union — VERDICT: **GO**

THE QUESTION (the campaign's declared risk class): can the RECURSIVE eliminators (natElim /
natRec) be expressed as table rows over a union-style judgment whose premises are RECURSIVE in
that judgment, such that the succ-ι reduct — whose var-0 substituent is the recursive eliminator
call itself — types INTERNALLY, with no `reductTyped` escape-hatch premise?

Every prior engine failed exactly here (the NATIVE-04 residual): the bespoke
`HasTypeDescNatElim` ships its succ-ι headline `natElimSuccIotaComputesTyped` CONDITIONAL on
`reductTyped`, because the reduct's inner substituent is the recursive `natElimCell`, which the
grown engine deliberately does not type — so `HasTypeDescPi.substPairUnderTwoBindings`
(TYPED-SUBSTPAIR) cannot fire at the ι instance within any single shipped judgment.

## The GO construction

  * **`RecursiveElimRule`** — the dedicated recursive-eliminator row schema (scrutinee type code,
    member cell, succ-ι contractum), with `natElimRecursiveRule` / `natRecRecursiveRule` rows and
    the `recursiveElimRuleOf` table.  This FIXES THE SCHEMA STYLE for NATIVE-28/32: a dedicated
    per-premise-shape table, not a `GeneralElimRule` overload.
  * **`RecursiveElimUnionSpike`** — the seed union (`HasTypeNativeUnion`) extended by one
    table-driven recursive-eliminator arm whose scrutinee and base-branch premises are recursive
    in the SPIKE itself, plus the `HasTypeDescNatIntro` embedding (numeral scrutinees).  A
    refactor-by-addition sibling: nothing in the shipped union is touched; NATIVE-32 integrates
    the arm into `HasTypeNativeUnion` proper using this spike as the locked design.
  * **★ `recursiveElimSuccIotaDischargedInternally`** — THE GO TEST.  On the
    inductive-hypothesis-return branch family (`succBranch = var 0`, the branch that RETURNS the
    recursive call — the exact minimal instance of the NATIVE-04 obstruction, where the reduct IS
    the recursive call and no substitution transport is needed), the succ-ι fires and the reduct
    types INTERNALLY through the spike's own recursive arm.  No `reductTyped` premise.  The
    2-variable substitution computes the contractum to the recursive call by `rfl`
    (`RawTermSubst.cons` head at var 0 — the banked innermost-var idiom).
  * **★ `recursiveElimClosedComputationFullyTyped`** — end-to-end: the closed eliminator
    `natElim(Bool, true, var 0, succ zero)` is typed, ι-steps to `natElim(Bool, true, var 0, zero)`
    (typed), ι-steps to `true` (typed) — a 2-step typed computation chain through the recursion
    loop, every link in ONE judgment.
  * **★ `spikeTypesEliminatorScrutinee` / `bespokeRejectsEliminatorScrutinee`** — the spike types
    `natElim(..., natElim(...))` (an eliminator whose SCRUTINEE is another eliminator — recursion
    on a computed number), which the bespoke engine PROVABLY rejects (its scrutinee premise is
    `HasTypeDescNatIntro`, whose subjects are natZero/natSucc-headed — head clash).
  * **Adequacy** (`HasTypeDescNatElim.toRecursiveElimUnionSpike` + the natRec twin): every bespoke
    derivation maps into the spike — premise PARITY (the NATIVE-33 fold's delete-safety
    direction).  The motive and succ branch stay STORED exactly as the bespoke stores them;
    strengthening them to typed premises is a deliberate post-fold decision gated on the union
    substitution lemma (NATIVE-37), because a premised branch would break this adequacy.

## Honest scope (the named residuals — none threatens GO)

  1. GENERAL succ branches: the IH-return family isolates and discharges the recursion-closure
     obstruction; an ARBITRARY branch's reduct typing additionally needs the 2-variable typed
     substitution transport restated OVER THE UNION (`substPairUnderTwoBindings` exists for the
     host engine, but its premises are host typings and the recursive call is never host-typed).
     That is standard-machinery work (NATIVE-37), not a schema obstruction.
  2. `gen_listElim` carries `binderShifts [1, 0, 0, 0]` — its cons-ι is an APP-CHAIN, not a
     substitution, so its row has a shift-0 step-branch field; it joins the table in NATIVE-32.
  3. The rows keep the bespoke's non-dependent `resultType` (the motive is stored).  The
     dependent output (`subst0 motive scrutinee`) is the NATIVE-28 schema question; the verdict
     fixed there is: extend THIS table style with a motive-applied output field.

## Zero-axiom

The table is an if-then-else over `DecidableEq Generator` (rfl on the diagonal); the spike is a
strictly-positive 4-arm inductive (two completed-inductive embeddings, one recursive arm); the GO
theorems are direct constructions + `Step.iotaNatElimSucc/Zero` with the contractum computing by
`rfl`; the bespoke rejection is a free-index inversion + `injections` drilling + head-generator
no-confusion.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## The recursive-eliminator row schema + the two Nat rows -/

/-- A recursive-eliminator row: the inductive type code its scrutinee inhabits, the eliminator
member cell (motive, base branch, two-binder step branch, scrutinee), and the succ-ι contractum
(the step branch with the recursive call substituted at var 0 and the predecessor at var 1).
Dedicated schema (NOT a `GeneralElimRule` overload): the recursive premise shape — a scrutinee at
a FIXED type code plus a base branch at the result type, with the step branch stored under two
binders — matches no other table's premise telescope. -/
structure RecursiveElimRule where
  /-- The inductive type code the scrutinee must inhabit (`natTypeCell` for both Nat rows). -/
  scrutineeType : (scope : Nat) → RawTerm scope
  /-- The eliminator cell: motive (one binder), base branch, step branch (two binders:
  predecessor outer, inductive hypothesis inner), scrutinee. -/
  memberCell : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm (scope + 2) →
    RawTerm scope → RawTerm scope
  /-- The succ-ι contractum at a predecessor: the step branch with the recursive call at var 0
  and the predecessor at var 1. -/
  succContractum : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm (scope + 2) →
    RawTerm scope → RawTerm scope

/-- The `gen_natElim` row. -/
def natElimRecursiveRule : RecursiveElimRule where
  scrutineeType := fun _ => natTypeCell
  memberCell := fun _ => natElimCell
  succContractum := fun _ => natElimSuccContractum

/-- The `gen_natRec` row (the dependent-recursor twin — identical substrate metadata). -/
def natRecRecursiveRule : RecursiveElimRule where
  scrutineeType := fun _ => natTypeCell
  memberCell := fun _ => natRecCell
  succContractum := fun _ => natRecSuccContractum

/-- The recursive-eliminator table.  `gen_listElim` joins in NATIVE-32 with a shift-0
step-branch row shape (its cons-ι is an app-chain, not a substitution). -/
def recursiveElimRuleOf (generator : Generator) : Option RecursiveElimRule :=
  if generator = .gen_natElim then some natElimRecursiveRule
  else if generator = .gen_natRec then some natRecRecursiveRule
  else none

/-- Table metadata: the natElim row is hit (rfl on the diagonal). -/
theorem recursiveElimRuleOf_natElim :
    recursiveElimRuleOf .gen_natElim = some natElimRecursiveRule := rfl

/-- Table metadata: the natRec row is hit. -/
theorem recursiveElimRuleOf_natRec :
    recursiveElimRuleOf .gen_natRec = some natRecRecursiveRule := rfl

/-! ## The spike judgment: the seed union + the recursive-eliminator arm -/

/-- **The NATIVE-27 spike judgment** — the seed union extended by the table-driven
recursive-eliminator arm with RECURSIVE premises, plus the Nat value-constructor embedding
(numeral scrutinees).  A refactor-by-addition sibling of `HasTypeNativeUnion`: the shipped union
is untouched; NATIVE-32 integrates this arm into the union proper with this spike as the locked
design.  The motive and step branch are STORED (premise parity with the bespoke
`HasTypeDescNatElim` — the NATIVE-33 fold's delete-safety requirement). -/
inductive RecursiveElimUnionSpike (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  /-- Embed the seed union (host / base-type / data / term-indexed / graded intro / general
  elim — the full NATIVE-25 judgment). -/
  | ofUnion {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (unionTyped : HasTypeNativeUnion profile context subject classifier) :
      RecursiveElimUnionSpike profile context subject classifier
  /-- Embed the Nat value constructors (numeral scrutinees; folds into the union as table rows
  in NATIVE-34). -/
  | ofNatIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (natTyped : HasTypeDescNatIntro profile context subject classifier) :
      RecursiveElimUnionSpike profile context subject classifier
  /-- The recursive-eliminator arm: scrutinee and base branch typed by THIS judgment — so a
  recursive call (`natElimCell` at the predecessor) is itself an admissible scrutinee-typed
  subject, closing the loop the bespoke engine could not. -/
  | recursiveElimRow {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : RecursiveElimRule)
      (motive : RawTerm (scope + 1)) (baseBranch : RawTerm scope)
      (stepBranch : RawTerm (scope + 2)) (scrutinee : RawTerm scope)
      (resultType : RawTerm scope)
      (isRecursiveElim : recursiveElimRuleOf generator = some rule)
      (scrutineeTyped : RecursiveElimUnionSpike profile context scrutinee
        (rule.scrutineeType scope))
      (baseBranchTyped : RecursiveElimUnionSpike profile context baseBranch resultType) :
      RecursiveElimUnionSpike profile context
        (rule.memberCell scope motive baseBranch stepBranch scrutinee) resultType

/-! ## Adequacy: every bespoke derivation maps into the spike (premise parity) -/

/-- **Bespoke natElim adequacy.**  Every `HasTypeDescNatElim` derivation translates to a spike
typing at the same subject and classifier — the scrutinee premise through the NatIntro embedding,
the base branch through the union's host embedding.  This is the NATIVE-33 fold's delete-safety
direction: the row admits everything the bespoke admits. -/
theorem HasTypeDescNatElim.toRecursiveElimUnionSpike {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatElim profile context subject classifier) :
    RecursiveElimUnionSpike profile context subject classifier := by
  cases derivation with
  | natElimIntro motive scrutinee zeroBranch succBranch _resultTypeUnified
      scrutineeTyped zeroBranchTyped =>
      exact RecursiveElimUnionSpike.recursiveElimRow _ .gen_natElim natElimRecursiveRule
        motive zeroBranch succBranch scrutinee classifier rfl
        (RecursiveElimUnionSpike.ofNatIntro scrutineeTyped)
        (RecursiveElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown zeroBranchTyped))

/-- **Bespoke natRec adequacy** — the recursor twin. -/
theorem HasTypeDescNatRec.toRecursiveElimUnionSpike {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatRec profile context subject classifier) :
    RecursiveElimUnionSpike profile context subject classifier := by
  cases derivation with
  | natRecIntro motive scrutinee zeroBranch succBranch _resultTypeUnified
      scrutineeTyped zeroBranchTyped =>
      exact RecursiveElimUnionSpike.recursiveElimRow _ .gen_natRec natRecRecursiveRule
        motive zeroBranch succBranch scrutinee classifier rfl
        (RecursiveElimUnionSpike.ofNatIntro scrutineeTyped)
        (RecursiveElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown zeroBranchTyped))

/-! ## ★ THE GO TEST: the succ-ι reduct types internally -/

/-- The inductive-hypothesis-return step branch: `var 0` under the two step-branch binders
(predecessor outer, inductive hypothesis inner) — the branch that RETURNS the recursive call.
The minimal instance of the NATIVE-04 obstruction: its succ-ι reduct IS the recursive eliminator
call, so the reduct typing is exactly the recursion-closure question with no substitution
transport in the way. -/
def inductiveHypothesisReturnBranch (scope : Nat) : RawTerm (scope + 2) :=
  variableCell ⟨0, Nat.succ_pos (scope + 1)⟩

/-- **The 2-variable substitution COMPUTES on the IH-return branch**: the contractum is the
recursive call, definitionally (`RawTermSubst.cons` head at var 0 — the banked innermost-var
idiom). -/
theorem natElimSuccContractum_ihReturn {scope : Nat} (motive : RawTerm (scope + 1))
    (zeroBranch predecessor : RawTerm scope) :
    natElimSuccContractum motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor
      = natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor := rfl

/-- The natRec twin of `natElimSuccContractum_ihReturn`. -/
theorem natRecSuccContractum_ihReturn {scope : Nat} (motive : RawTerm (scope + 1))
    (zeroBranch predecessor : RawTerm scope) :
    natRecSuccContractum motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor
      = natRecCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor := rfl

/-- **★★ THE GO THEOREM (natElim): the succ-ι reduct types INTERNALLY.**  On the IH-return
branch family, for ANY spike-typed predecessor and base branch: the succ-ι fires
(`Step.iotaNatElimSucc`, the contractum computing to the recursive call by `rfl`), and the
reduct — the recursive `natElimCell` at the predecessor — is typed by the spike's own
recursive-eliminator arm.  NO `reductTyped` premise: contrast `natElimSuccIotaComputesTyped`
(HasTypeDescNatElim), which must ASSUME exactly this conclusion because no single prior judgment
contained both the eliminator intro and the recursive call's scrutinee typing.  The NATIVE-04
residual, discharged. -/
theorem recursiveElimSuccIotaDischargedInternally {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (predecessor zeroBranch resultType : RawTerm scope)
    (predecessorTyped : RecursiveElimUnionSpike profile context predecessor natTypeCell)
    (zeroBranchTyped : RecursiveElimUnionSpike profile context zeroBranch resultType) :
    Step
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope)
        (natSuccCell predecessor))
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor) ∧
    RecursiveElimUnionSpike profile context
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor)
      resultType :=
  ⟨natElimSuccContractum_ihReturn motive zeroBranch predecessor ▸ Step.iotaNatElimSucc,
    RecursiveElimUnionSpike.recursiveElimRow context .gen_natElim natElimRecursiveRule
      motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor resultType rfl
      predecessorTyped zeroBranchTyped⟩

/-- **★ The natRec twin of the GO theorem.** -/
theorem recursiveRecSuccIotaDischargedInternally {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (predecessor zeroBranch resultType : RawTerm scope)
    (predecessorTyped : RecursiveElimUnionSpike profile context predecessor natTypeCell)
    (zeroBranchTyped : RecursiveElimUnionSpike profile context zeroBranch resultType) :
    Step
      (natRecCell motive zeroBranch (inductiveHypothesisReturnBranch scope)
        (natSuccCell predecessor))
      (natRecCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor) ∧
    RecursiveElimUnionSpike profile context
      (natRecCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor)
      resultType :=
  ⟨natRecSuccContractum_ihReturn motive zeroBranch predecessor ▸ Step.iotaNatRecSucc,
    RecursiveElimUnionSpike.recursiveElimRow context .gen_natRec natRecRecursiveRule
      motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor resultType rfl
      predecessorTyped zeroBranchTyped⟩

/-! ## ★ End-to-end: a closed 2-step typed computation through the recursion loop -/

/-- **★ The closed eliminator computes through the recursion loop with every link typed.**
`natElim(Bool, true, var 0, succ zero) : Bool` (typed) ι-steps to
`natElim(Bool, true, var 0, zero) : Bool` (typed — the recursive call, typed by the SAME arm)
ι-steps to `true : Bool` (typed).  The first fully-internal typed computation chain of a
recursive eliminator in the campaign: redex, recursive-call reduct, and value all in ONE
judgment. -/
theorem recursiveElimClosedComputationFullyTyped {profile : PolyProfile} :
    RecursiveElimUnionSpike profile (TypingContext.empty : TypingContext profile 0)
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
        (natSuccCell natZeroCell))
      boolTypeCell ∧
    Step
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
        (natSuccCell natZeroCell))
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0) natZeroCell) ∧
    RecursiveElimUnionSpike profile (TypingContext.empty : TypingContext profile 0)
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0) natZeroCell)
      boolTypeCell ∧
    Step
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0) natZeroCell)
      boolTrueCell ∧
    RecursiveElimUnionSpike profile (TypingContext.empty : TypingContext profile 0)
      boolTrueCell boolTypeCell := by
  have zeroScrutineeTyped : RecursiveElimUnionSpike profile
      (TypingContext.empty : TypingContext profile 0) natZeroCell natTypeCell :=
    RecursiveElimUnionSpike.ofNatIntro (HasTypeDescNatIntro.natZeroIntro TypingContext.empty)
  have trueBranchTyped : RecursiveElimUnionSpike profile
      (TypingContext.empty : TypingContext profile 0) boolTrueCell boolTypeCell :=
    RecursiveElimUnionSpike.ofUnion (HasTypeNativeUnion.ofDataIntro
      (HasTypeDescDataIntro.boolTrueTyped TypingContext.empty))
  refine ⟨?_, ?_, ?_, Step.iotaNatElimZero, trueBranchTyped⟩
  · exact RecursiveElimUnionSpike.recursiveElimRow TypingContext.empty .gen_natElim
      natElimRecursiveRule boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
      (natSuccCell natZeroCell) boolTypeCell rfl
      (RecursiveElimUnionSpike.ofNatIntro
        (HasTypeDescNatIntro.natSuccIntro TypingContext.empty natZeroCell
          (HasTypeDescNatIntro.natZeroIntro TypingContext.empty)))
      trueBranchTyped
  · exact natElimSuccContractum_ihReturn boolTypeCell boolTrueCell natZeroCell ▸
      Step.iotaNatElimSucc
  · exact RecursiveElimUnionSpike.recursiveElimRow TypingContext.empty .gen_natElim
      natElimRecursiveRule boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
      natZeroCell boolTypeCell rfl zeroScrutineeTyped trueBranchTyped

/-! ## ★ The spike exceeds the bespoke: eliminator-valued scrutinees -/

/-- A `HasTypeDescNatIntro` subject is natZero- or natSucc-headed (free-index cases). -/
theorem HasTypeDescNatIntro.subjectHeadIsNatValue {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatIntro profile context subject classifier) :
    subject.rootGenerator = .gen_natZero ∨ subject.rootGenerator = .gen_natSucc := by
  cases derivation with
  | natZeroIntro => exact Or.inl rfl
  | natSuccIntro => exact Or.inr rfl

/-- Premise-surfacing inversion of the bespoke natElim engine (free-index single-arm cases):
the subject is the eliminator cell and the scrutinee carries a `HasTypeDescNatIntro` typing. -/
theorem HasTypeDescNatElim.invertPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatElim profile context subject classifier) :
    ∃ (motive : RawTerm (scope + 1)) (zeroBranch scrutinee : RawTerm scope)
      (succBranch : RawTerm (scope + 2)),
        subject = natElimCell motive zeroBranch succBranch scrutinee ∧
        HasTypeDescNatIntro profile context scrutinee natTypeCell ∧
        HasTypeDescPi profile context zeroBranch classifier := by
  cases derivation with
  | natElimIntro motive scrutinee zeroBranch succBranch resultType
      scrutineeTyped zeroBranchTyped =>
      exact ⟨motive, zeroBranch, scrutinee, succBranch, rfl, scrutineeTyped, zeroBranchTyped⟩

/-- **The bespoke engine PROVABLY rejects an eliminator-valued scrutinee**: its scrutinee premise
is `HasTypeDescNatIntro`, whose subjects are natZero/natSucc-headed — a `natElimCell` scrutinee
is a head clash.  This is the judgment-boundary wall, exhibited as a refutation.  The scrutinee
equation is extracted by the banked `mkGen`/`childCons` injection drilling (four outputs at the
`mkGen` level, five per `childCons` level: scope / shift / restShifts / head / tail). -/
theorem bespokeRejectsEliminatorScrutinee {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive innerMotive : RawTerm (scope + 1)) (zeroBranch innerZero : RawTerm scope)
    (succBranch innerSucc : RawTerm (scope + 2)) (innerScrutinee resultType : RawTerm scope) :
    ¬ HasTypeDescNatElim profile context
        (natElimCell motive zeroBranch succBranch
          (natElimCell innerMotive innerZero innerSucc innerScrutinee))
        resultType := by
  intro derivation
  obtain ⟨reconMotive, reconZero, reconScrutinee, reconSucc, subjectEq, scrutineeTyped, _⟩ :=
    derivation.invertPremises
  injection subjectEq with _scopeEq _generatorEq _payloadEq childrenEq
  injection childrenEq with _motiveScopeEq _motiveShiftEq _motiveRestShiftsEq _motiveEq
    zeroRestEq
  injection zeroRestEq with _zeroScopeEq _zeroShiftEq _zeroRestShiftsEq _zeroEq succRestEq
  injection succRestEq with _succScopeEq _succShiftEq _succRestShiftsEq _succEq
    scrutineeRestEq
  injection scrutineeRestEq with _scrScopeEq _scrShiftEq _scrRestShiftsEq scrutineeEq _nilEq
  rw [← scrutineeEq] at scrutineeTyped
  rcases scrutineeTyped.subjectHeadIsNatValue with headClash | headClash
  · exact absurd headClash (by intro headEq; cases headEq)
  · exact absurd headClash (by intro headEq; cases headEq)

/-- **★ The spike TYPES the eliminator-valued scrutinee the bespoke rejects**: the closed term
`natElim(Bool, true, var 0, natElim(Nat, zero, var 0, zero))` — recursion on a COMPUTED number —
typed end-to-end through the recursive arm composing with itself. -/
theorem spikeTypesEliminatorScrutinee {profile : PolyProfile} :
    RecursiveElimUnionSpike profile (TypingContext.empty : TypingContext profile 0)
      (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
        (natElimCell natTypeCell natZeroCell (inductiveHypothesisReturnBranch 0) natZeroCell))
      boolTypeCell :=
  RecursiveElimUnionSpike.recursiveElimRow TypingContext.empty .gen_natElim
    natElimRecursiveRule boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
    (natElimCell natTypeCell natZeroCell (inductiveHypothesisReturnBranch 0) natZeroCell)
    boolTypeCell rfl
    (RecursiveElimUnionSpike.recursiveElimRow TypingContext.empty .gen_natElim
      natElimRecursiveRule natTypeCell natZeroCell (inductiveHypothesisReturnBranch 0)
      natZeroCell natTypeCell rfl
      (RecursiveElimUnionSpike.ofNatIntro
        (HasTypeDescNatIntro.natZeroIntro TypingContext.empty))
      (RecursiveElimUnionSpike.ofNatIntro
        (HasTypeDescNatIntro.natZeroIntro TypingContext.empty)))
    (RecursiveElimUnionSpike.ofUnion (HasTypeNativeUnion.ofDataIntro
      (HasTypeDescDataIntro.boolTrueTyped TypingContext.empty)))

/-! ## The GO verdict gate -/

/-- **The NATIVE-27 GO evidence record.**  Each field is a distinct live property of the
recursive-eliminator row design; an inhabitant certifies the verdict is GO: the rows are
expressible, the bespoke engines map in (premise parity, the fold's delete-safety), the succ-ι
reduct types internally on the recursion-isolating family (the NATIVE-04 residual discharge),
and the spike strictly exceeds the bespoke (eliminator-valued scrutinees). -/
structure RecursiveElimRowGoEvidence (profile : PolyProfile) : Prop where
  /-- Every bespoke natElim derivation maps into the spike. -/
  natElimAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescNatElim profile context subject classifier →
    RecursiveElimUnionSpike profile context subject classifier
  /-- Every bespoke natRec derivation maps into the spike. -/
  natRecAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescNatRec profile context subject classifier →
    RecursiveElimUnionSpike profile context subject classifier
  /-- The succ-ι reduct types internally (no `reductTyped` premise) on the IH-return family. -/
  succIotaInternal : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (predecessor zeroBranch resultType : RawTerm scope),
    RecursiveElimUnionSpike profile context predecessor natTypeCell →
    RecursiveElimUnionSpike profile context zeroBranch resultType →
    Step
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope)
        (natSuccCell predecessor))
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor) ∧
    RecursiveElimUnionSpike profile context
      (natElimCell motive zeroBranch (inductiveHypothesisReturnBranch scope) predecessor)
      resultType
  /-- The spike types the eliminator-valued scrutinee... -/
  exceedsBespoke : RecursiveElimUnionSpike profile (TypingContext.empty : TypingContext profile 0)
    (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
      (natElimCell natTypeCell natZeroCell (inductiveHypothesisReturnBranch 0) natZeroCell))
    boolTypeCell
  /-- ...which the bespoke engine provably rejects. -/
  bespokeRejects : ¬ HasTypeDescNatElim profile
    (TypingContext.empty : TypingContext profile 0)
    (natElimCell boolTypeCell boolTrueCell (inductiveHypothesisReturnBranch 0)
      (natElimCell natTypeCell natZeroCell (inductiveHypothesisReturnBranch 0) natZeroCell))
    boolTypeCell

/-- **★ The NATIVE-27 verdict: GO** — inhabited by the shipped witnesses. -/
theorem recursiveElimRowGoVerdict {profile : PolyProfile} :
    RecursiveElimRowGoEvidence profile where
  natElimAdequate := fun derivation => derivation.toRecursiveElimUnionSpike
  natRecAdequate := fun derivation => derivation.toRecursiveElimUnionSpike
  succIotaInternal := fun context motive predecessor zeroBranch resultType
    predecessorTyped zeroBranchTyped =>
    recursiveElimSuccIotaDischargedInternally context motive predecessor zeroBranch resultType
      predecessorTyped zeroBranchTyped
  exceedsBespoke := spikeTypesEliminatorScrutinee
  bespokeRejects := bespokeRejectsEliminatorScrutinee TypingContext.empty boolTypeCell
    natTypeCell boolTrueCell natZeroCell (inductiveHypothesisReturnBranch 0)
    (inductiveHypothesisReturnBranch 0) natZeroCell boolTypeCell

end FX1Poly.Typed
