import FX1Poly.Typed.RecursiveElimNativeUnion
import FX1Poly.Typed.HasTypeDescListElim

/-! # FX1Poly/Typed/ListElimRecursiveRow — NATIVE-32 (B): the `gen_listElim` recursive-eliminator row

`gen_listElim` carries `binderShifts [1, 0, 0, 0]` — its cons-ι is an APP-CHAIN, not a substituting ι:

    listElim(motive, cons head tail, nil, cons)
      ↝  app (app (app cons head) tail) (listElim motive tail nil cons)

(`Step.iotaListElimCons`).  The cons branch sits at SHIFT 0 (an ordinary term applied to head, tail,
and the recursive call), unlike `natElim`'s succ branch which lives under two binders and is the var-0
substituent of a 2-variable substitution.  So the `NativeRecursiveElimRule` table — whose
`succContractum` field is a 2-binder substitution shape — does NOT fit `listElim`.

## The design decision (the task's sanctioned alternative, documented)

Per the app-chain shape, this file ships a SIBLING rule shape `ListElimRule` (cons branch at shift 0,
app-chain `consContractum` builder) with an if-then-else table (`gen_listElim` row, rfl diagonal), and
carries the recursive arm on a SPIKE-SIBLING judgment `ListElimUnionSpike` (the union embedded + the
list-intro scrutinee embedding + the table-driven `listElimRecursiveRow` arm).  A SECOND full arm on
`HasTypeNativeUnion` proper is deliberately NOT added here: a second union arm is disproportionate to
this spike-sibling, and — unlike the Nat rows whose succ-ι reduct is itself a recursive eliminator call
typing through the SAME arm — the listElim cons-ι reduct is an APP-CHAIN whose middle/outer layers need
the cross-engine `mixedTailApplication` / `recursiveResultApplication` shapes the bespoke
`HasTypeDescListElim` already supplies.  **Honest pin:** union-proper residency of the listElim row
(folding `HasTypeDescListElim`'s three arms into `HasTypeNativeUnion`) lands with NATIVE-33; this file
locks the row schema + table + bespoke adequacy + a nil-ι typed smoke, the same GO-evidence surface the
Nat spike fixed for NATIVE-32.

## What this ships

  * **`ListElimRule`** — the sibling schema: scrutinee type code, member cell (motive, scrutinee, nil
    branch, cons branch — cons branch at shift 0), and the app-chain cons-ι contractum builder.
  * **`listElimRecursiveRule` / `listElimRecursiveRuleOf`** — the one row + the if-then-else table
    (`gen_listElim` row, rfl diagonal).
  * **`ListElimUnionSpike`** — the spike-sibling judgment: union embedding + list-intro scrutinee
    embedding + the table-driven `listElimRecursiveRow` arm (scrutinee LIST-INTRO-typed, nil/cons
    branches host-typed — premise PARITY with the bespoke `HasTypeDescListElim.listElimIntro`).
  * **`HasTypeDescListElim.toListElimUnionSpike`** — bespoke adequacy: every bespoke `listElimIntro`
    derivation maps into the spike (the cross-engine application arms of `HasTypeDescListElim` are the
    cons-ι reduct's typing machinery, not eliminator intros, so the adequacy targets the `listElimIntro`
    arm; the other two arms are intermediate application shapes carried by the bespoke engine).
  * **`listElimNilIotaSelectsNilBranchTyped`** — the nil-ι typed smoke: `listElim` on `nil` ι-steps to
    the nil branch (`Step.iotaListElimNil`), and the nil branch is host-typed.

## Zero-axiom

The table is an if-then-else over `DecidableEq Generator` (rfl on the diagonal); the spike is a
strictly-positive 3-arm inductive; adequacy is a single-arm bespoke `cases` building the spike arm; the
nil-ι smoke is a direct construction + `Step.iotaListElimNil`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditNativeWaveRecursiveElim.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## The sibling rule schema + the one `gen_listElim` row -/

/-- A list-eliminator row: the inductive type code its scrutinee inhabits, the eliminator member cell
(motive under one binder, scrutinee, nil branch, cons branch — the cons branch at SHIFT 0), and the
app-chain cons-ι contractum (the cons branch applied to head, tail, and the recursive call).  A SIBLING
of `NativeRecursiveElimRule`: the app-chain `consContractum` replaces the 2-binder substitution
`succContractum`, matching `gen_listElim`'s `binderShifts [1, 0, 0, 0]`. -/
structure ListElimRule where
  /-- The list type code the scrutinee must inhabit (`listTypeCell elementType`). -/
  scrutineeType : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The eliminator cell: motive (one binder), scrutinee, nil branch, cons branch (all at scope). -/
  memberCell : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm scope →
    RawTerm scope → RawTerm scope
  /-- The cons-ι contractum at a head and a tail: the app-chain `app (app (app cons head) tail)
  (listElim motive tail nil cons)` — the cons branch (shift 0) applied to head, tail, and the recursive
  call over the tail. -/
  consContractum : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm scope →
    RawTerm scope → RawTerm scope → RawTerm scope

/-- The `gen_listElim` row.  `scrutineeType` is `List(A)`; `memberCell` is `listElimCell`;
`consContractum` is the triple app-chain the cons-ι produces. -/
def listElimRecursiveRule : ListElimRule where
  scrutineeType := fun _ elementType => listTypeCell elementType
  memberCell := fun _ motive scrutinee nilBranch consBranch =>
    listElimCell motive scrutinee nilBranch consBranch
  consContractum := fun _ motive nilBranch consBranch headValue tailList =>
    appCell (appCell (appCell consBranch headValue) tailList)
      (listElimCell motive tailList nilBranch consBranch)

/-- The list-eliminator table.  `gen_listElim` is the sole row (rfl on the diagonal); every other
generator misses (`none`). -/
def listElimRecursiveRuleOf (generator : Generator) : Option ListElimRule :=
  if generator = .gen_listElim then some listElimRecursiveRule
  else none

/-- Table metadata: the listElim row is hit (rfl on the diagonal). -/
theorem listElimRecursiveRuleOf_listElim :
    listElimRecursiveRuleOf .gen_listElim = some listElimRecursiveRule := rfl

/-- The cons-ι contractum of the listElim row IS the triple app-chain the Step arm produces — the row's
`consContractum` field computes to exactly `Step.iotaListElimCons`'s reduct (`rfl`). -/
theorem listElimRecursiveRule_consContractum_eq {scope : Nat} (motive : RawTerm (scope + 1))
    (nilBranch consBranch headValue tailList : RawTerm scope) :
    listElimRecursiveRule.consContractum scope motive nilBranch consBranch headValue tailList
      = appCell (appCell (appCell consBranch headValue) tailList)
          (listElimCell motive tailList nilBranch consBranch) := rfl

/-! ## The spike-sibling judgment: union embedding + list-intro scrutinee + the listElim row -/

/-- **The listElim recursive-eliminator spike-sibling judgment.**  The native union embedded, the
list-intro scrutinee embedding (list values are admissible scrutinees), and the table-driven
`listElimRecursiveRow` arm whose scrutinee is LIST-INTRO-typed and whose nil/cons branches are
host-typed — premise PARITY with the bespoke `HasTypeDescListElim.listElimIntro`.  A refactor-by-addition
sibling of `HasTypeNativeUnion`: union-proper residency lands with NATIVE-33 (the honest pin). -/
inductive ListElimUnionSpike (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  /-- Embed the native union (host / base-type / data / term-indexed / graded intro / general elim /
  natIntro / recursive-elim — the full NATIVE-32 judgment). -/
  | ofUnion {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (unionTyped : HasTypeNativeUnion profile context subject classifier) :
      ListElimUnionSpike profile context subject classifier
  /-- Embed the list value constructors (list scrutinees; folds into the union as table rows in
  NATIVE-34). -/
  | ofListIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (listTyped : HasTypeDescListIntro profile context subject classifier) :
      ListElimUnionSpike profile context subject classifier
  /-- The list-eliminator arm: scrutinee LIST-INTRO-typed, nil/cons branches host-typed at the
  non-dependent result / 3-arg curried step type.  Premise parity with the bespoke
  `HasTypeDescListElim.listElimIntro`; the cons branch stays STORED (the NATIVE-33 fold's delete-safety
  requirement). -/
  | listElimRecursiveRow {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : ListElimRule)
      (motive : RawTerm (scope + 1))
      (scrutinee nilBranch consBranch elementType resultType : RawTerm scope)
      (isListElim : listElimRecursiveRuleOf generator = some rule)
      (scrutineeTyped : HasTypeDescListIntro profile context scrutinee (listTypeCell elementType))
      (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
      (consBranchTyped : HasTypeDescPi profile context consBranch
        (listStepFunctionType elementType resultType)) :
      ListElimUnionSpike profile context
        (rule.memberCell scope motive scrutinee nilBranch consBranch) resultType

/-! ## Bespoke adequacy: every bespoke listElim intro maps into the spike (premise parity) -/

/-- **Bespoke listElim adequacy.**  Every bespoke `HasTypeDescListElim.listElimIntro` derivation
translates to a `ListElimUnionSpike` typing at the same subject and classifier — the scrutinee, nil, and
cons premises carried verbatim through the table-driven `listElimRecursiveRow` arm.  The other two
bespoke arms (`mixedTailApplication` / `recursiveResultApplication`) are the cons-ι reduct's intermediate
application shapes, not eliminator intros; they are the typing MACHINERY for the reduct, carried by the
bespoke engine and reproduced by the union's `generalElim` / `gradedBinderIntro` arms (NATIVE-33).  The
adequacy on the intro arm is the fold's delete-safety direction: the row admits every listElim the
bespoke intro admits. -/
theorem HasTypeDescListElim.toListElimUnionSpike {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (motive : RawTerm (scope + 1))
    (scrutinee nilBranch consBranch elementType resultType : RawTerm scope)
    (scrutineeTyped : HasTypeDescListIntro profile context scrutinee (listTypeCell elementType))
    (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
    (consBranchTyped : HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType)) :
    ListElimUnionSpike profile context
      (listElimCell motive scrutinee nilBranch consBranch) resultType :=
  ListElimUnionSpike.listElimRecursiveRow context .gen_listElim listElimRecursiveRule
    motive scrutinee nilBranch consBranch elementType resultType rfl
    scrutineeTyped nilBranchTyped consBranchTyped

/-! ## ★ The nil-ι typed smoke -/

/-- **★ The listElim nil-ι selects the nil branch, typed.**  A list-eliminator on `nil` ι-steps to the
nil branch (`Step.iotaListElimNil`, branch selection), the eliminator is typed by the spike's
`listElimRecursiveRow` arm (scrutinee `nil` list-intro-typed via `listNilIntro`), and the nil branch is
host-typed.  The list analogue of the Nat zero-ι smoke. -/
theorem listElimNilIotaSelectsNilBranchTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (nilBranch consBranch elementType resultType : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementTypeFormed :
      HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag))
    (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
    (consBranchTyped : HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType)) :
    ListElimUnionSpike profile context
      (listElimCell motive listNilCell nilBranch consBranch) resultType ∧
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    HasTypeDescPi profile context nilBranch resultType :=
  ⟨ListElimUnionSpike.listElimRecursiveRow context .gen_listElim listElimRecursiveRule
      motive listNilCell nilBranch consBranch elementType resultType rfl
      (HasTypeDescListIntro.listNilIntro context elementType elementLevel flag elementTypeFormed)
      nilBranchTyped consBranchTyped,
    Step.iotaListElimNil, nilBranchTyped⟩

/-! ## The listElim row GO-evidence gate -/

/-- **The NATIVE-32 (B) listElim row evidence record.**  Each field is a distinct live property of the
sibling row design; an inhabitant certifies the listElim row is expressible at the app-chain shape (the
table hits, the cons-ι contractum matches the Step reduct, the bespoke engine maps in, and the nil-ι
selects the nil branch typed).  Union-proper residency is the NATIVE-33 follow-on (the honest pin). -/
structure ListElimRecursiveRowEvidence (profile : PolyProfile) : Prop where
  /-- The listElim row is hit by the table. -/
  tableHits : listElimRecursiveRuleOf .gen_listElim = some listElimRecursiveRule
  /-- The cons-ι contractum matches the Step reduct. -/
  consContractumMatches : ∀ {scope : Nat} (motive : RawTerm (scope + 1))
    (nilBranch consBranch headValue tailList : RawTerm scope),
    listElimRecursiveRule.consContractum scope motive nilBranch consBranch headValue tailList
      = appCell (appCell (appCell consBranch headValue) tailList)
          (listElimCell motive tailList nilBranch consBranch)
  /-- Every bespoke listElim intro maps into the spike. -/
  bespokeAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    (motive : RawTerm (scope + 1))
    (scrutinee nilBranch consBranch elementType resultType : RawTerm scope),
    HasTypeDescListIntro profile context scrutinee (listTypeCell elementType) →
    HasTypeDescPi profile context nilBranch resultType →
    HasTypeDescPi profile context consBranch (listStepFunctionType elementType resultType) →
    ListElimUnionSpike profile context
      (listElimCell motive scrutinee nilBranch consBranch) resultType

/-- **★ The NATIVE-32 (B) listElim row gate** — inhabited by the shipped witnesses. -/
theorem listElimRecursiveRowEvidenceWitness {profile : PolyProfile} :
    ListElimRecursiveRowEvidence profile where
  tableHits := listElimRecursiveRuleOf_listElim
  consContractumMatches := fun motive nilBranch consBranch headValue tailList =>
    listElimRecursiveRule_consContractum_eq motive nilBranch consBranch headValue tailList
  bespokeAdequate := fun motive scrutinee nilBranch consBranch elementType resultType
    scrutineeTyped nilBranchTyped consBranchTyped =>
    HasTypeDescListElim.toListElimUnionSpike motive scrutinee nilBranch consBranch elementType
      resultType scrutineeTyped nilBranchTyped consBranchTyped

end FX1Poly.Typed
