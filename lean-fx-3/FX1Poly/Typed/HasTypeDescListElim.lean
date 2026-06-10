import FX1Poly.Typed.HasTypeDescListIntro
import FX1Poly.Typed.ListElimComputingCanonicity
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Typed/HasTypeDescListElim — the recursive List eliminator judgment + typed SHAPE-5
    ι-computation (CAN-2 / DI-5g: closes the DI-5 eliminator track).

CAN-1 (`HasTypeDescNatElim`) broke the recursive-eliminator engine-separation wall with the
3-arm mixed-engine judgment.  `listElim` is the SHAPE-5 eliminator — the deepest ι in the
substrate: `listElim(motive, cons h t, nb, cb) ↝ app (app (app cb h) t) (listElim motive t nb cb)`
(`Step.iotaListElimCons`), a TRIPLE app-chain (one curried argument per cons-payload piece plus
the recursive call).  Phase-Z motive shape: `gen_listElim` is arity 4, `binderShifts =
[1, 0, 0, 0]`, children `(motive, nilBranch, consBranch, scrutinee)` with the motive a term under
one binder; the `listElimIntro` ctor carries the motive structurally with NO typing premise (the
non-dependent rule's branches stay typed as before), and the cons ι THREADS the motive into the
recursive call (unlike the nil ι, which discards it).

## How SHAPE-5 distributes over the engines

The cons payload splits across engines: the HEAD is GROWN-typed (`listConsIntro` takes
`headTyped : HasTypeDescPi … headValue elementType`) while the TAIL is LIST-INTRO-typed (the
recursive premise).  So the triple chain needs only ONE new mixed arm:

  * innermost `app cb h` — both parts grown-typed: plain `HasTypeDescPi.piElim` +
    `weaken_subst_singleton` collapse (the eitherMatch pattern), NO new arm;
  * middle `app (app cb h) t` — grown function × DATA-ENGINE tail: the mixed arm
    (`mixedTailApplication`), output `C → C` baked in;
  * outer `app … (listElim t nb cb)` — both parts typed by THIS judgment: the recursive arm
    (`recursiveResultApplication`).

The cons branch inhabits the 3-arg curried step type `A → List(A) → C → C`
(`listStepFunctionType`).

★★ `listElimConsIotaComputesTyped`: a typed `listElim` on `cons(h, t)` ι-steps by SHAPE-5 and
the reduct is typed at `C` — `recursiveResultApplication (mixedTailApplication (piElim …) …)
(listElimIntro …)`, the recursive call typed at the TAIL.  Nil case + honest 3-shape closed
forms included.  With CAN-1 this completes DI-5 (#1047): every live eliminator family
(bool/either/option/Σ/id/nat/list) has a standalone typed judgment with typed ι-computation.

Constructor-side as the whole DI-5 family (SR-free, propext-free); full SR is CAN-3.

## Zero-axiom

A three-arm strictly-positive inductive; ι theorems are direct constructions (the innermost
`piElim` collapse is the only rewrite); shape inversion is a free-index `cases` with `rfl`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The 3-arg curried step-function type `A → List(A) → C → C` the cons branch of a list
eliminator inhabits (every codomain weakened past its binder). -/
def listStepFunctionType {scope : Nat} (elementType resultType : RawTerm scope) : RawTerm scope :=
  piTyCodeCell elementType
    (RawTerm.weaken
      (piTyCodeCell (listTypeCell elementType)
        (RawTerm.weaken (piTyCodeCell resultType (RawTerm.weaken resultType)))))

/-- The partial-application type `List(A) → C → C` — what remains after the cons branch consumes
the head. -/
def listTailStepType {scope : Nat} (elementType resultType : RawTerm scope) : RawTerm scope :=
  piTyCodeCell (listTypeCell elementType)
    (RawTerm.weaken (piTyCodeCell resultType (RawTerm.weaken resultType)))

/-- **The recursive List eliminator judgment.**  The CAN-1 mixed-engine template at SHAPE-5:
the eliminator cell, the cross-engine tail application (grown partial function × DATA-ENGINE
tail — the rule `piElim` cannot express), and the recursive result application (both parts
typed by this judgment). -/
inductive HasTypeDescListElim (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | listElimIntro {scope : Nat} (context : TypingContext profile scope)
      (motive : RawTerm (scope + 1))
      (scrutinee nilBranch consBranch elementType resultType : RawTerm scope)
      (scrutineeTyped :
        HasTypeDescListIntro profile context scrutinee (listTypeCell elementType))
      (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
      (consBranchTyped : HasTypeDescPi profile context consBranch
        (listStepFunctionType elementType resultType)) :
      HasTypeDescListElim profile context
        (listElimCell motive scrutinee nilBranch consBranch) resultType
  | mixedTailApplication {scope : Nat} (context : TypingContext profile scope)
      (partialFunction tailList elementType resultType : RawTerm scope)
      (partialFunctionTyped : HasTypeDescPi profile context partialFunction
        (listTailStepType elementType resultType))
      (tailTyped :
        HasTypeDescListIntro profile context tailList (listTypeCell elementType)) :
      HasTypeDescListElim profile context (appCell partialFunction tailList)
        (piTyCodeCell resultType (RawTerm.weaken resultType))
  | recursiveResultApplication {scope : Nat} (context : TypingContext profile scope)
      (stepFunction recursiveCall resultType : RawTerm scope)
      (stepFunctionTyped : HasTypeDescListElim profile context stepFunction
        (piTyCodeCell resultType (RawTerm.weaken resultType)))
      (recursiveCallTyped : HasTypeDescListElim profile context recursiveCall resultType) :
      HasTypeDescListElim profile context (appCell stepFunction recursiveCall) resultType

/-- **★ Closed forms: a listElim-typed subject is the eliminator cell or an application** —
the honest 3-shape disjunction of the recursive-eliminator template.  Free-index three-arm
`cases`. -/
theorem HasTypeDescListElim.subjectShape {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescListElim profile context subject classifier) :
    (∃ (motive : RawTerm (scope + 1)) (scrutinee nilBranch consBranch : RawTerm scope),
        subject = listElimCell motive scrutinee nilBranch consBranch) ∨
      (∃ functionPart argumentPart : RawTerm scope,
        subject = appCell functionPart argumentPart) := by
  cases derivation with
  | listElimIntro motive scrutinee nilBranch consBranch _eT _rT _sT _nT _cT =>
      exact Or.inl ⟨motive, scrutinee, nilBranch, consBranch, rfl⟩
  | mixedTailApplication partialFunction tailList _eT _rT _pT _tT =>
      exact Or.inr ⟨partialFunction, tailList, rfl⟩
  | recursiveResultApplication stepFunction recursiveCall _rT _fT _cT =>
      exact Or.inr ⟨stepFunction, recursiveCall, rfl⟩

/-- **★ Typed ι-computation (listElim, nil case).**  A typed `listElim` on `nil` ι-reduces to
the nil branch (`Step.iotaListElimNil`, branch selection), typed at `C` by hypothesis. -/
theorem listElimNilIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (nilBranch consBranch elementType resultType : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementTypeFormed :
      HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag))
    (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
    (consBranchTyped : HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType)) :
    HasTypeDescListElim profile context
      (listElimCell motive listNilCell nilBranch consBranch) resultType ∧
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    HasTypeDescPi profile context nilBranch resultType :=
  ⟨HasTypeDescListElim.listElimIntro context motive listNilCell nilBranch consBranch elementType
      resultType
      (HasTypeDescListIntro.listNilIntro context elementType elementLevel flag
        elementTypeFormed)
      nilBranchTyped consBranchTyped,
    Step.iotaListElimNil, nilBranchTyped⟩

/-- **★★ Typed SHAPE-5 ι-computation (listElim, cons case)** — the CAN-2 headline and the
deepest typed ι in the kernel.  A typed `listElim` on `cons(h, t)` ι-reduces to the TRIPLE
app-chain `app (app (app cb h) t) (listElim t nb cb)` (`Step.iotaListElimCons`), and the
reduct is typed at `C`: the innermost application by plain `piElim` (head and branch both
grown-typed) with the non-dependent collapse, the middle by the cross-engine
`mixedTailApplication` (DATA-engine tail), the outer by `recursiveResultApplication` with the
RECURSIVE CALL typed by `listElimIntro` at the tail.  Constructor-side: SR-free,
propext-free. -/
theorem listElimConsIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (headValue tailList nilBranch consBranch elementType resultType : RawTerm scope)
    (headTyped : HasTypeDescPi profile context headValue elementType)
    (tailTyped : HasTypeDescListIntro profile context tailList (listTypeCell elementType))
    (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
    (consBranchTyped : HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType)) :
    HasTypeDescListElim profile context
      (listElimCell motive (listConsCell headValue tailList) nilBranch consBranch) resultType ∧
    Step (listElimCell motive (listConsCell headValue tailList) nilBranch consBranch)
      (appCell (appCell (appCell consBranch headValue) tailList)
        (listElimCell motive tailList nilBranch consBranch)) ∧
    HasTypeDescListElim profile context
      (appCell (appCell (appCell consBranch headValue) tailList)
        (listElimCell motive tailList nilBranch consBranch)) resultType := by
  refine
    ⟨HasTypeDescListElim.listElimIntro context motive (listConsCell headValue tailList) nilBranch
        consBranch elementType resultType
        (HasTypeDescListIntro.listConsIntro context headValue tailList elementType
          headTyped tailTyped)
        nilBranchTyped consBranchTyped,
      Step.iotaListElimCons, ?_⟩
  -- innermost `app cb h`: both grown-typed, so plain piElim; the non-dependent codomain
  -- collapses to the partial-application type `List(A) → C → C`.
  have innerApplicationTyped := HasTypeDescPi.piElim consBranchTyped headTyped
  have codomainCollapses :
      (RawTerm.weaken (piTyCodeCell (listTypeCell elementType)
          (RawTerm.weaken (piTyCodeCell resultType (RawTerm.weaken resultType))))).subst0
          headValue
        = piTyCodeCell (listTypeCell elementType)
            (RawTerm.weaken (piTyCodeCell resultType (RawTerm.weaken resultType))) :=
    RawTerm.weaken_subst_singleton _ headValue
  rw [codomainCollapses] at innerApplicationTyped
  -- middle: the cross-engine tail application; outer: the recursive result application with
  -- the recursive call typed by `listElimIntro` at the tail.
  exact HasTypeDescListElim.recursiveResultApplication context
    (appCell (appCell consBranch headValue) tailList)
    (listElimCell motive tailList nilBranch consBranch) resultType
    (HasTypeDescListElim.mixedTailApplication context
      (appCell consBranch headValue) tailList elementType resultType
      innerApplicationTyped tailTyped)
    (HasTypeDescListElim.listElimIntro context motive tailList nilBranch consBranch elementType
      resultType tailTyped nilBranchTyped consBranchTyped)

end FX1Poly.Typed
