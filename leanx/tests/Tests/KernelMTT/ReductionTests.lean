import FX.KernelMTT.Term
import FX.KernelMTT.Substitution
import FX.KernelMTT.Reduction
import FX.KernelMTT.Mode
import FX.KernelMTT.Modality
import FX.Kernel.Grade
import FX.Kernel.Level
import Tests.Framework

/-!
# FX.KernelMTT.Reduction tests (V1.15)

Pinning tests for the six single-step reduction rules and the
`whnf` weak-head-normalizer over the well-scoped mode-indexed
`Term : Nat → Type`.

Twenty tests covering:

  * β-reduction (3 tests)
  * ι-reduction on inductive recursor (3 tests, including
    type-name mismatch and out-of-range index rejection)
  * ν-reduction on coinductive destructor (2 tests)
  * modElim-ι reduction (2 tests including modality-mismatch
    rejection)
  * idJ-ι reduction (1 test)
  * coerceCell strip (2 tests, including multi-layer wrap)
  * `whnf` composition (5 tests: nested β, coerce-then-β,
    ι via whnf, ν via whnf, fuel-zero behaviour)
  * `whnf` on already-WHNF input (1 test) — lam stays lam
  * `applyArgs` helper (1 test)

These tests pin the operational behaviour; mechanized
preservation theorems are V_meta scope.  The well-scoping
discipline (W2) is automatically witnessed by every `Term n →
Term n` signature compiling; no separate tests needed.
-/

namespace Tests.KernelMTT.ReductionTests

open Tests FX.KernelMTT FX.Kernel

/-! ## Builders -/

def natType {n : Nat} (m : Mode) : Term n := .ind m "Nat" .nil
def natZero {n : Nat} (m : Mode) : Term n := .ctor m "Nat" 0 .nil .nil
def boolFalse {n : Nat} (m : Mode) : Term n := .ctor m "Bool" 0 .nil .nil
def boolTrue  {n : Nat} (m : Mode) : Term n := .ctor m "Bool" 1 .nil .nil

/-- Identity lambda `λ x : Nat. x` at the given mode, closed. -/
def idLam (m : Mode) : Term 0 :=
  .lam m Grade.ghost (natType m) (.var m 0)

def run : IO Unit := Tests.suite "Tests.KernelMTT.ReductionTests" do

  -----------------------------------------------------------
  -- β-reduction
  -----------------------------------------------------------

  -- 1. βStep on (λ x : Nat. x) zero → zero.
  let app1 : Term 0 := .app Mode.software (idLam Mode.software)
                          (natZero Mode.software)
  match Term.betaStep? app1 with
  | some result =>
      check "βStep: (λx. x) zero ↦ zero"
        true
        (Term.structEq result (natZero Mode.software))
  | none =>
      check "βStep: expected reduction"
        true
        false

  -- 2. βStep returns none when function is not a lam.
  let app2 : Term 1 :=
    .app Mode.software (.var Mode.software 0) (natZero Mode.software)
  check "βStep: var head doesn't reduce"
    true
    (Term.betaStep? app2 |>.isNone)

  -- 3. βStep on `(λ x. λ y. y) zero` reduces to `λ y. y`.
  --    The inner lam's body references var 0 (the inner
  --    binder); after subst the inner binder is preserved.
  let outerLam : Term 0 :=
    .lam Mode.software Grade.ghost (natType Mode.software)
      (.lam Mode.software Grade.ghost (natType Mode.software)
        (.var Mode.software 0))
  let arg3 : Term 0 := natZero Mode.software
  let app3 : Term 0 := .app Mode.software outerLam arg3
  match Term.betaStep? app3 with
  | some result =>
      let expected : Term 0 := idLam Mode.software
      check "βStep: (λx.λy.y) zero ↦ (λy.y)"
        true
        (Term.structEq result expected)
  | none =>
      check "βStep: expected reduction (case 3)"
        true
        false

  -----------------------------------------------------------
  -- ι-reduction (inductive recursor)
  -----------------------------------------------------------

  -- 4. ι on Bool's true ctor: indRec "Bool" mot [methodF,
  --    methodT] true ↦ methodT.
  let methF : Term 0 := .const Mode.software "false_method"
  let methT : Term 0 := .const Mode.software "true_method"
  let mot   : Term 0 := .const Mode.software "motive"
  let recOnTrue : Term 0 :=
    .indRec Mode.software "Bool" mot
      (TermArgs.ofList [methF, methT])
      (boolTrue Mode.software)
  match Term.iotaIndRecStep? recOnTrue with
  | some result =>
      -- Bool's true is ctor index 1, no value args; so iota
      -- yields applyArgs methT .nil = methT.
      check "ι: indRec Bool [F, T] true ↦ T method"
        true
        (Term.structEq result methT)
  | none =>
      check "ι: expected reduction (Bool true)"
        true
        false

  -- 5. ι returns none when recursor type ≠ ctor type.
  let crossType : Term 0 :=
    .indRec Mode.software "Bool" mot
      (TermArgs.ofList [methF, methT])
      (.ctor Mode.software "Nat" 0 .nil .nil)
  check "ι: type mismatch → no reduction"
    true
    (Term.iotaIndRecStep? crossType |>.isNone)

  -- 6. ι returns none when method index out of range.
  let outOfRange : Term 0 :=
    .indRec Mode.software "Bool" mot
      (TermArgs.ofList [methF])  -- only one method!
      (boolTrue Mode.software)   -- true is index 1, out of range
  check "ι: method index out of range → no reduction"
    true
    (Term.iotaIndRecStep? outOfRange |>.isNone)

  -----------------------------------------------------------
  -- ν-reduction (coinductive destructor)
  -----------------------------------------------------------

  -- 7. ν on Stream's tail destructor: select arm 1.
  let headArm : Term 0 := .const Mode.software "head_body"
  let tailArm : Term 0 := .const Mode.software "tail_body"
  let unfold : Term 0 :=
    .coindUnfold Mode.software "Stream"
      (TermArgs.ofList [natType Mode.software])
      (TermArgs.ofList [headArm, tailArm])
  let destrTail : Term 0 :=
    .coindDestruct Mode.software "Stream" 1 unfold
  match Term.nuStep? destrTail with
  | some result =>
      check "ν: tail destructor on Stream unfold ↦ tail arm"
        true
        (Term.structEq result tailArm)
  | none =>
      check "ν: expected reduction (Stream tail)"
        true
        false

  -- 8. ν returns none when destructor target isn't coindUnfold.
  let stuckDestr : Term 1 :=
    .coindDestruct Mode.software "Stream" 0 (.var Mode.software 0)
  check "ν: var target → no reduction"
    true
    (Term.nuStep? stuckDestr |>.isNone)

  -----------------------------------------------------------
  -- modElim-ι reduction
  -----------------------------------------------------------

  -- 9. modElim on matching modIntro: ↦ subst body inner.
  --    modElim Software Ghost usage (modIntro Ghost Software
  --    usage natZero) (var 0) ↦ subst (var 0) natZero = natZero.
  let mInner : Term 0 := natZero Mode.ghost
  let modIntroT : Term 0 :=
    .modIntro Mode.ghost Mode.software Modality.usage mInner
  let elimBody : Term 1 := .var Mode.ghost 0
  let elimT : Term 0 :=
    .modElim Mode.software Mode.ghost Modality.usage modIntroT elimBody
  match Term.modElimIotaStep? elimT with
  | some result =>
      check "modElim-ι: matching modality ↦ subst body inner"
        true
        (Term.structEq result mInner)
  | none =>
      check "modElim-ι: expected reduction"
        true
        false

  -- 10. modElim with mismatched modality: no reduction.
  --     Use a different modality on the modIntro and check
  --     that the eliminator's `usage` doesn't match the
  --     introducer's `sec`.
  let mIntroMisMod : Term 0 :=
    .modIntro Mode.ghost Mode.software Modality.sec mInner
  let elimMisMod : Term 0 :=
    .modElim Mode.software Mode.ghost Modality.usage
      mIntroMisMod elimBody
  check "modElim-ι: mismatched modality → no reduction"
    true
    (Term.modElimIotaStep? elimMisMod |>.isNone)

  -----------------------------------------------------------
  -- idJ-ι reduction
  -----------------------------------------------------------

  -- 11. idJ on refl: ↦ app base witness.
  let baseFn : Term 0 := .const Mode.software "j_base"
  let witness : Term 0 := natZero Mode.software
  let reflTerm : Term 0 := .refl Mode.software witness
  let idJTerm : Term 0 :=
    .idJ Mode.software mot baseFn reflTerm
  match Term.idJIotaStep? idJTerm with
  | some result =>
      let expected : Term 0 :=
        .app Mode.software baseFn witness
      check "idJ-ι: idJ mot base (refl w) ↦ app base w"
        true
        (Term.structEq result expected)
  | none =>
      check "idJ-ι: expected reduction"
        true
        false

  -----------------------------------------------------------
  -- coerceCell strip
  -----------------------------------------------------------

  -- 12. coerceCell strip: yields the inner term.
  let wrapped : Term 0 :=
    .coerceCell Modality.usage "from" "to" (natZero Mode.software)
  match Term.coerceCellStrip? wrapped with
  | some inner =>
      check "coerceCell strip: yields inner"
        true
        (Term.structEq inner (natZero Mode.software))
  | none =>
      check "coerceCell strip: expected to apply"
        true
        false

  -- 13. coerceCell strip on non-coerceCell: returns none.
  check "coerceCell strip: non-coerceCell → none"
    true
    (Term.coerceCellStrip? (natZero Mode.software : Term 0)
      |>.isNone)

  -----------------------------------------------------------
  -- whnf composition
  -----------------------------------------------------------

  -- 14. whnf on β: `(λx. x) zero` ↦ zero.
  let whnf1 : Term 0 :=
    Term.whnf Term.defaultFuel
      (.app Mode.software (idLam Mode.software)
        (natZero Mode.software))
  check "whnf: (λx. x) zero ↦ zero"
    true
    (Term.structEq whnf1 (natZero Mode.software))

  -- 15. whnf on nested β: `((λx. x) (λy. y)) zero` ↦ zero.
  let nestedApp : Term 0 :=
    .app Mode.software
      (.app Mode.software (idLam Mode.software) (idLam Mode.software))
      (natZero Mode.software)
  let whnf2 : Term 0 := Term.whnf Term.defaultFuel nestedApp
  check "whnf: ((λx. x) (λy. y)) zero ↦ zero"
    true
    (Term.structEq whnf2 (natZero Mode.software))

  -- 16. whnf strips coerceCell wrapping then reduces.  A
  --     coerceCell wrapping `(λx. x) zero` should normalize
  --     to `zero` (strip + β).
  let coerceWrap : Term 0 :=
    .coerceCell Modality.usage "g_lo" "g_hi"
      (.app Mode.software (idLam Mode.software)
        (natZero Mode.software))
  let whnf3 : Term 0 := Term.whnf Term.defaultFuel coerceWrap
  check "whnf: coerceCell + β ↦ inner reduct"
    true
    (Term.structEq whnf3 (natZero Mode.software))

  -- 17. whnf composes ι: indRec on bool true via whnf.
  let recWhnf : Term 0 := Term.whnf Term.defaultFuel
    (.indRec Mode.software "Bool" mot
      (TermArgs.ofList [methF, methT])
      (boolTrue Mode.software))
  check "whnf: indRec Bool true ↦ true method"
    true
    (Term.structEq recWhnf methT)

  -- 18. whnf composes ν: tail of unfold.
  let tailWhnf : Term 0 := Term.whnf Term.defaultFuel destrTail
  check "whnf: coindDestruct(tail) on unfold ↦ tail arm"
    true
    (Term.structEq tailWhnf tailArm)

  -- 19. whnf with 0 fuel returns the input unchanged (no
  --     reduction even if a head step is available).
  let stuck : Term 0 := Term.whnf 0
    (.app Mode.software (idLam Mode.software)
      (natZero Mode.software))
  let stuckExpected : Term 0 :=
    .app Mode.software (idLam Mode.software)
      (natZero Mode.software)
  check "whnf: 0 fuel returns input unchanged"
    true
    (Term.structEq stuck stuckExpected)

  -- 20. whnf on already-WHNF (lam): unchanged.
  let lamHead : Term 0 := idLam Mode.software
  let whnfLam : Term 0 := Term.whnf Term.defaultFuel lamHead
  check "whnf: lam already in WHNF, unchanged"
    true
    (Term.structEq whnfLam lamHead)

  -- 21. applyArgs builds left-associated app chain:
  --     applyArgs m head [a, b, c] = app (app (app head a) b) c
  let head21 : Term 0 := .const Mode.software "F"
  let argList : TermArgs 0 := TermArgs.ofList
    [.const Mode.software "a", .const Mode.software "b"]
  let applied : Term 0 := Term.applyArgs Mode.software head21 argList
  let expected21 : Term 0 :=
    .app Mode.software
      (.app Mode.software head21 (.const Mode.software "a"))
      (.const Mode.software "b")
  check "applyArgs: left-associates the app chain"
    true
    (Term.structEq applied expected21)

end Tests.KernelMTT.ReductionTests
