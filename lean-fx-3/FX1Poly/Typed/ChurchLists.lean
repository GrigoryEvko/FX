import FX1Poly.Typed.CombinatoryLogic
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/ChurchLists — Church-encoded (Boehm-Berarducci) lists in the λ-fragment

The shipped Church encodings cover booleans (#981), numerals (#989), products (#1017) and coproducts (#1019).
This file adds the first RECURSIVE / inductive data shape — LISTS — via the Boehm-Berarducci fold encoding,
demonstrating that the pure Π-fragment captures parametric inductive data (not just finite tagged unions)
through polymorphism: a list IS its own right-fold.

  `nil = λc. λn. n`,   `cons h t = λc. λn. c h (t c n)`,   `fold c n list = list c n`

A Church list value is its own eliminator: applied to a cons-handler `c` and a nil-handler `n`, it computes the
right fold `c h₁ (c h₂ (… (c hₖ n)))`.  `churchNil` ignores `c` and returns the nil-handler; `churchCons h t`
applies `c` to the head `h` and the RECURSIVELY-folded tail `t c n` — the inductive structure realized as
nested polymorphic application (exactly Church numeral SUCC carrying a payload).

  * **`foldNil`** — `fold c n nil ↝* n`: the nil case discards the cons-handler and returns the nil-handler, for
    ARBITRARY handlers `c, n` (`nil` has no payload, so the two β-contractions are clean — `churchNil` is the
    Church-numeral zero `λf.λx.x` carrying the fold).  The base case of the Boehm-Berarducci fold, computing in
    the pure Π-fragment with no primitive list type.
  * **`churchNil_isValue` / `churchCons_isValue`** — both encodings are λ-VALUES (their head is `gen_lam`, a
    closed normal canonical inhabitant of the encoded list type), the data-value witnesses.
  * **`foldCons` (★)** — `fold c n (cons h t) ↝* c h (t c n)`: the RECURSIVE cons-fold.  Folding a cons cell
    applies the cons-handler `c` to the head `h` and the RECURSIVELY-folded tail `t c n` — the inductive
    eliminator computing one constructor deep.  The contractum threads the cons-handler `c` through TWO binders
    into both the head-handler position AND the tail, so the first β-step weakens `c` TWICE; the doubly-weakened
    stored values (head, tail) collapse one level by `RawTerm.subst_lift_singleton_weaken_weaken` (#1023) — the
    same double-weaken cancellation the symbolic Church-sum payload (#1025) and general S-rule (#1024) used.
  * **`foldSingleton` (★)** — `fold c n (cons h nil) ↝* c h n`: the fold of a CONCRETE one-element list, the
    recursion BOTTOMING OUT.  Composes `foldCons` (reaching `c h (nil c n)`) with `foldNil` (the folded tail
    `nil c n ↝* n`) lifted through the application's argument position (`StepStar.appArgument`) — the non-vacuous
    demonstration that the Boehm-Berarducci fold computes a finite list to its folded value.

## Zero-axiom verification

`foldNil` is two `Step.beta` (lifted by one `Step.cong .gen_app` congruence) whose `subst0` contracta are the
`rfl`-clean innermost-variable substitutions; the value witnesses read the `gen_lam` head off the `lamCell`
definitions by `rfl`.  `foldCons` mirrors the `ChurchSums` symbolic case-selection (#1025): the β1 reshape
`churchCons_subst_consHandler` is a `show`-push (distribute `subst` through the nested `appCell`s, exposing the
doubly-weakened head/tail) + `rw [subst_lift_singleton_weaken_weaken …]` + `rfl`, then the function-position
congruence lifts the reshaped β1, the second β cancels the single weakens (`weaken_subst_singleton`), composed by
`StepStar.trans`.  `foldSingleton` is `StepStar.trans_compose` of `foldCons` with `StepStar.appArgument`-lifted
`foldNil`.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- A closed, scope-polymorphic domain annotation for the Church-list binders.  Under T2 every `lamCell` carries a
domain; for these pure-raw fixtures (no typing derivation) a closed `universeCodeCell` is invariant under
`subst0`/`weaken` and heads no redex, keeping the value/fold computations clean. -/
def churchListDomainAnn {scope : Nat} : RawTerm scope :=
  universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- `nil = λc. λn. n` — the empty Church list: ignores the cons-handler `c` (outer binder) and returns the
nil-handler `n` (inner binder, `var 0`).  Structurally the Church-numeral zero `λf.λx.x`. -/
def churchNil : RawTerm 0 :=
  lamCell churchListDomainAnn (lamCell churchListDomainAnn (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))

/-- `cons h t = λc. λn. c h (t c n)` — prepend `h` to `t`: applies the cons-handler `c` (outer binder, `var 1`)
to the stored head `h` and the RECURSIVELY-folded tail `t c n`.  The inductive constructor as nested polymorphic
application. -/
def churchCons (head tail : RawTerm 0) : RawTerm 0 :=
  lamCell churchListDomainAnn (lamCell churchListDomainAnn
    (appCell
      (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (RawTerm.weaken (RawTerm.weaken head)))
      (appCell
        (appCell (RawTerm.weaken (RawTerm.weaken tail))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
        (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))))

/-- `fold c n list = list c n` — the right-fold eliminator: apply the Church list to its cons- and nil-handlers. -/
def churchFold (consHandler nilHandler list : RawTerm 0) : RawTerm 0 :=
  appCell (appCell list consHandler) nilHandler

/-- **`fold c n nil ↝* n`** — folding the empty list discards the cons-handler and returns the nil-handler, for
ARBITRARY handlers.  `nil = λc.λn.n` applied to `c` β-reduces (the body never mentions `c`) to `λn.n`; applied
to `n` it returns `n`.  Both `subst0` contracta are the clean innermost-variable substitutions. -/
theorem foldNil (consHandler nilHandler : RawTerm 0) :
    StepStar (churchFold consHandler nilHandler churchNil) nilHandler := by
  have functionBeta : Step (appCell churchNil consHandler)
      (lamCell churchListDomainAnn (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) := HeadStep.beta.toStep
  have congStep : Step (churchFold consHandler nilHandler churchNil)
      (appCell (lamCell churchListDomainAnn (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) nilHandler) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons nilHandler .childNil) functionBeta)
  have innerBeta : Step (appCell (lamCell churchListDomainAnn (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) nilHandler)
      nilHandler := HeadStep.beta.toStep
  exact StepStar.trans congStep (StepStar.trans innerBeta (StepStar.refl _))

/-- **`churchNil` is a λ-value.**  Its head generator is `gen_lam` — a closed weak-head-normal function value,
the canonical inhabitant of the Boehm-Berarducci list type `Π R. (A → R → R) → R → R`. -/
theorem churchNil_isValue : churchNil.rootGenerator = Generator.gen_lam := rfl

/-- **`churchCons h t` is a λ-value** for any head and tail.  Its head generator is `gen_lam` — the cons
constructor is a function value (it abstracts the two fold-handlers before computing). -/
theorem churchCons_isValue (head tail : RawTerm 0) :
    (churchCons head tail).rootGenerator = Generator.gen_lam := rfl

/-- **β1 contractum reshape (cons-fold).**  Substituting the cons-handler into `churchCons`'s inner body collapses
each doubly-weakened stored value (`head`, `tail`) one level (`subst_lift_singleton_weaken_weaken`, #1023) to
`weaken …` and turns the two `c`-references (`var 1`) into `weaken consHandler`; the `n`-reference (`var 0`) stays.
The cons analogue of `ChurchSumsGeneral.leftInjection_subst_handlerL`, with two stored values instead of one. -/
theorem churchCons_subst_consHandler (head tail consHandler : RawTerm 0) :
    RawTerm.subst0
        (lamCell churchListDomainAnn
          (appCell
            (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
              (RawTerm.weaken (RawTerm.weaken head)))
            (appCell
              (appCell (RawTerm.weaken (RawTerm.weaken tail))
                (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
              (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) consHandler
      = lamCell churchListDomainAnn
          (appCell
            (appCell (RawTerm.weaken consHandler) (RawTerm.weaken head))
            (appCell
              (appCell (RawTerm.weaken tail) (RawTerm.weaken consHandler))
              (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) := by
  dsimp only [RawTerm.subst0, churchListDomainAnn]
  show lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (appCell
        (appCell _ (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton consHandler))
          (RawTerm.weaken (RawTerm.weaken head))))
        (appCell
          (appCell (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton consHandler))
            (RawTerm.weaken (RawTerm.weaken tail))) _)
          _)) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken head consHandler,
      RawTerm.subst_lift_singleton_weaken_weaken tail consHandler]
  rfl

/-- **★ `fold c n (cons h t) ↝* c h (t c n)`** — the RECURSIVE cons-fold computation.  Folding a cons cell applies
the cons-handler `c` to the head `h` and the RECURSIVELY-folded tail `t c n`: `churchCons h t = λc.λn. c h (t c n)`
applied to `c` (the β1 reshape `churchCons_subst_consHandler`, where the cons-handler is weakened twice and the two
stored values collapse via #1023) then to `n` (the second β, single-weaken cancellations).  The inductive
eliminator computing one constructor deep, faithful for ARBITRARY head and tail. -/
theorem foldCons (head tail consHandler nilHandler : RawTerm 0) :
    StepStar (churchFold consHandler nilHandler (churchCons head tail))
      (appCell (appCell consHandler head)
        (appCell (appCell tail consHandler) nilHandler)) := by
  have functionBeta : Step (appCell (churchCons head tail) consHandler)
      (lamCell churchListDomainAnn
        (appCell
          (appCell (RawTerm.weaken consHandler) (RawTerm.weaken head))
          (appCell
            (appCell (RawTerm.weaken tail) (RawTerm.weaken consHandler))
            (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))))) := by
    rw [← churchCons_subst_consHandler head tail consHandler]
    exact HeadStep.beta.toStep
  have congStep : Step (churchFold consHandler nilHandler (churchCons head tail))
      (appCell
        (lamCell churchListDomainAnn
          (appCell
            (appCell (RawTerm.weaken consHandler) (RawTerm.weaken head))
            (appCell
              (appCell (RawTerm.weaken tail) (RawTerm.weaken consHandler))
              (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))))
        nilHandler) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons nilHandler .childNil) functionBeta)
  have outerBeta : Step
      (appCell
        (lamCell churchListDomainAnn
          (appCell
            (appCell (RawTerm.weaken consHandler) (RawTerm.weaken head))
            (appCell
              (appCell (RawTerm.weaken tail) (RawTerm.weaken consHandler))
              (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))))
        nilHandler)
      (appCell
        (appCell (RawTerm.subst0 (RawTerm.weaken consHandler) nilHandler)
          (RawTerm.subst0 (RawTerm.weaken head) nilHandler))
        (appCell
          (appCell (RawTerm.subst0 (RawTerm.weaken tail) nilHandler)
            (RawTerm.subst0 (RawTerm.weaken consHandler) nilHandler))
          nilHandler)) := HeadStep.beta.toStep
  have cancelConsHandler : RawTerm.subst0 (RawTerm.weaken consHandler) nilHandler = consHandler :=
    RawTerm.weaken_subst_singleton consHandler nilHandler
  have cancelHead : RawTerm.subst0 (RawTerm.weaken head) nilHandler = head :=
    RawTerm.weaken_subst_singleton head nilHandler
  have cancelTail : RawTerm.subst0 (RawTerm.weaken tail) nilHandler = tail :=
    RawTerm.weaken_subst_singleton tail nilHandler
  rw [cancelConsHandler, cancelHead, cancelTail] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

/-- **★ `fold c n (cons h nil) ↝* c h n`** — the fold of a CONCRETE one-element list, the recursion BOTTOMING OUT.
`foldCons` reaches `c h (nil c n)`; the folded tail `nil c n` reduces by `foldNil` (lifted through the application's
argument position via `StepStar.appArgument`) to the nil-handler `n`.  The non-vacuous demonstration that the
Boehm-Berarducci fold computes a finite list to its folded value. -/
theorem foldSingleton (head consHandler nilHandler : RawTerm 0) :
    StepStar (churchFold consHandler nilHandler (churchCons head churchNil))
      (appCell (appCell consHandler head) nilHandler) :=
  StepStar.trans_compose
    (foldCons head churchNil consHandler nilHandler)
    (StepStar.appArgument (appCell consHandler head) (foldNil consHandler nilHandler))

end FX1Poly.Typed
