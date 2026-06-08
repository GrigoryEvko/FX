import FX1Poly.Typed.CombinatoryLogic
import FX1Poly.Core.RawTermSubst0Commute

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

The recursive CONS-fold computation `fold c n (cons h t) ↝* c h (t c n)` is DEFERRED: its contractum threads the
cons-handler `c` through TWO binders into both the head-handler position AND the recursively-folded tail, so the
under-binder `weaken·/subst0` cancellations run one binder deeper than the `ChurchSums` `case`-selection and need
the same weaken/subst commutation that the symbolic Church-sum payload (#1025) and the general S-rule (#1024)
deferred.  The base case (`foldNil`) and the value witnesses are the clean fragment; the recursive computation is
the documented next brick (the de Bruijn cons-fold, parallel to the symbolic-payload deferral).  Everything here
is the raw `Step` relation; no typing derivation is consulted.

## Zero-axiom verification

`foldNil` is two `Step.beta` (lifted by one `Step.cong .gen_app` congruence) whose `subst0` contracta are the
`rfl`-clean innermost-variable substitutions; the value witnesses read the `gen_lam` head off the `lamCell`
definitions by `rfl`.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated
per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- `nil = λc. λn. n` — the empty Church list: ignores the cons-handler `c` (outer binder) and returns the
nil-handler `n` (inner binder, `var 0`).  Structurally the Church-numeral zero `λf.λx.x`. -/
def churchNil : RawTerm 0 :=
  lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))

/-- `cons h t = λc. λn. c h (t c n)` — prepend `h` to `t`: applies the cons-handler `c` (outer binder, `var 1`)
to the stored head `h` and the RECURSIVELY-folded tail `t c n`.  The inductive constructor as nested polymorphic
application. -/
def churchCons (head tail : RawTerm 0) : RawTerm 0 :=
  lamCell (lamCell
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
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) := Step.beta
  have congStep : Step (churchFold consHandler nilHandler churchNil)
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) nilHandler) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons nilHandler .childNil) functionBeta)
  have innerBeta : Step (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) nilHandler)
      nilHandler := Step.beta
  exact StepStar.trans congStep (StepStar.trans innerBeta (StepStar.refl _))

/-- **`churchNil` is a λ-value.**  Its head generator is `gen_lam` — a closed weak-head-normal function value,
the canonical inhabitant of the Boehm-Berarducci list type `Π R. (A → R → R) → R → R`. -/
theorem churchNil_isValue : churchNil.rootGenerator = Generator.gen_lam := rfl

/-- **`churchCons h t` is a λ-value** for any head and tail.  Its head generator is `gen_lam` — the cons
constructor is a function value (it abstracts the two fold-handlers before computing). -/
theorem churchCons_isValue (head tail : RawTerm 0) :
    (churchCons head tail).rootGenerator = Generator.gen_lam := rfl

end FX1Poly.Typed
