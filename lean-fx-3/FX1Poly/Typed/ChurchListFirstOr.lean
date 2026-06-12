import FX1Poly.Typed.ChurchLists
import FX1Poly.Typed.TypedChurchBooleans
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Core.ConvCongruence
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/ChurchListFirstOr — `firstOr`: the head accessor, the first list op that PROJECTS DATA out

The shipped list operations all return a DERIVED BOOLEAN: `isEmpty` (#1083, structure), `any`/`all` (#1084/#1085,
a content-fold to `true`/`false`).  This file ships the first list op that PROJECTS AN ELEMENT OUT of the list —
`firstOr`, the head accessor with a default for `nil`:

  `firstOr default list = fold (λhead. λrest. head) default list`

The cons-handler `λhead. λrest. head` returns its FIRST argument (the head) and DISCARDS the second (the
recursively-folded tail).  This is a new handler shape — `isEmpty`'s handler was a constant (`λ_.λ_. false`),
`any`/`all`'s were shipped combinators (`or`/`and`); `firstOr`'s PROJECTS its first bound argument, so the fold
returns an arbitrary stored ELEMENT rather than computing a predicate over the list.  It demonstrates the
HEAD-STRICT short-circuit: the head is returned without ever inspecting the tail.

  * **`firstOrHandler_returnsHead`** — `firstOrHandler head rest ↝* head` for ANY head and rest: the projection
    handler returns the head and never touches `rest`.  The β1 reshape `firstOrHandlerInnerSubst` is `rfl` (the
    lift of the singleton on the head-index computes straight to `weaken head`), and the outer β cancels the single
    weakening (`weaken_subst_singleton`).
  * **`firstOrNil`** — `firstOr d nil ↝* d`: the empty list yields the default (directly via `foldNil`).
  * **`firstOrConsNil`** — `firstOr d [a] ↝* a`: a one-element list yields its head.
  * **`firstOrConsConsNil` (★)** — `firstOr d [a, b] ↝* a`: the HEAD-STRICT short-circuit.  `foldCons` reaches
    `firstOrHandler a (b-fold)`, and the projection handler returns `a` WITHOUT reducing the folded tail `b-fold`.
  * **`firstOrSeesHead` (★)** — `¬ Conv (firstOr d [true, x]) (firstOr d [false, x])`: `firstOr` separates lists by
    their FIRST element even at EQUAL length and equal tail — it reads the head, where `any`/`all` inspect every
    element.  A genuinely different list observation; else `true ≡ false` (refuted by #983).
  * **`firstOrDefaultIsFallback`** — `¬ Conv (firstOr true [false]) (firstOr true nil)`: the default fires on `nil`
    (yielding `true`) but a `cons` overrides it (yielding `false`), so the default is a genuine fallback.

Everything is the raw `Step` / `Conv` relations; no typing derivation is consulted.

## Zero-axiom verification

`firstOrHandler_returnsHead` mirrors the `ChurchListIsEmpty` handler reshape, but the body is the head VARIABLE
`var 1` (a projection), not a weakened closed constant: the β1 reshape is `rfl` (cleaner than isEmpty's
double-weaken `rw`), and the outer β is `Step.beta` with `subst0 (weaken head) rest = head` rewritten FORWARD at
the hypothesis (`weaken_subst_singleton`) to avoid over-rewriting the free `head`.  The computations are
`StepStar.trans_compose` of the shipped fold lemmas (`foldNil` / `foldSingleton` / `foldCons`, #1081/#1082) with
`firstOrHandler_returnsHead`; the discriminations are `Conv.fromStepStar` / `.trans` / `.sym` +
`churchTrue_notConvertible_churchFalse` (#983).  No `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- `firstOrHandler = λhead. λrest. head` — the head-projecting cons-handler: returns the head, discards the
recursively-folded tail. -/
def firstOrHandler : RawTerm 0 :=
  lamCell churchListDomainAnn
    (lamCell churchListDomainAnn (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))

/-- β1 reshape: substituting the head into `firstOrHandler` keeps the head (lifted under the rest-binder).  `rfl`
because `lift (singleton head)` on the head-index `var 1` computes directly to `weaken head`. -/
theorem firstOrHandlerInnerSubst (head : RawTerm 0) :
    RawTerm.subst0 (lamCell churchListDomainAnn (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))) head
      = lamCell churchListDomainAnn (RawTerm.weaken head) := by
  dsimp only [RawTerm.subst0, churchListDomainAnn]
  show lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton head))
      (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))) = _
  rfl

/-- **`firstOrHandler head rest ↝* head`** for any head and rest — the projection handler returns its FIRST
argument and DISCARDS the second (head-strict: `rest` is never inspected). -/
theorem firstOrHandler_returnsHead (head rest : RawTerm 0) :
    StepStar (appCell (appCell firstOrHandler head) rest) head := by
  have functionBeta : Step (appCell firstOrHandler head)
      (lamCell churchListDomainAnn (RawTerm.weaken head)) := by
    rw [← firstOrHandlerInnerSubst head]; exact HeadStep.beta.toStep
  have congStep : Step (appCell (appCell firstOrHandler head) rest)
      (appCell (lamCell churchListDomainAnn (RawTerm.weaken head)) rest) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons rest .childNil) functionBeta)
  have cancel : RawTerm.subst0 (RawTerm.weaken head) rest = head :=
    RawTerm.weaken_subst_singleton head rest
  have outerBeta : Step (appCell (lamCell churchListDomainAnn (RawTerm.weaken head)) rest)
      (RawTerm.subst0 (RawTerm.weaken head) rest) := HeadStep.beta.toStep
  rw [cancel] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

/-- `firstOr default list = fold (λh.λrest. h) default list` — the head accessor with a default for `nil`: the
first list operation that PROJECTS A STORED ELEMENT out rather than computing a derived boolean. -/
def churchListFirstOr (defaultValue list : RawTerm 0) : RawTerm 0 :=
  churchFold firstOrHandler defaultValue list

/-- `firstOr d nil ↝* d` — the empty list yields the default, directly via `foldNil`. -/
theorem firstOrNil (defaultValue : RawTerm 0) :
    StepStar (churchListFirstOr defaultValue churchNil) defaultValue :=
  foldNil firstOrHandler defaultValue

/-- `firstOr d [a] ↝* a` — a one-element list yields its head: `foldSingleton` reaches `firstOrHandler a d`, which
the projection handler reduces to `a`. -/
theorem firstOrConsNil (defaultValue head : RawTerm 0) :
    StepStar (churchListFirstOr defaultValue (churchCons head churchNil)) head :=
  StepStar.trans_compose
    (foldSingleton head firstOrHandler defaultValue)
    (firstOrHandler_returnsHead head defaultValue)

/-- **★ `firstOr d [a, b] ↝* a`** — the HEAD-STRICT short-circuit: `foldCons` reaches `firstOrHandler a (b-fold)`,
and the projection handler returns `a` WITHOUT inspecting the folded tail.  `firstOr` reads only the head, however
long the list. -/
theorem firstOrConsConsNil (defaultValue head second : RawTerm 0) :
    StepStar (churchListFirstOr defaultValue (churchCons head (churchCons second churchNil))) head :=
  StepStar.trans_compose
    (foldCons head (churchCons second churchNil) firstOrHandler defaultValue)
    (firstOrHandler_returnsHead head
      (appCell (appCell (churchCons second churchNil) firstOrHandler) defaultValue))

/-- **★ `firstOr` reads the HEAD: it separates lists by first element, even at equal length.**  `firstOr d [true, x]`
and `firstOr d [false, x]` are NOT convertible — both length-2 with the same tail `x`, but `firstOr` returns the
head, so the results `true` / `false` differ (else `true ≡ false`, refuted by #983).  Where `any`/`all` inspect
ALL elements, `firstOr` projects the first — a genuinely different list observation. -/
theorem firstOrSeesHead (defaultValue secondValue : RawTerm 0) :
    ¬ Conv (churchListFirstOr defaultValue (churchCons churchTrueLambda (churchCons secondValue churchNil)))
        (churchListFirstOr defaultValue (churchCons churchFalseLambda (churchCons secondValue churchNil))) := by
  intro hConv
  have convResults : Conv churchTrueLambda churchFalseLambda :=
    Conv.trans (Conv.sym (Conv.fromStepStar (firstOrConsConsNil defaultValue churchTrueLambda secondValue)))
      (Conv.trans hConv (Conv.fromStepStar (firstOrConsConsNil defaultValue churchFalseLambda secondValue)))
  exact churchTrue_notConvertible_churchFalse convResults

/-- `firstOr` falls back to the default on `nil` but a `cons` overrides it: `firstOr true [false] ↝* false` while
`firstOr true nil ↝* true`, so the two are NOT convertible — the default is a genuine fallback, not the result on a
non-empty list. -/
theorem firstOrDefaultIsFallback :
    ¬ Conv (churchListFirstOr churchTrueLambda (churchCons churchFalseLambda churchNil))
        (churchListFirstOr churchTrueLambda churchNil) := by
  intro hConv
  have convResults : Conv churchFalseLambda churchTrueLambda :=
    Conv.trans (Conv.sym (Conv.fromStepStar (firstOrConsNil churchTrueLambda churchFalseLambda)))
      (Conv.trans hConv (Conv.fromStepStar (firstOrNil churchTrueLambda)))
  exact churchTrue_notConvertible_churchFalse (Conv.sym convResults)

end FX1Poly.Typed
