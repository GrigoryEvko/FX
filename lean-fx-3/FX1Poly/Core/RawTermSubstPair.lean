import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.RawTermSubstConsCommute
import FX1Poly.Core.RawTermFresh

/-! # Foundation/PolyCell/Core/RawTermSubstPair — two-variable substitution toolkit

The **two-variable parallel substitution** that the natural-number
eliminators' step-case iota (`Step.iotaNatElimSucc` /
`Step.iotaNatRecSucc`) cites.  Where beta needs a single-variable
substitution (`RawTerm.subst0`, replacing `var 0`), the succ-iota
needs to replace BOTH `var 0` (the inductive hypothesis = the
recursive call) AND `var 1` (the predecessor) inside the succ-branch
(which lives under TWO binders at `scope + 2`).

## The succ-iota reduct convention

`Step.iotaNatElimSucc` fires the canonical natElim step-case as:

```
Step (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                .childNil)))))
     (RawTerm.subst
        (RawTermSubst.cons recursiveCall (RawTermSubst.singleton predecessor))
        succBranch)
```

where `recursiveCall = natElim motive zeroBranch succBranch predecessor`.
This file packages `RawTermSubst.cons recursiveCall (RawTermSubst.singleton
predecessor)` as `RawTermSubst.pair recursiveCall predecessor` and its
application to a body as `RawTerm.substPair`.

## Definitions

* `RawTermSubst.pair innerArg outerArg : RawTermSubst (scope + 2) scope`
  — position 0 ↦ `innerArg`, position 1 ↦ `outerArg`, position k+2 ↦
  variable k.  The two-substituent analog of `RawTermSubst.singleton`.

* `RawTerm.substPair body innerArg outerArg : RawTerm scope` —
  convenience wrapper applying `pair`.

## The commute laws (the natElim analogs of the beta laws)

The succ-iota proofs run the EXACT template of the beta proofs in
`StepSubst.lean`, replacing `subst0` machinery with `substPair`:

* `RawTerm.substPair_rename_commute` — renaming distributes over
  `substPair` (the analog of `RawTerm.rename_subst0_commute`); the
  body renames under the DOUBLE lift `(lift (lift rho))`.
* `RawTerm.substPair_subst_commute` — an outer substitution reshapes
  a `substPair` contractum (the analog of
  `RawTerm.subst0_subst_commute`); the body substitutes under the
  DOUBLE lift `(lift (lift sigma))`.

## Zero-axiom verification

Every law is proved from the shipped fold-based commute/compose
machinery (`RawTerm.subst_compose`, `RawTerm.subst_rename_commute`,
`RawTerm.rename_subst_commute`, `RawTerm.subst_pointwise`,
`RawTerm.weaken_subst_singleton`) plus per-position `Fin` `cases`
closing by `rfl` — the identical proof shape as the singleton laws in
`RawTermSubst0Commute.lean`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- Two-position parallel substitution: maps position 0 to `innerArg`,
position 1 to `outerArg`, and position k+2 to variable k (shifting all
higher variables down by two).

`RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)`: the
`cons` fills position 0 with `innerArg`, and the inner `singleton`
fills (the now position-0-of-the-tail =) overall position 1 with
`outerArg`, shifting the rest down.  The substitution the
natural-number step-case iota references. -/
@[reducible] def RawTermSubst.pair {scope : Nat}
    (innerArg outerArg : RawTerm scope) :
    RawTermSubst (scope + 2) scope :=
  RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)

/-- Two-variable substitution under two binders: substitutes `innerArg`
for `var 0` (the innermost, e.g. the inductive hypothesis) and
`outerArg` for `var 1` (e.g. the predecessor) in `body`, shifting all
higher variables down by two.

The natElim/natRec step-case iota reduces `natElim m z s (natSucc n)`
to `substPair s (natElim m z s n) n`. -/
@[reducible] def RawTerm.substPair {scope : Nat}
    (body : RawTerm (scope + 2)) (innerArg outerArg : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst (RawTermSubst.pair innerArg outerArg) body

/-- Behavior pin: `pair`'s position-0 entry returns the inner
substituent (the inductive hypothesis slot). -/
theorem RawTermSubst.pair_var_zero {scope : Nat}
    (innerArg outerArg : RawTerm scope) :
    RawTermSubst.pair innerArg outerArg ⟨0, Nat.zero_lt_succ (scope + 1)⟩ =
      innerArg := rfl

/-- Behavior pin: `pair`'s position-1 entry returns the outer
substituent (the predecessor slot). -/
theorem RawTermSubst.pair_var_one {scope : Nat}
    (innerArg outerArg : RawTerm scope) :
    RawTermSubst.pair innerArg outerArg
        ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩ = outerArg := rfl

/-- Beta-shape smoke: `substPair` on `var 0` returns the inner
substituent (the IH slot). -/
theorem RawTerm.substPair_var_zero {scope : Nat}
    (innerArg outerArg : RawTerm scope) :
    RawTerm.substPair
        (.mkGen .gen_var ⟨0, Nat.zero_lt_succ (scope + 1)⟩ .childNil)
        innerArg outerArg = innerArg := rfl

/-- Beta-shape smoke: `substPair` on `var 1` returns the outer
substituent (the predecessor slot). -/
theorem RawTerm.substPair_var_one {scope : Nat}
    (innerArg outerArg : RawTerm scope) :
    RawTerm.substPair
        (.mkGen .gen_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩
          .childNil)
        innerArg outerArg = outerArg := rfl

/-- **Renaming distributes over two-variable substitution.**  The
two-substituent analog of `RawTerm.rename_subst0_commute`: pushing a
renaming `rho` through a `substPair` renames the body under the DOUBLE
lift and renames each substituent directly.

  `rename rho (substPair body inner outer) =
     substPair (rename (lift (lift rho)) body) (rename rho inner)
       (rename rho outer)`.

Proved by the identical fold-commute template as the singleton law:
fold the rename into the substitution on both sides, then
`subst_pointwise` against a per-position `Fin` case split — at
positions 0 and 1 both sides land on `rename rho inner` /
`rename rho outer`; at position k+2 both reduce to the shifted
variable. -/
theorem RawTerm.substPair_rename_commute {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 2))
    (innerArg outerArg : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (RawTerm.substPair body innerArg outerArg) =
      RawTerm.substPair
        (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming))
          body)
        (RawTerm.rename rawRenaming innerArg)
        (RawTerm.rename rawRenaming outerArg) := by
  dsimp only [RawTerm.substPair, RawTermSubst.pair]
  rw [RawTerm.subst_rename_commute
    (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
    rawRenaming body]
  rw [RawTerm.rename_subst_commute
    (RawRenaming.lift (RawRenaming.lift rawRenaming))
    (RawTermSubst.cons (RawTerm.rename rawRenaming innerArg)
      (RawTermSubst.singleton (RawTerm.rename rawRenaming outerArg)))
    body]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero => rfl
      | succ priorPositionValue =>
          cases priorPositionValue with
          | zero => rfl
          | succ _priorPriorPositionValue => rfl

/-- **An outer substitution reshapes a two-variable contractum.**  The
two-substituent analog of `RawTerm.subst0_subst_commute`: substituting
`sigma` through a `substPair` contractum equals the `substPair` of the
double-lifted body and the substituted substituents.

  `subst sigma (substPair body inner outer) =
     substPair (subst (lift (lift sigma)) body) (subst sigma inner)
       (subst sigma outer)`.

This is the reshape the natElim/natRec succ-iota arm of `Step.subst`
runs: after an outer substitution, the substituted succ-redex still
contracts in one `Step` to the substituted reduct.  Proved by
`subst_compose` on both sides + `subst_pointwise`; at positions 0/1 the
substituents agree, at k+2 the lift's weakening cancels against the
inner singleton (`RawTerm.weaken_subst_singleton`), exactly as in the
singleton law. -/
theorem RawTerm.substPair_subst_commute {sourceScope targetScope : Nat}
    (body : RawTerm (sourceScope + 2))
    (innerArg outerArg : RawTerm sourceScope)
    (sigma : RawTermSubst sourceScope targetScope) :
    RawTerm.subst sigma (RawTerm.substPair body innerArg outerArg) =
      RawTerm.substPair
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift sigma)) body)
        (RawTerm.subst sigma innerArg)
        (RawTerm.subst sigma outerArg) := by
  dsimp only [RawTerm.substPair, RawTermSubst.pair]
  rw [RawTerm.subst_compose
    (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) sigma body]
  rw [RawTerm.subst_compose (RawTermSubst.lift (RawTermSubst.lift sigma))
    (RawTermSubst.cons (RawTerm.subst sigma innerArg)
      (RawTermSubst.singleton (RawTerm.subst sigma outerArg))) body]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero => rfl
      | succ priorPositionValue =>
          cases priorPositionValue with
          | zero =>
              -- Position 1: LHS = subst sigma outer (via the singleton's position-0
              -- entry through cons); RHS reduces `(lift (lift sigma)) 1 = weaken (var 0)
              -- = var 1`, then subst (cons A (singleton B)) (var 1) = B = subst sigma outer.
              -- Both sides reduce to `subst sigma outerArg`.
              rfl
          | succ priorPriorPositionValue =>
              dsimp only [RawTermSubst.compose, RawTermSubst.cons,
                RawTermSubst.lift, RawTermSubst.singleton]
              -- RHS = subst (cons A (singleton B)) (weaken (weaken (sigma k))).  Expose the
              -- OUTER weaken as `rename weaken` so the `cons` law `weaken_subst_cons` (whose
              -- pattern is `rename weaken _`) fires, peeling it to `subst (singleton B) (weaken
              -- (sigma k))`; then `weaken_subst_singleton` peels the inner one, leaving sigma k.
              rw [RawTerm.weaken_eq_rename
                (RawTerm.weaken
                  (sigma ⟨priorPriorPositionValue,
                    Nat.lt_of_succ_lt_succ
                      (Nat.lt_of_succ_lt_succ positionBound)⟩))]
              rw [RawTerm.weaken_subst_cons
                (RawTerm.weaken
                  (sigma ⟨priorPriorPositionValue,
                    Nat.lt_of_succ_lt_succ
                      (Nat.lt_of_succ_lt_succ positionBound)⟩))
                (RawTerm.subst sigma innerArg)
                (RawTermSubst.singleton (RawTerm.subst sigma outerArg))]
              exact (RawTerm.weaken_subst_singleton
                (sigma ⟨priorPriorPositionValue,
                  Nat.lt_of_succ_lt_succ
                    (Nat.lt_of_succ_lt_succ positionBound)⟩)
                (RawTerm.subst sigma outerArg)).symm

/-! ## Inline `cons`/`singleton` forms

The `Step` relation's succ-iota constructors and the rename-reflection
arms write the two-variable reduct in the EXPANDED form `RawTerm.subst
(RawTermSubst.cons inner (RawTermSubst.singleton outer)) body` rather
than the `RawTerm.substPair` abbreviation, so their proof goals carry
that head.  These aliases re-state the two commute laws over the
expanded head so a plain `rw` matches the goal directly (the bodies are
definitionally the `substPair` laws — `substPair` is `@[reducible]`
and unfolds to exactly this `cons`/`singleton` form). -/

/-- Inline-`cons` form of `RawTerm.substPair_rename_commute` — the head
matches the `Step.iotaNatElimSucc` reduct shape for `rw`. -/
theorem RawTerm.cons_singleton_rename_commute {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 2))
    (innerArg outerArg : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (RawTerm.subst
          (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) body) =
      RawTerm.subst
        (RawTermSubst.cons (RawTerm.rename rawRenaming innerArg)
          (RawTermSubst.singleton (RawTerm.rename rawRenaming outerArg)))
        (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming)) body) :=
  RawTerm.substPair_rename_commute rawRenaming body innerArg outerArg

/-- Inline-`cons` form of `RawTerm.substPair_subst_commute` — the head
matches the `Step.iotaNatElimSucc` reduct shape for `rw`. -/
theorem RawTerm.cons_singleton_subst_commute {sourceScope targetScope : Nat}
    (body : RawTerm (sourceScope + 2))
    (innerArg outerArg : RawTerm sourceScope)
    (sigma : RawTermSubst sourceScope targetScope) :
    RawTerm.subst sigma
        (RawTerm.subst
          (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) body) =
      RawTerm.subst
        (RawTermSubst.cons (RawTerm.subst sigma innerArg)
          (RawTermSubst.singleton (RawTerm.subst sigma outerArg)))
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift sigma)) body) :=
  RawTerm.substPair_subst_commute body innerArg outerArg sigma

/-! ## Freshness of the two-variable contractum

The natElim/natRec succ-iota arm of `Step.preserves_isFreshFor` must
show the SUBSTITUTED reduct stays fresh.  This is the two-variable
analog of the beta arm, which derives freshness of `subst0 body arg`
from `bodyFresh` (at the single lift) and `argFresh` via
`subst0_subst_commute` + `rename_subst0_commute`.  Here the body lives
under TWO binders, so its freshness arrives at the DOUBLE lift
(`iterateLiftRaw _ 2`, definitionally `lift (lift _)`). -/

/-- **The two-variable contractum is fresh.**  Given the body fresh at
the double-lifted renaming/substitution (the shape
`RawTermChildren.head_isFreshFor_of_childCons_isFreshFor` delivers for a
shift-2 child) and both substituents fresh, the `substPair` reduct is
fresh.  The two-variable analog of the beta freshness step. -/
theorem RawTerm.isFreshFor_cons_singleton {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    (body : RawTerm (sourceScope + 2))
    (innerArg outerArg : RawTerm sourceScope)
    (bodyFresh :
      RawTerm.isFreshFor (iterateLiftRaw rawRenaming 2)
        (iterateLiftRaw rawSubstitution 2) body)
    (innerFresh : RawTerm.isFreshFor rawRenaming rawSubstitution innerArg)
    (outerFresh : RawTerm.isFreshFor rawRenaming rawSubstitution outerArg) :
    RawTerm.isFreshFor rawRenaming rawSubstitution
      (RawTerm.subst
        (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) body) := by
  dsimp only [RawTerm.isFreshFor]
  rw [RawTerm.cons_singleton_subst_commute body innerArg outerArg rawSubstitution]
  rw [RawTerm.cons_singleton_rename_commute rawRenaming
    (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift rawSubstitution)) body)
    (RawTerm.subst rawSubstitution innerArg)
    (RawTerm.subst rawSubstitution outerArg)]
  -- `iterateLiftRaw _ 2` is defeq to `lift (lift _)`, so the body-freshness
  -- hypothesis (stated at the double iterate) closes the renamed-body slot.
  dsimp only [RawTerm.isFreshFor] at bodyFresh innerFresh outerFresh
  have bodyFreshLift :
      RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming))
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift rawSubstitution))
            body) = body := bodyFresh
  rw [bodyFreshLift, innerFresh, outerFresh]

end FX1Poly.Core
