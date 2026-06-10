import FX1Poly.Core.FireRootRedex
import FX1Poly.Core.StepSubst

/-! # FX1Poly/Core/CompleteDevelopment
    — the Takahashi complete-development function, propext-clean via `fireRootRedex`.

`TakahashiTriangle.lean` reduces the FX raw-confluence diamond (the prize that strong
normalization cannot supply because raw β+ι is not SN) to exhibiting a complete-development function
with the triangle / maximal-reduct property: a function that contracts ALL redexes present in a term
at once (but NOT the redexes created by those contractions), to which every parallel reduct
further parallel-reduces.  This file ships that function.

## The propext-clean construction recipe

A direct definition matching the ~18 redex shapes (β-redex `app (lam body) arg`, each ι-redex
`boolElim true · ·`, …) with overlapping nested patterns plus a fallback generates a Lean matcher
that leaks `propext` (the deeply-nested-overlapping-pattern trap) and defeats the equation compiler.

The clean construction delegates ALL redex-shape detection to the already-propext-clean
`RawTerm.fireRootRedex` (gated in `AuditTyped.lean`), so this file does only flat structural matches:

* `fireRootRedexOrSelf` — fire the root redex if present (`Option.getD` over `fireRootRedex`), else
  keep the cell.  Non-recursive, a single `Option` match.
* `fireRootRedexOrSelfGated` — fire on the DEVELOPED children but ONLY when the ORIGINAL children
  form a syntactic redex (a single `Option` match on `fireRootRedex` of the original children).
* `completeDevelopment` / `completeDevelopmentChildren` — develop every child, then fire the root
  redex once VIA THE GATE.  The only matches are `mkGen` (one constructor), `childNil`/`childCons`
  (two non-overlapping constructors), and the gate's `Option`, so no propext-leaking matcher is generated.

This is exactly Takahashi's complete development: developing the children first contracts all redexes
inside them; firing the (developed) root once contracts the head redex IF the source was a syntactic
redex; and because `fireRootRedex`'s ι-contractums build the recursive eliminator call SYNTACTICALLY
(e.g. `natElim … (succ n) ↦ app (app s n) (natElim … n)`), the redexes CREATED by contraction are left
untouched — the defining property separating the complete development from full normalization.  The
GATE is essential: firing on developed children alone over-fires (an inner redex whose contractum is a
`lam` would turn an enclosing non-`lam`-headed application into a β-redex and contract it), which is not
a single parallel-reduction step and would break the triangle's `ParStep a (cd a)` instance.  Gating on
the original head — safe because redex-head constructors are never themselves root-redex generators, so
developing preserves the head — fires the SAME redex with the developed components (see `cd_app_lam_eq`).

`completeDevelopment_stepStar` confirms the development sits inside the existing reduction relation:
the source `StepStar`-reduces to its complete development (children congruence via
`StepStar.ofChildrenStar`, then the root firing via `fireRootRedex_sound`).  This is the soundness
half feeding the eventual `HasMaximalReduct ParStep` proof (the triangle), which discharges the
`ParStep` diamond and hence — through the shipped `Step ⊆ ParStep ⊆ StepStar` sandwich — unconditional
raw confluence.

## Zero-axiom verification

The functions are flat structural mutual recursion (no `termination_by`); `fireRootRedexOrSelf_stepStar`
is `cases` on the `Option` + `fireRootRedex_sound`; `completeDevelopment_stepStar` is term-mode mutual
recursion composing `StepStar.ofChildrenStar`, `StepChildrenStar.here`/`there`/`trans_compose`, and
`StepStar.trans_compose`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Gated per declaration in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Fire the root redex, or keep the cell.**  Returns the reduct named by the matching `Step`
constructor when `mkGen generator payload children` is a root redex, otherwise the cell unchanged.
Non-recursive `Option.getD` over the propext-clean `RawTerm.fireRootRedex`. -/
def RawTerm.fireRootRedexOrSelf {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) : RawTerm scope :=
  (RawTerm.fireRootRedex generator payload children).getD
    (.mkGen generator payload children)

/-- **Gated root firing.**  Fire the root redex on the DEVELOPED children, but ONLY when the ORIGINAL
children already form a syntactic redex.  This is the gate that makes `completeDevelopment` the STANDARD
Takahashi development rather than an over-firing one: firing on developed children alone would also
contract redexes CREATED by developing the children (e.g. an inner redex whose contractum is a `lam`
turns the enclosing application into a β-redex), which is not a single parallel-reduction step.  Because
the redex-head constructors (`lam`, `boolTrue`/`boolFalse`, `pair`, `natZero`/`natSucc`, `listNil`/`listCons`,
`optionNone`/`optionSome`, `eitherInl`/`eitherInr`, `refl`) are never themselves root-redex generators,
developing the children preserves the head, so when the gate passes the developed children fire the SAME
redex shape — yielding exactly the contractum built from the developed components. -/
def RawTerm.fireRootRedexOrSelfGated {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (originalChildren developedChildren : RawTermChildren generator.binderShifts scope) :
    RawTerm scope :=
  match RawTerm.fireRootRedex generator payload originalChildren with
  | some _ => RawTerm.fireRootRedexOrSelf generator payload developedChildren
  | none => .mkGen generator payload developedChildren

mutual
/-- **Takahashi complete development.**  Contracts every redex present in `term` simultaneously —
develop all children, then fire the root redex once IF the source was a syntactic redex (the
`fireRootRedexOrSelfGated` gate) — but leaves redexes CREATED by the contraction untouched.  Propext-clean:
the redex-shape detection is delegated to `fireRootRedex`, so this is a single `mkGen` match. -/
def RawTerm.completeDevelopment {scope : Nat} : (term : RawTerm scope) → RawTerm scope
  | .mkGen generator payload children =>
      RawTerm.fireRootRedexOrSelfGated generator payload children
        (RawTerm.completeDevelopmentChildren children)

/-- Pointwise complete development of a children spine. -/
def RawTerm.completeDevelopmentChildren {binderShifts : List Nat} {scope : Nat} :
    (children : RawTermChildren binderShifts scope) → RawTermChildren binderShifts scope
  | .childNil => .childNil
  | .childCons childHead childTail =>
      .childCons (RawTerm.completeDevelopment childHead)
        (RawTerm.completeDevelopmentChildren childTail)
end

/-- **Root firing is reachable by `StepStar`.**  Either `fireRootRedex` fires a genuine `Step`
(soundness) — one star step — or it returns the cell unchanged (reflexivity). -/
theorem RawTerm.fireRootRedexOrSelf_stepStar {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope} :
    StepStar (.mkGen generator payload children)
      (RawTerm.fireRootRedexOrSelf generator payload children) := by
  unfold RawTerm.fireRootRedexOrSelf
  cases hFired : RawTerm.fireRootRedex generator payload children with
  | none => exact StepStar.refl _
  | some reduct => exact StepStar.single (RawTerm.fireRootRedex_sound hFired)

/-- **Gated root firing is reachable by `StepStar`** from the developed cell.  When the gate passes
(`some`), the developed cell `StepStar`-reduces to the fired reduct (`fireRootRedexOrSelf_stepStar`);
when it does not (`none`), the gated result IS the developed cell (reflexivity). -/
theorem RawTerm.fireRootRedexOrSelfGated_stepStar {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {originalChildren developedChildren : RawTermChildren generator.binderShifts scope} :
    StepStar (.mkGen generator payload developedChildren)
      (RawTerm.fireRootRedexOrSelfGated generator payload originalChildren developedChildren) := by
  unfold RawTerm.fireRootRedexOrSelfGated
  cases RawTerm.fireRootRedex generator payload originalChildren with
  | some _ => exact RawTerm.fireRootRedexOrSelf_stepStar
  | none => exact StepStar.refl _

mutual
/-- **The complete development is reachable from the source by `StepStar`.**  Develop all children
(a congruence chain lifted via `StepStar.ofChildrenStar`), then fire the root redex once
(`fireRootRedexOrSelf_stepStar`); compose with `StepStar.trans_compose`.  The soundness half of the
eventual maximal-reduct / triangle property toward raw confluence. -/
theorem RawTerm.completeDevelopment_stepStar {scope : Nat} :
    (term : RawTerm scope) → StepStar term (RawTerm.completeDevelopment term)
  | .mkGen _generator _payload children =>
      StepStar.trans_compose
        (StepStar.ofChildrenStar
          (RawTerm.completeDevelopmentChildren_stepChildrenStar children))
        RawTerm.fireRootRedexOrSelfGated_stepStar

/-- Pointwise children-spine companion of `completeDevelopment_stepStar`: each child `StepStar`-reduces
to its complete development, replayed through the spine via `here`/`there`/`trans_compose`. -/
theorem RawTerm.completeDevelopmentChildren_stepChildrenStar
    {binderShifts : List Nat} {scope : Nat} :
    (children : RawTermChildren binderShifts scope) →
    StepChildrenStar children (RawTerm.completeDevelopmentChildren children)
  | .childNil => StepChildrenStar.refl _
  | .childCons childHead childTail =>
      StepChildrenStar.trans_compose
        (StepChildrenStar.here childTail
          (RawTerm.completeDevelopment_stepStar childHead))
        (StepChildrenStar.there (RawTerm.completeDevelopment childHead)
          (RawTerm.completeDevelopmentChildren_stepChildrenStar childTail))
end

/-- **Triangle-readiness: the β-redex develops to `subst0` of the developed components.**  Holds by
`rfl` — the gate passes (`fireRootRedex` fires on the syntactic β-redex), the developed function child
`lam (cd body)` is still a `lam`, so the gated firing reduces to `subst0 (cd body) (cd arg)`.  This is
the exact equation the Takahashi triangle's β arm needs, and witnesses that the gated (non-over-firing)
development fires the source β-redex with the developed components — the property the over-firing version
also had for β but violated by additionally firing redexes created under non-`lam` heads. -/
theorem cd_app_lam_eq {scope : Nat} (domainAnn : RawTerm scope) (body : RawTerm (scope + 1))
    (arg : RawTerm scope) :
    RawTerm.completeDevelopment
      (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
          (.childCons arg .childNil)))
      = RawTerm.subst0 (RawTerm.completeDevelopment body) (RawTerm.completeDevelopment arg) := rfl

/-! ### ι reduction-rule equations.

The companions of `cd_app_lam_eq` for the sixteen ι-redexes: each pins down, by `rfl`, the developed
contractum the gated complete development produces for that syntactic redex.  The gate fires (the source
is a syntactic redex), the scrutinee/witness constructor develops to itself (it is not a root-redex
generator), and the developed children fire the matching `Step`/`ParStep` arm — yielding the contractum
built from the developed components.  These are the reduction rules the Takahashi triangle's β/ι arms
rewrite the goal's `completeDevelopment` with before firing the matching `ParStep` constructor. -/

theorem cd_boolElimTrue_eq {scope : Nat} (thenBranch elseBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_boolElim () (.childCons (.mkGen .gen_boolTrue () .childNil)
      (.childCons thenBranch (.childCons elseBranch .childNil)))) =
      RawTerm.completeDevelopment thenBranch := rfl

theorem cd_boolElimFalse_eq {scope : Nat} (thenBranch elseBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_boolElim () (.childCons (.mkGen .gen_boolFalse () .childNil)
      (.childCons thenBranch (.childCons elseBranch .childNil)))) =
      RawTerm.completeDevelopment elseBranch := rfl

theorem cd_fstPair_eq {scope : Nat} (firstValue secondValue : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_fst () (.childCons (.mkGen .gen_pair ()
      (.childCons firstValue (.childCons secondValue .childNil))) .childNil)) =
      RawTerm.completeDevelopment firstValue := rfl

theorem cd_sndPair_eq {scope : Nat} (firstValue secondValue : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_snd () (.childCons (.mkGen .gen_pair ()
      (.childCons firstValue (.childCons secondValue .childNil))) .childNil)) =
      RawTerm.completeDevelopment secondValue := rfl

theorem cd_natElimZero_eq {scope : Nat} (zeroBranch succBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_natElim () (.childCons (.mkGen .gen_natZero () .childNil)
      (.childCons zeroBranch (.childCons succBranch .childNil)))) =
      RawTerm.completeDevelopment zeroBranch := rfl

theorem cd_natRecZero_eq {scope : Nat} (zeroBranch succBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_natRec () (.childCons (.mkGen .gen_natZero () .childNil)
      (.childCons zeroBranch (.childCons succBranch .childNil)))) =
      RawTerm.completeDevelopment zeroBranch := rfl

theorem cd_listElimNil_eq {scope : Nat} (nilBranch consBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_listElim () (.childCons (.mkGen .gen_listNil () .childNil)
      (.childCons nilBranch (.childCons consBranch .childNil)))) =
      RawTerm.completeDevelopment nilBranch := rfl

theorem cd_optionMatchNone_eq {scope : Nat} (noneBranch someBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_optionMatch () (.childCons (.mkGen .gen_optionNone () .childNil)
      (.childCons noneBranch (.childCons someBranch .childNil)))) =
      RawTerm.completeDevelopment noneBranch := rfl

theorem cd_optionMatchSome_eq {scope : Nat} (value noneBranch someBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_optionMatch () (.childCons
      (.mkGen .gen_optionSome () (.childCons value .childNil))
      (.childCons noneBranch (.childCons someBranch .childNil)))) =
      .mkGen .gen_app () (.childCons (RawTerm.completeDevelopment someBranch)
        (.childCons (RawTerm.completeDevelopment value) .childNil)) := rfl

theorem cd_eitherMatchInl_eq {scope : Nat} (value leftBranch rightBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_eitherMatch () (.childCons
      (.mkGen .gen_eitherInl () (.childCons value .childNil))
      (.childCons leftBranch (.childCons rightBranch .childNil)))) =
      .mkGen .gen_app () (.childCons (RawTerm.completeDevelopment leftBranch)
        (.childCons (RawTerm.completeDevelopment value) .childNil)) := rfl

theorem cd_eitherMatchInr_eq {scope : Nat} (value leftBranch rightBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_eitherMatch () (.childCons
      (.mkGen .gen_eitherInr () (.childCons value .childNil))
      (.childCons leftBranch (.childCons rightBranch .childNil)))) =
      .mkGen .gen_app () (.childCons (RawTerm.completeDevelopment rightBranch)
        (.childCons (RawTerm.completeDevelopment value) .childNil)) := rfl

theorem cd_natElimSucc_eq {scope : Nat} (predecessor zeroBranch succBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_natElim () (.childCons
      (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
      (.childCons zeroBranch (.childCons succBranch .childNil)))) =
      .mkGen .gen_app () (.childCons
        (.mkGen .gen_app () (.childCons (RawTerm.completeDevelopment succBranch)
          (.childCons (RawTerm.completeDevelopment predecessor) .childNil)))
        (.childCons (.mkGen .gen_natElim () (.childCons (RawTerm.completeDevelopment predecessor)
          (.childCons (RawTerm.completeDevelopment zeroBranch)
            (.childCons (RawTerm.completeDevelopment succBranch) .childNil)))) .childNil)) := rfl

theorem cd_natRecSucc_eq {scope : Nat} (predecessor zeroBranch succBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_natRec () (.childCons
      (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
      (.childCons zeroBranch (.childCons succBranch .childNil)))) =
      .mkGen .gen_app () (.childCons
        (.mkGen .gen_app () (.childCons (RawTerm.completeDevelopment succBranch)
          (.childCons (RawTerm.completeDevelopment predecessor) .childNil)))
        (.childCons (.mkGen .gen_natRec () (.childCons (RawTerm.completeDevelopment predecessor)
          (.childCons (RawTerm.completeDevelopment zeroBranch)
            (.childCons (RawTerm.completeDevelopment succBranch) .childNil)))) .childNil)) := rfl

theorem cd_listElimCons_eq {scope : Nat} (headValue tailValue nilBranch consBranch : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_listElim () (.childCons
      (.mkGen .gen_listCons () (.childCons headValue (.childCons tailValue .childNil)))
      (.childCons nilBranch (.childCons consBranch .childNil)))) =
      .mkGen .gen_app () (.childCons
        (.mkGen .gen_app () (.childCons
          (.mkGen .gen_app () (.childCons (RawTerm.completeDevelopment consBranch)
            (.childCons (RawTerm.completeDevelopment headValue) .childNil)))
          (.childCons (RawTerm.completeDevelopment tailValue) .childNil)))
        (.childCons (.mkGen .gen_listElim () (.childCons (RawTerm.completeDevelopment tailValue)
          (.childCons (RawTerm.completeDevelopment nilBranch)
            (.childCons (RawTerm.completeDevelopment consBranch) .childNil)))) .childNil)) := rfl

theorem cd_idJRefl_eq {scope : Nat} (baseCase rawWitness : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_idJ () (.childCons baseCase
      (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))) =
      RawTerm.completeDevelopment baseCase := rfl

theorem cd_idStrictRecRefl_eq {scope : Nat} (baseCase rawWitness : RawTerm scope) :
    RawTerm.completeDevelopment (.mkGen .gen_idStrictRec () (.childCons baseCase
      (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))) =
      RawTerm.completeDevelopment baseCase := rfl

end FX1Poly.Core
