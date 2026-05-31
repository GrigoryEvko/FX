import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.StepSubst

/-! # Foundation/PolyCell/Core/ConvCongruence
   — generic Conv-as-congruence lifter (one theorem for all 194 generators)

Ships the per-generator Conv-level congruence rules (#369).  The
surrounding substrate provides:

* `Conv.refl` + `Conv.sym` at `StepStarConfluence.lean`.
* 4 conditional `Conv.trans_of_*` variants.
* Three hand-coded StepStar-level congruence helpers:
  `StepStar.appFunction`, `StepStar.appArgument`, `StepStar.lamBody`.

A Conv-level congruence rule is what `HasType.conv`, typed SR, and
Conv-respecting term-replacement reasoning all build on.

## What this file ships

Rather than ship 194 hand-coded rules, ship ONE generic lifter
that subsumes them all via the PolyCell uniformity thesis:

```
ConvChildren : RawTermChildren shifts scope →
               RawTermChildren shifts scope → Prop
ConvChildren.exists_join : ConvChildren L R →
  ∃ commons, StepChildrenStar L commons ∧ StepChildrenStar R commons
Conv.ofChildren : ConvChildren L R →
  Conv (mkGen gen p L) (mkGen gen p R)
```

Plus per-position corollaries for the ~10 most-cited generators:
* `Conv.app_cong`, `Conv.lam_cong`, `Conv.pair_cong`
* `Conv.fst_cong`, `Conv.snd_cong`
* `Conv.natSucc_cong`, `Conv.listCons_cong`
* `Conv.optionSome_cong`, `Conv.eitherInl_cong`, `Conv.eitherInr_cong`
* `Conv.gen_refl_cong` (distinguished from `Conv.refl` reflexivity by
  the `_cong` suffix and `gen_` prefix to make the name unambiguous)

## Proof technique

The generic theorem extracts the per-position `StepStar.Join` from
each child's `Conv`, then RECURSIVELY ASSEMBLES a common spine via
`StepChildrenStar.here` (head reduction at fixed rest) plus
`StepChildrenStar.there` (tail reduction at fixed head) plus
`StepChildrenStar.trans_compose` (chain composition).  The parent
`Conv` then follows from `StepStar.ofChildrenStar` applied to each
leg.

Substrate consumed:
* `Conv` / `Conv.refl` / `Conv.sym` from `StepStarConfluence.lean`.
* `StepStar.Join` definition (∃ common, StepStar L common ∧ StepStar R common).
* `StepChildrenStar` inductive + `.here` + `.there` + `.trans_compose`
  from `StepSubst.lean:1151-1209`.
* `StepStar.ofChildrenStar` from `StepSubst.lean:1213-1224` — lifts a
  child-spine chain to a parent generator-application chain.

## Zero-axiom verification

All declarations close by `induction` on `ConvChildren` (Prop-to-Prop,
no large elimination) or by direct ctor construction.  No `simp`, no
`omega`, no `propext`, no `Classical.choice`.  Audit-gated.

## Consumers

* Typed Subject Reduction: cites `Conv.ofChildren` to lift child
  Conv to parent Conv under any typing-context shape.
* Typed weakening + substitution: cites per-ctor corollaries.
* Conv subst/rename preservation: extends to substitution/renaming.
* The Conv `Equivalence` instance: composes with refl/symm/trans.
* Typed beta+eta Decidable Conv: relies on Conv being a congruence
  to lift eta-long readback comparisons. -/

namespace FX1Poly.Core

/-- Pointwise `Conv` on a child spine.  Each child position carries
its own `Conv` witness.  Indexed by `binderShifts` and `scope` to
match `RawTermChildren`'s indexing. -/
inductive ConvChildren : ∀ {binderShifts : List Nat} {scope : Nat},
    RawTermChildren binderShifts scope →
    RawTermChildren binderShifts scope → Prop where
  /-- Empty spines are trivially pointwise-Conv. -/
  | nilC {scope : Nat} :
      ConvChildren (.childNil : RawTermChildren [] scope) .childNil
  /-- A head Conv plus a tail ConvChildren produces a cons-level
  pointwise-Conv. -/
  | consC {scope shift : Nat} {restShifts : List Nat}
      {headLeft headRight : RawTerm (scope + shift)}
      {restLeft restRight : RawTermChildren restShifts scope}
      (headConv : Conv headLeft headRight)
      (restConv : ConvChildren restLeft restRight) :
      ConvChildren (.childCons headLeft restLeft)
                   (.childCons headRight restRight)

namespace ConvChildren

/-- Pointwise symmetry: pointwise-Conv is symmetric.  Induction is
on the ConvChildren proof (Prop-to-Prop), not on the RawTermChildren
spine (which is mutually inductive with RawTerm and therefore not
directly supported by Lean's `induction` tactic). -/
theorem symm {binderShifts : List Nat} {scope : Nat}
    {leftChildren rightChildren : RawTermChildren binderShifts scope}
    (pointwise : ConvChildren leftChildren rightChildren) :
    ConvChildren rightChildren leftChildren := by
  induction pointwise with
  | nilC => exact ConvChildren.nilC
  | consC headConv _ restIH =>
      exact ConvChildren.consC (Conv.sym headConv) restIH

/-- **Bridge to children-level Join.** Pointwise `Conv` on a spine
extracts to a JOINT child-spine reduct: there exists a common spine
that both left and right reduce to via `StepChildrenStar`.

This is the load-bearing structural lemma: the per-position joins
get ASSEMBLED into a single common spine by recursive composition.

Proof structure:
* `nilC`: common spine is `.childNil`, both legs are `refl`.
* `consC headConv restConv` (IH): extract `headCommon` from
  `headConv`'s Join + `restCommons` from `restIH`'s Join.  The
  common spine is `.childCons headCommon restCommons`.  Each leg
  composes:
  * `StepChildrenStar.here` reduces the head while fixing the rest
    (giving `childCons headSrc restSrc →* childCons headCommon
    restSrc`).
  * `StepChildrenStar.there` reduces the rest while fixing the
    head (giving `childCons headCommon restSrc →* childCons
    headCommon restCommons`).
  * `trans_compose` chains them. -/
theorem exists_join {binderShifts : List Nat} {scope : Nat}
    {leftChildren rightChildren : RawTermChildren binderShifts scope}
    (pointwise : ConvChildren leftChildren rightChildren) :
    ∃ commonChildren,
      StepChildrenStar leftChildren commonChildren ∧
      StepChildrenStar rightChildren commonChildren := by
  induction pointwise with
  | nilC =>
      exact ⟨.childNil, StepChildrenStar.refl _, StepChildrenStar.refl _⟩
  | @consC scope shift restShifts headLeft headRight restLeft restRight
          headConv _ restIH =>
      obtain ⟨restCommons, restLeftChain, restRightChain⟩ := restIH
      obtain ⟨headCommon, headLeftChain, headRightChain⟩ := headConv
      refine ⟨.childCons headCommon restCommons, ?_, ?_⟩
      · -- left leg: childCons headLeft restLeft →* childCons headCommon restCommons
        exact StepChildrenStar.trans_compose
          (StepChildrenStar.here restLeft headLeftChain)
          (StepChildrenStar.there headCommon restLeftChain)
      · -- right leg: childCons headRight restRight →* childCons headCommon restCommons
        exact StepChildrenStar.trans_compose
          (StepChildrenStar.here restRight headRightChain)
          (StepChildrenStar.there headCommon restRightChain)

end ConvChildren

/-- **Generic Conv-congruence lifter (the M-Conv-cong headline).**

Given pointwise `Conv` on the children of a generator application,
`Conv` lifts to the parent application.  ONE theorem covering ALL
194 generators by exploiting the Generator-table structure — the
PolyCell uniformity payoff at the Conv level.

Proof:
1. Extract `commonChildren` + per-leg `StepChildrenStar` via
   `ConvChildren.exists_join`.
2. Build the parent common term `mkGen generator payload commonChildren`.
3. Lift each per-leg `StepChildrenStar` to parent `StepStar` via
   `StepStar.ofChildrenStar`.
4. Package as `Conv` (i.e., `StepStar.Join`). -/
theorem Conv.ofChildren {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {leftChildren rightChildren :
      RawTermChildren generator.binderShifts scope}
    (pointwise : ConvChildren leftChildren rightChildren) :
    Conv (.mkGen generator payload leftChildren)
         (.mkGen generator payload rightChildren) := by
  obtain ⟨commonChildren, leftChain, rightChain⟩ := pointwise.exists_join
  exact ⟨.mkGen generator payload commonChildren,
         StepStar.ofChildrenStar leftChain,
         StepStar.ofChildrenStar rightChain⟩

/-! ## Per-generator congruence corollaries

Each `Conv.<gen>_cong` is a one-line specialization of
`Conv.ofChildren` to a specific Generator's spine shape.  The
spine is assembled by `ConvChildren.consC` chained with
`ConvChildren.nilC` at the tail.

These corollaries are the API surface most downstream code will
use; the generic `Conv.ofChildren` is the load-bearing theorem
they all delegate to. -/

/-- **Conv-congruence for `gen_app`.** -/
theorem Conv.app_cong {scope : Nat}
    {functionLeft functionRight argumentLeft argumentRight : RawTerm scope}
    (functionConv : Conv functionLeft functionRight)
    (argumentConv : Conv argumentLeft argumentRight) :
    Conv (.mkGen .gen_app ()
           (.childCons functionLeft (.childCons argumentLeft .childNil)))
         (.mkGen .gen_app ()
           (.childCons functionRight (.childCons argumentRight .childNil))) :=
  Conv.ofChildren (ConvChildren.consC functionConv
                    (ConvChildren.consC argumentConv ConvChildren.nilC))

/-- **Conv-congruence for `gen_lam`.** -/
theorem Conv.lam_cong {scope : Nat}
    {bodyLeft bodyRight : RawTerm (scope + 1)}
    (bodyConv : Conv bodyLeft bodyRight) :
    Conv (.mkGen .gen_lam () (.childCons bodyLeft .childNil) :
            RawTerm scope)
         (.mkGen .gen_lam () (.childCons bodyRight .childNil) :
            RawTerm scope) :=
  Conv.ofChildren (ConvChildren.consC bodyConv ConvChildren.nilC)

/-- **Conv-congruence for `gen_pair`.** -/
theorem Conv.pair_cong {scope : Nat}
    {firstLeft firstRight secondLeft secondRight : RawTerm scope}
    (firstConv : Conv firstLeft firstRight)
    (secondConv : Conv secondLeft secondRight) :
    Conv (.mkGen .gen_pair ()
           (.childCons firstLeft (.childCons secondLeft .childNil)))
         (.mkGen .gen_pair ()
           (.childCons firstRight (.childCons secondRight .childNil))) :=
  Conv.ofChildren (ConvChildren.consC firstConv
                    (ConvChildren.consC secondConv ConvChildren.nilC))

/-- **Conv-congruence for `gen_fst`.** -/
theorem Conv.fst_cong {scope : Nat}
    {argLeft argRight : RawTerm scope}
    (argConv : Conv argLeft argRight) :
    Conv (.mkGen .gen_fst () (.childCons argLeft .childNil))
         (.mkGen .gen_fst () (.childCons argRight .childNil)) :=
  Conv.ofChildren (ConvChildren.consC argConv ConvChildren.nilC)

/-- **Conv-congruence for `gen_snd`.** -/
theorem Conv.snd_cong {scope : Nat}
    {argLeft argRight : RawTerm scope}
    (argConv : Conv argLeft argRight) :
    Conv (.mkGen .gen_snd () (.childCons argLeft .childNil))
         (.mkGen .gen_snd () (.childCons argRight .childNil)) :=
  Conv.ofChildren (ConvChildren.consC argConv ConvChildren.nilC)

/-- **Conv-congruence for `gen_natSucc`.** -/
theorem Conv.natSucc_cong {scope : Nat}
    {predLeft predRight : RawTerm scope}
    (predConv : Conv predLeft predRight) :
    Conv (.mkGen .gen_natSucc () (.childCons predLeft .childNil))
         (.mkGen .gen_natSucc () (.childCons predRight .childNil)) :=
  Conv.ofChildren (ConvChildren.consC predConv ConvChildren.nilC)

/-- **Conv-congruence for `gen_listCons`.** -/
theorem Conv.listCons_cong {scope : Nat}
    {headLeft headRight tailLeft tailRight : RawTerm scope}
    (headConv : Conv headLeft headRight)
    (tailConv : Conv tailLeft tailRight) :
    Conv (.mkGen .gen_listCons ()
           (.childCons headLeft (.childCons tailLeft .childNil)))
         (.mkGen .gen_listCons ()
           (.childCons headRight (.childCons tailRight .childNil))) :=
  Conv.ofChildren (ConvChildren.consC headConv
                    (ConvChildren.consC tailConv ConvChildren.nilC))

/-- **Conv-congruence for `gen_optionSome`.** -/
theorem Conv.optionSome_cong {scope : Nat}
    {valueLeft valueRight : RawTerm scope}
    (valueConv : Conv valueLeft valueRight) :
    Conv (.mkGen .gen_optionSome () (.childCons valueLeft .childNil))
         (.mkGen .gen_optionSome () (.childCons valueRight .childNil)) :=
  Conv.ofChildren (ConvChildren.consC valueConv ConvChildren.nilC)

/-- **Conv-congruence for `gen_eitherInl`.** -/
theorem Conv.eitherInl_cong {scope : Nat}
    {valueLeft valueRight : RawTerm scope}
    (valueConv : Conv valueLeft valueRight) :
    Conv (.mkGen .gen_eitherInl () (.childCons valueLeft .childNil))
         (.mkGen .gen_eitherInl () (.childCons valueRight .childNil)) :=
  Conv.ofChildren (ConvChildren.consC valueConv ConvChildren.nilC)

/-- **Conv-congruence for `gen_eitherInr`.** -/
theorem Conv.eitherInr_cong {scope : Nat}
    {valueLeft valueRight : RawTerm scope}
    (valueConv : Conv valueLeft valueRight) :
    Conv (.mkGen .gen_eitherInr () (.childCons valueLeft .childNil))
         (.mkGen .gen_eitherInr () (.childCons valueRight .childNil)) :=
  Conv.ofChildren (ConvChildren.consC valueConv ConvChildren.nilC)

/-- **Conv-congruence for `gen_refl`** (the identity-type refl
constructor, NOT to be confused with `Conv.refl` reflexivity). -/
theorem Conv.gen_refl_cong {scope : Nat}
    {witnessLeft witnessRight : RawTerm scope}
    (witnessConv : Conv witnessLeft witnessRight) :
    Conv (.mkGen .gen_refl () (.childCons witnessLeft .childNil))
         (.mkGen .gen_refl () (.childCons witnessRight .childNil)) :=
  Conv.ofChildren (ConvChildren.consC witnessConv ConvChildren.nilC)

end FX1Poly.Core
