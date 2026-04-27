import FX.Derived.Session
import FX.Kernel.Reduction

/-!
# Session ν reduction bridge tests (task S7)

Closes the bridge between S9 (SessionType → CoindSpec translation)
and A5 (ν reduction on `coindDestruct` / `coindUnfold`).  A5's
kernel tests pin ν on hand-rolled `"Stream"` specs; the
`Tests.Derived.SessionTranslateTests` pin the *output shape* of
translated specs; neither exercises **driving reduction through a
translated spec's name** — that is the S7 gap.

These tests construct concrete `Term.coindUnfold` values whose
`specName` is taken from `Session.translate`'s `rootName` output,
then apply `Term.coindDestruct` at the destructor indices the
spec declares, and verify `whnf` reduces as expected.  Arms are
arbitrary marker terms; reduction cares only about shape, not
typing.

All checks are compile-time `example` assertions via
`native_decide`, matching the style of
`Tests.Derived.SessionTranslateTests`.  Kernel reduction uses
`partial def whnf`, so `native_decide` is required.
-/

namespace Tests.Derived.SessionReductionTests

open FX.Derived.Session
open FX.Kernel
open FX.Kernel.Term

/-! ## Helpers -/

/-- `Nat` inductive used as an arbitrary payload / arm marker
    in the tests below.  Shape-only — no values are constructed. -/
private def natPayload : Term := Term.ind "Nat" []

/-- A second distinct marker term used for index-1 arm bodies;
    chosen to be structurally unequal to `natPayload` so arm
    selection is observable. -/
private def unitMarker : Term := Term.ind "Unit" []

/-- A third distinct marker for three-armed tests. -/
private def boolMarker : Term := Term.ind "Bool" []

/-- Local term-equality helper — avoids importing the one from
    ReductionTests. -/
private def termsEq (leftTerm rightTerm : Term) : Bool :=
  leftTerm == rightTerm

/-! ## endS / stop — no ν-redex exists

Terminal specs have zero destructors, so `coindDestruct` at any
index on their unfold is already stuck (no arm to pick).  Even
index 0 doesn't fire because the unfold's `arms` list is empty.
-/

-- endS: destruct at index 0 on an empty-arms unfold stays stuck.
example :
  let rootName := (translate "EndCh" SessionType.endS).rootName
  let unfold   := Term.coindUnfold rootName [] []
  let destruct := Term.coindDestruct rootName 0 unfold
  termsEq (Term.whnf 10 destruct) destruct = true := by native_decide

-- stop: same behavior — zero destructors, no ν-redex.
example :
  let rootName := (translate "StopCh" SessionType.stop).rootName
  let unfold   := Term.coindUnfold rootName [] []
  let destruct := Term.coindDestruct rootName 0 unfold
  termsEq (Term.whnf 10 destruct) destruct = true := by native_decide

/-! ## send / recv — single destructor at index 0 -/

-- send(Nat, end): root spec has one destructor named "send".
-- coindDestruct at index 0 on a one-arm unfold ν-reduces to the arm.
example :
  let result   := translate "SendCh" (SessionType.send natPayload .endS)
  let rootName := result.rootName
  let arm      := unitMarker
  let unfold   := Term.coindUnfold rootName [] [arm]
  let destruct := Term.coindDestruct rootName 0 unfold
  termsEq (Term.whnf 10 destruct) arm = true := by native_decide

-- recv(Nat, end): same shape as send — one destructor, index 0.
example :
  let result   := translate "RecvCh" (SessionType.recv natPayload .endS)
  let rootName := result.rootName
  let arm      := boolMarker
  let unfold   := Term.coindUnfold rootName [] [arm]
  let destruct := Term.coindDestruct rootName 0 unfold
  termsEq (Term.whnf 10 destruct) arm = true := by native_decide

-- Using the wrong spec name against a translated root: stays stuck.
-- The translator produces `SendCh_1` as the root; here we destruct
-- with a different name, verifying the spec-name defensive guard
-- still fires on translated specs.
example :
  let result   := translate "SendCh" (SessionType.send natPayload .endS)
  let rootName := result.rootName
  let wrongName := "NotTheRealName"
  let arm      := unitMarker
  let unfold   := Term.coindUnfold rootName [] [arm]
  let destruct := Term.coindDestruct wrongName 0 unfold
  termsEq (Term.whnf 10 destruct) destruct = true := by native_decide

-- Out-of-bounds index on a single-destructor send spec: stays stuck.
example :
  let result   := translate "SendCh" (SessionType.send natPayload .endS)
  let rootName := result.rootName
  let arm      := unitMarker
  let unfold   := Term.coindUnfold rootName [] [arm]
  let destruct := Term.coindDestruct rootName 5 unfold
  termsEq (Term.whnf 10 destruct) destruct = true := by native_decide

/-! ## selectS / offerS — destructor per branch label

`selectS` and `offerS` produce a spec with one destructor per
branch label, in declaration order.  The kernel doesn't know the
label — it indexes into the destructor list.  These tests pin
that index 0 selects the first branch, index 1 the second, and
that an out-of-bounds index stays stuck.
-/

-- selectS [("a", end), ("b", end)]: two destructors at indices 0, 1.
-- coindDestruct at index 0 picks the first arm.
example :
  let sessions := SessionType.selectS [("a", .endS), ("b", .endS)]
  let rootName := (translate "SelCh" sessions).rootName
  let arm0     := natPayload
  let arm1     := unitMarker
  let unfold   := Term.coindUnfold rootName [] [arm0, arm1]
  let destruct := Term.coindDestruct rootName 0 unfold
  termsEq (Term.whnf 10 destruct) arm0 = true := by native_decide

-- Same setup, index 1: picks the second arm.
example :
  let sessions := SessionType.selectS [("a", .endS), ("b", .endS)]
  let rootName := (translate "SelCh" sessions).rootName
  let arm0     := natPayload
  let arm1     := unitMarker
  let unfold   := Term.coindUnfold rootName [] [arm0, arm1]
  let destruct := Term.coindDestruct rootName 1 unfold
  termsEq (Term.whnf 10 destruct) arm1 = true := by native_decide

-- offerS has the same kernel shape as selectS — duality is at
-- the session level, not at the CoindSpec level.  Same index
-- behavior applies.
example :
  let sessions := SessionType.offerS [("hit", .endS), ("miss", .endS)]
  let rootName := (translate "OffCh" sessions).rootName
  let arm0     := natPayload
  let arm1     := unitMarker
  let unfold   := Term.coindUnfold rootName [] [arm0, arm1]
  termsEq (Term.whnf 10 (Term.coindDestruct rootName 0 unfold)) arm0 = true := by
  native_decide

example :
  let sessions := SessionType.offerS [("hit", .endS), ("miss", .endS)]
  let rootName := (translate "OffCh" sessions).rootName
  let arm0     := natPayload
  let arm1     := unitMarker
  let unfold   := Term.coindUnfold rootName [] [arm0, arm1]
  termsEq (Term.whnf 10 (Term.coindDestruct rootName 1 unfold)) arm1 = true := by
  native_decide

-- Three-branch selectS: index 2 picks the third arm.
example :
  let sessions := SessionType.selectS
    [("a", .endS), ("b", .endS), ("c", .endS)]
  let rootName := (translate "ThreeSel" sessions).rootName
  let arm0     := natPayload
  let arm1     := unitMarker
  let arm2     := boolMarker
  let unfold   := Term.coindUnfold rootName [] [arm0, arm1, arm2]
  termsEq (Term.whnf 10 (Term.coindDestruct rootName 2 unfold)) arm2 = true := by
  native_decide

-- Three-branch selectS with OOB index 3 — stays stuck.
example :
  let sessions := SessionType.selectS
    [("a", .endS), ("b", .endS), ("c", .endS)]
  let rootName := (translate "ThreeSel" sessions).rootName
  let arm0     := natPayload
  let arm1     := unitMarker
  let arm2     := boolMarker
  let unfold   := Term.coindUnfold rootName [] [arm0, arm1, arm2]
  let destruct := Term.coindDestruct rootName 3 unfold
  termsEq (Term.whnf 10 destruct) destruct = true := by native_decide

/-! ## loopS / continueS — self-referential spec

A `loopS body` reserves a spec name and translates its body with
that name assigned.  `continueS` inside the body refers to the
reserved name.  The shape-of-the-spec tests live in
SessionTranslateTests; here we pin that ν reduction works against
the loop's reserved root name.
-/

-- loopS (send Nat continueS): root is the loop's reserved name,
-- spec has one "send" destructor whose continuation points back
-- to the loop.  ν fires at the loop's root.
example :
  let sessions := SessionType.loopS (.send natPayload .continueS)
  let rootName := (translate "LoopCh" sessions).rootName
  let arm      := unitMarker
  let unfold   := Term.coindUnfold rootName [] [arm]
  termsEq (Term.whnf 10 (Term.coindDestruct rootName 0 unfold)) arm = true := by
  native_decide

/-! ## β ∘ ν composition via translated specs

`whnf` reduces the destructor's target to whnf before ν-stepping.
When the target is `(λ_. unfold ...) x`, β fires first, the
exposed unfold is reached, then ν fires on the translated spec.
Verifies the dispatch order is preserved for translated
specifications.
-/

-- β then ν: destruct ((λ_. unfold arm) x) → arm.
example :
  let result   := translate "SendCh" (SessionType.send natPayload .endS)
  let rootName := result.rootName
  let arm      := unitMarker
  let unfold   := Term.coindUnfold rootName [] [arm]
  let betaApp  := Term.app (Term.lam Grade.default natPayload unfold) natPayload
  let destruct := Term.coindDestruct rootName 0 betaApp
  termsEq (Term.whnf 20 destruct) arm = true := by native_decide

/-! ## normalize descends into translated-spec unfolds

An unfold at a translated root reached in whnf is already a value
form; `normalize` recurses into its arms.  Pins that a β-redex
nested inside an arm is reduced while the outer unfold's spec
name is preserved.
-/

-- normalize reduces (λ_. arm0) x inside a translated-spec unfold.
example :
  let result    := translate "SendCh" (SessionType.send natPayload .endS)
  let rootName  := result.rootName
  let arm0      := unitMarker
  let innerBeta := Term.app (Term.lam Grade.default natPayload arm0) natPayload
  let before    := Term.coindUnfold rootName [] [innerBeta]
  let after     := Term.coindUnfold rootName [] [arm0]
  termsEq (Term.normalize 20 before) after = true := by native_decide

end Tests.Derived.SessionReductionTests
