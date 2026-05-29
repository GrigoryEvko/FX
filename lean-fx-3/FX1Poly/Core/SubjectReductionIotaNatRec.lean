import FX1Poly.Core.CertifiedToPolyCell
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaNatRec — nat elimination/recursor step iotas

V2-L3.1 phase D step 12 (2026-05-27).  Ships SR arms 14-15:

  * iotaNatElimSucc : `natElim (natSucc n) z s ↝ app (app s n) (natElim n z s)`
  * iotaNatRecSucc  : `natRec  (natSucc n) z s ↝ app (app s n) (natRec  n z s)`

## What's new vs. the single-payload compound iotas

The eitherMatch / optionMatchSome arms (sibling commits a8f3c45a /
81aeae69) built a SINGLE `gen_app ()` target with 2 children
(branch + extracted value).  These arms build a more complex
NESTED structure:

```
target =
  gen_app
    [ gen_app [succBranch, predecessor]
    , gen_natElim [predecessor, zeroBranch, succBranch]
    ]
```

Two levels of `gen_app` nesting plus a recursive `gen_natElim`
that REUSES the source's zeroBranch and succBranch.  The
recursive call appears as a syntactic sub-term (the v2 iota
rule's "structural recursion" presentation, NOT subst-based).

## Key construction insight: branches reused twice

The proof extracts `zeroBranchCell` and `succBranchCell` from
the outer spine, then uses them in BOTH the inner `gen_app` AND
the recursive `gen_natElim`.  Lean has no linearity restriction;
the same extracted certified cell value can populate multiple
spine positions in the target.

## Audit-gated

`#assert_no_axioms` on both theorems.

After this commit: 16/18 SR arms shipped.  Remaining: `beta`
(uses V2-L2.12 subst preservation) and `cong` (structural
induction over child Step + spine).

(Plus a sibling `iotaListElimCons` arm at the same proof template
— 3-arg nested app — in the file's third theorem.)
-/

namespace FX1Poly.Core

/-- **SR arm: `Step.iotaNatElimSucc` preserves `HasCertifiedCellDim0`.**

Target builds `app (app succBranch predecessor) (natElim
predecessor zeroBranch succBranch)` — two nested apps + recursive
natElim. -/
theorem HasCertifiedCellDim0.preservedByIotaNatElimSucc
    {profile : PolyProfile} {scope : Nat}
    {predecessor zeroBranch succBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_natElim ()
          (.childCons
            (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
            (.childCons zeroBranch
              (.childCons succBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons succBranch (.childCons predecessor .childNil)))
          (.childCons
            (.mkGen .gen_natElim ()
              (.childCons predecessor
                (.childCons zeroBranch
                  (.childCons succBranch .childNil))))
            .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons natSuccCell restAfterNatSucc =>
        cases restAfterNatSucc with
        | cons zeroBranchCell restAfterZero =>
          cases restAfterZero with
          | cons succBranchCell _ =>
            generalize hSort :
                (ChildSpec.termSameScope.cellSort) = innerSort
              at natSuccCell
            cases natSuccCell with
            | gen _ _ natSuccInnerSpine =>
              cases natSuccInnerSpine with
              | cons predecessorCell _ =>
                -- Build inner gen_app cell: spine [succBranch, predecessor].
                let innerAppCell :=
                  PolyCell.gen
                    SupportedGenerator.gen_app
                    (genPayloadEvidence (generator := .gen_app)
                                         (scope := scope) ())
                    (CertifiedTermSpine.cons succBranchCell
                      (CertifiedTermSpine.cons predecessorCell
                        CertifiedTermSpine.nil))
                -- Build recursive gen_natElim cell: spine
                -- [predecessor, zeroBranch, succBranch].
                -- (Branches reused from source's outer spine.)
                let innerNatElimCell :=
                  PolyCell.gen
                    SupportedGenerator.gen_natElim
                    (genPayloadEvidence (generator := .gen_natElim)
                                         (scope := scope) ())
                    (CertifiedTermSpine.cons predecessorCell
                      (CertifiedTermSpine.cons zeroBranchCell
                        (CertifiedTermSpine.cons succBranchCell
                          CertifiedTermSpine.nil)))
                -- Outer gen_app: spine [innerAppCell, innerNatElimCell].
                exact .intro .term
                  (PolyCell.gen
                    SupportedGenerator.gen_app
                    (genPayloadEvidence (generator := .gen_app)
                                         (scope := scope) ())
                    (CertifiedTermSpine.cons innerAppCell
                      (CertifiedTermSpine.cons innerNatElimCell
                        CertifiedTermSpine.nil)))

/-- **SR arm: `Step.iotaNatRecSucc` preserves `HasCertifiedCellDim0`.**

Symmetric to `iotaNatElimSucc`: the substrate treats `gen_natElim`
and `gen_natRec` identically (same arity, same binderShifts).
Only differences: outer source generator is `gen_natRec`, and the
recursive call rebuilds with `gen_natRec`. -/
theorem HasCertifiedCellDim0.preservedByIotaNatRecSucc
    {profile : PolyProfile} {scope : Nat}
    {predecessor zeroBranch succBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_natRec ()
          (.childCons
            (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
            (.childCons zeroBranch
              (.childCons succBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons succBranch (.childCons predecessor .childNil)))
          (.childCons
            (.mkGen .gen_natRec ()
              (.childCons predecessor
                (.childCons zeroBranch
                  (.childCons succBranch .childNil))))
            .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons natSuccCell restAfterNatSucc =>
        cases restAfterNatSucc with
        | cons zeroBranchCell restAfterZero =>
          cases restAfterZero with
          | cons succBranchCell _ =>
            generalize hSort :
                (ChildSpec.termSameScope.cellSort) = innerSort
              at natSuccCell
            cases natSuccCell with
            | gen _ _ natSuccInnerSpine =>
              cases natSuccInnerSpine with
              | cons predecessorCell _ =>
                let innerAppCell :=
                  PolyCell.gen
                    SupportedGenerator.gen_app
                    (genPayloadEvidence (generator := .gen_app)
                                         (scope := scope) ())
                    (CertifiedTermSpine.cons succBranchCell
                      (CertifiedTermSpine.cons predecessorCell
                        CertifiedTermSpine.nil))
                let innerNatRecCell :=
                  PolyCell.gen
                    SupportedGenerator.gen_natRec
                    (genPayloadEvidence (generator := .gen_natRec)
                                         (scope := scope) ())
                    (CertifiedTermSpine.cons predecessorCell
                      (CertifiedTermSpine.cons zeroBranchCell
                        (CertifiedTermSpine.cons succBranchCell
                          CertifiedTermSpine.nil)))
                exact .intro .term
                  (PolyCell.gen
                    SupportedGenerator.gen_app
                    (genPayloadEvidence (generator := .gen_app)
                                         (scope := scope) ())
                    (CertifiedTermSpine.cons innerAppCell
                      (CertifiedTermSpine.cons innerNatRecCell
                        CertifiedTermSpine.nil)))

/-- **SR arm: `Step.iotaListElimCons` preserves `HasCertifiedCellDim0`.**

Three nested `gen_app`s plus a recursive `gen_listElim`:

```
target =
  gen_app
    [ gen_app
        [ gen_app [consBranch, headVal]
        , tailVal
        ]
    , gen_listElim [tailVal, nilBranch, consBranch]
    ]
```

The wrapper has 2 payloads (head and tail), so the inner-spine
destructure binds BOTH after `cases natSuccInnerSpine` analog. -/
theorem HasCertifiedCellDim0.preservedByIotaListElimCons
    {profile : PolyProfile} {scope : Nat}
    {headVal tailVal nilBranch consBranch : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_listElim ()
          (.childCons
            (.mkGen .gen_listCons ()
              (.childCons headVal (.childCons tailVal .childNil)))
            (.childCons nilBranch
              (.childCons consBranch .childNil)))
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons consBranch (.childCons headVal .childNil)))
              (.childCons tailVal .childNil)))
          (.childCons
            (.mkGen .gen_listElim ()
              (.childCons tailVal
                (.childCons nilBranch
                  (.childCons consBranch .childNil))))
            .childNil))) := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons listConsCell restAfterListCons =>
        cases restAfterListCons with
        | cons nilBranchCell restAfterNil =>
          cases restAfterNil with
          | cons consBranchCell _ =>
            generalize hSort :
                (ChildSpec.termSameScope.cellSort) = innerSort
              at listConsCell
            cases listConsCell with
            | gen _ _ listConsInnerSpine =>
              cases listConsInnerSpine with
              | cons headValCell restListConsInner =>
                cases restListConsInner with
                | cons tailValCell _ =>
                  -- Build innermost: app(consBranch, headVal).
                  let app1Cell :=
                    PolyCell.gen
                      SupportedGenerator.gen_app
                      (genPayloadEvidence (generator := .gen_app)
                                           (scope := scope) ())
                      (CertifiedTermSpine.cons consBranchCell
                        (CertifiedTermSpine.cons headValCell
                          CertifiedTermSpine.nil))
                  -- Build middle: app(app1, tailVal).
                  let app2Cell :=
                    PolyCell.gen
                      SupportedGenerator.gen_app
                      (genPayloadEvidence (generator := .gen_app)
                                           (scope := scope) ())
                      (CertifiedTermSpine.cons app1Cell
                        (CertifiedTermSpine.cons tailValCell
                          CertifiedTermSpine.nil))
                  -- Build recursive: listElim(tailVal, nilBranch, consBranch).
                  let recCell :=
                    PolyCell.gen
                      SupportedGenerator.gen_listElim
                      (genPayloadEvidence (generator := .gen_listElim)
                                           (scope := scope) ())
                      (CertifiedTermSpine.cons tailValCell
                        (CertifiedTermSpine.cons nilBranchCell
                          (CertifiedTermSpine.cons consBranchCell
                            CertifiedTermSpine.nil)))
                  -- Outer: app(app2, recCell).
                  exact .intro .term
                    (PolyCell.gen
                      SupportedGenerator.gen_app
                      (genPayloadEvidence (generator := .gen_app)
                                           (scope := scope) ())
                      (CertifiedTermSpine.cons app2Cell
                        (CertifiedTermSpine.cons recCell
                          CertifiedTermSpine.nil)))

end FX1Poly.Core
