import FX1Poly.Polygraph.Computad.WordProblem
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainGodementStep
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.OrientedAtomSwap

/-! # SwapTrichotomy — every adjacent swap orients, or the lists are equal (FREE-6b, part 1)

The orientation-totality lemma the normal-form legs consume: for ANY adjacent atom swap,
the trace-vector comparison decides — the swap descends along its constructor direction,
descends against it, or the two lists are EQUAL.  The decision walks the tie tower on the
constructor data:

  1. `|fMid| + |inert| > 0` — the head columns differ; the left-zone-first order is smaller.
  2. `|gLow| > 0` — head columns tie; the right contexts at position 1 differ.
  3. generator keys differ at position 2 — order by key.
  4. `|fHigh| > 0` — position-3 columns differ.
  5. `|gMid| > 0` — position-4 right contexts differ.
  6. all five widths zero and keys equal — both generators are SCALARS in the same fiber
     (all four boundary modes collapse), `keyOf_injectiveOnFiber` identifies them, and the
     two lists coincide (the Eckmann–Hilton-adjacent configuration is a fixed point, not a
     step).

Positions 0/1 tie whenever the later cases are reached because the shared summands cancel:
each comparison collapses to a `Nat` fact about the five widths and two keys.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open FX1Poly.Core (LexListStep)

/-- ★ **Orientation totality**: any adjacent atom swap fires as an oriented step in exactly
one direction — or relates two EQUAL lists (the same-fiber scalar tie, identified by the
key's fiber injectivity). -/
theorem SpineAtomSwap.orientOrEqual {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList) :
    OrientedAtomStep keying firstList secondList
      ∨ OrientedAtomStep keying secondList firstList
      ∨ firstList = secondList := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath
      rightAcc rest =>
    have lenHeadTwo : (composePath (composePath leftAcc oneCellFMid) inertPath).length
        = leftAcc.length + oneCellFMid.length + inertPath.length := by
      rw [ModalityPath.length_composePath, ModalityPath.length_composePath]
    have lenRightCtxOne : (composePath (composePath inertPath oneCellGLow) rightAcc).length
        = inertPath.length + oneCellGLow.length + rightAcc.length := by
      rw [ModalityPath.length_composePath, ModalityPath.length_composePath]
    have lenAccOne : (composePath (composePath leftAcc oneCellFHigh) inertPath).length
        = leftAcc.length + oneCellFHigh.length + inertPath.length := by
      rw [ModalityPath.length_composePath, ModalityPath.length_composePath]
    have lenRightCtxTwo : (composePath (composePath inertPath oneCellGMid) rightAcc).length
        = inertPath.length + oneCellGMid.length + rightAcc.length := by
      rw [ModalityPath.length_composePath, ModalityPath.length_composePath]
    cases hInnerSum : oneCellFMid.length + inertPath.length with
    | succ predSum =>
        -- Case 1: the head columns differ — the left-zone-first list is lex-smaller,
        -- so the oriented step fires AGAINST the constructor direction.
        refine Or.inr (Or.inl (OrientedAtomStep.hereBackward
          (SpineAtomSwap.swap generatorLeft generatorRight leftAcc inertPath rightAcc rest)
          ⟨[], leftAcc.length,
            (composePath (composePath leftAcc oneCellFMid) inertPath).length,
            (composePath (composePath inertPath oneCellGLow) rightAcc).length ::
              keying.keyOf generatorLeft ::
              (composePath (composePath leftAcc oneCellFHigh) inertPath).length ::
              rightAcc.length :: keying.keyOf generatorRight ::
              spineTraceVector keying rest,
            rightAcc.length :: keying.keyOf generatorRight :: leftAcc.length ::
              (composePath (composePath inertPath oneCellGMid) rightAcc).length ::
              keying.keyOf generatorLeft :: spineTraceVector keying rest,
            rfl, rfl, rfl, ?_⟩))
        rw [lenHeadTwo, Nat.add_assoc, hInnerSum]
        exact Nat.add_lt_add_left (Nat.succ_pos predSum) leftAcc.length
    | zero =>
        obtain ⟨hMidZero, hInertZero⟩ :=
          sumEqZero_impliesComponentsZero oneCellFMid.length inertPath.length hInnerSum
        have headEntryTwoEq :
            (composePath (composePath leftAcc oneCellFMid) inertPath).length
              = leftAcc.length := by
          rw [lenHeadTwo, hMidZero, hInertZero]; rfl
        cases hLowWidth : oneCellGLow.length with
        | succ predWidth =>
            -- Case 2: position-1 right contexts differ — the constructor direction descends.
            refine Or.inl (OrientedAtomStep.hereForward
              (SpineAtomSwap.swap generatorLeft generatorRight leftAcc inertPath rightAcc
                rest)
              ⟨[leftAcc.length], rightAcc.length,
                (composePath (composePath inertPath oneCellGLow) rightAcc).length,
                keying.keyOf generatorRight :: leftAcc.length ::
                  (composePath (composePath inertPath oneCellGMid) rightAcc).length ::
                  keying.keyOf generatorLeft :: spineTraceVector keying rest,
                keying.keyOf generatorLeft ::
                  (composePath (composePath leftAcc oneCellFHigh) inertPath).length ::
                  rightAcc.length :: keying.keyOf generatorRight ::
                  spineTraceVector keying rest,
                rfl,
                congrArg (fun headEntry => headEntry :: rightAcc.length ::
                  keying.keyOf generatorRight :: leftAcc.length ::
                  (composePath (composePath inertPath oneCellGMid) rightAcc).length ::
                  keying.keyOf generatorLeft :: spineTraceVector keying rest)
                  headEntryTwoEq,
                rfl, ?_⟩)
            rw [lenRightCtxOne, hInertZero, hLowWidth, Nat.zero_add, Nat.succ_add]
            exact Nat.lt_succ_of_le (Nat.le_add_left rightAcc.length predWidth)
        | zero =>
            have rightCtxOneEq :
                (composePath (composePath inertPath oneCellGLow) rightAcc).length
                  = rightAcc.length := by
              rw [lenRightCtxOne, hInertZero, hLowWidth]
              exact Nat.zero_add rightAcc.length
            rcases Nat.lt_or_ge (keying.keyOf generatorLeft) (keying.keyOf generatorRight)
              with hKeyLt | hKeyGe
            · -- Case 3a: the left generator's key is smaller — fire backward.
              exact Or.inr (Or.inl (OrientedAtomStep.hereBackward
                (SpineAtomSwap.swap generatorLeft generatorRight leftAcc inertPath rightAcc
                  rest)
                ⟨[leftAcc.length, rightAcc.length], keying.keyOf generatorLeft,
                  keying.keyOf generatorRight,
                  (composePath (composePath leftAcc oneCellFHigh) inertPath).length ::
                    rightAcc.length :: keying.keyOf generatorRight ::
                    spineTraceVector keying rest,
                  leftAcc.length ::
                    (composePath (composePath inertPath oneCellGMid) rightAcc).length ::
                    keying.keyOf generatorLeft :: spineTraceVector keying rest,
                  congrArg (fun headEntry => headEntry :: rightAcc.length ::
                    keying.keyOf generatorRight :: leftAcc.length ::
                    (composePath (composePath inertPath oneCellGMid) rightAcc).length ::
                    keying.keyOf generatorLeft :: spineTraceVector keying rest)
                    headEntryTwoEq,
                  congrArg (fun rightCtxEntry => leftAcc.length :: rightCtxEntry ::
                    keying.keyOf generatorLeft ::
                    (composePath (composePath leftAcc oneCellFHigh) inertPath).length ::
                    rightAcc.length :: keying.keyOf generatorRight ::
                    spineTraceVector keying rest) rightCtxOneEq,
                  rfl, hKeyLt⟩))
            · rcases Nat.lt_or_ge (keying.keyOf generatorRight) (keying.keyOf generatorLeft)
                with hKeyGt | hKeyGeSecond
              · -- Case 3b: the right generator's key is smaller — fire forward.
                exact Or.inl (OrientedAtomStep.hereForward
                  (SpineAtomSwap.swap generatorLeft generatorRight leftAcc inertPath
                    rightAcc rest)
                  ⟨[leftAcc.length, rightAcc.length], keying.keyOf generatorRight,
                    keying.keyOf generatorLeft,
                    leftAcc.length ::
                      (composePath (composePath inertPath oneCellGMid) rightAcc).length ::
                      keying.keyOf generatorLeft :: spineTraceVector keying rest,
                    (composePath (composePath leftAcc oneCellFHigh) inertPath).length ::
                      rightAcc.length :: keying.keyOf generatorRight ::
                      spineTraceVector keying rest,
                    congrArg (fun rightCtxEntry => leftAcc.length :: rightCtxEntry ::
                      keying.keyOf generatorLeft ::
                      (composePath (composePath leftAcc oneCellFHigh) inertPath).length ::
                      rightAcc.length :: keying.keyOf generatorRight ::
                      spineTraceVector keying rest) rightCtxOneEq,
                    congrArg (fun headEntry => headEntry :: rightAcc.length ::
                      keying.keyOf generatorRight :: leftAcc.length ::
                      (composePath (composePath inertPath oneCellGMid) rightAcc).length ::
                      keying.keyOf generatorLeft :: spineTraceVector keying rest)
                      headEntryTwoEq,
                    rfl, hKeyGt⟩)
              · have hKeysEq : keying.keyOf generatorLeft = keying.keyOf generatorRight :=
                  Nat.le_antisymm hKeyGeSecond hKeyGe
                cases hHighWidth : oneCellFHigh.length with
                | succ predHigh =>
                    -- Case 4: position-3 columns differ — fire forward.
                    refine Or.inl (OrientedAtomStep.hereForward
                      (SpineAtomSwap.swap generatorLeft generatorRight leftAcc inertPath
                        rightAcc rest)
                      ⟨[leftAcc.length, rightAcc.length, keying.keyOf generatorLeft],
                        leftAcc.length,
                        (composePath (composePath leftAcc oneCellFHigh) inertPath).length,
                        (composePath (composePath inertPath oneCellGMid) rightAcc).length ::
                          keying.keyOf generatorLeft :: spineTraceVector keying rest,
                        rightAcc.length :: keying.keyOf generatorRight ::
                          spineTraceVector keying rest,
                        congrArg (fun rightCtxEntry => leftAcc.length :: rightCtxEntry ::
                          keying.keyOf generatorLeft ::
                          (composePath (composePath leftAcc oneCellFHigh) inertPath).length
                          :: rightAcc.length :: keying.keyOf generatorRight ::
                          spineTraceVector keying rest) rightCtxOneEq,
                        (congrArg (fun headEntry => headEntry :: rightAcc.length ::
                          keying.keyOf generatorRight :: leftAcc.length ::
                          (composePath (composePath inertPath oneCellGMid) rightAcc).length
                          :: keying.keyOf generatorLeft :: spineTraceVector keying rest)
                          headEntryTwoEq).trans
                          (congrArg (fun keyEntry => leftAcc.length :: rightAcc.length ::
                            keyEntry :: leftAcc.length ::
                            (composePath (composePath inertPath oneCellGMid)
                              rightAcc).length ::
                            keying.keyOf generatorLeft :: spineTraceVector keying rest)
                            hKeysEq.symm),
                        rfl, ?_⟩)
                    rw [lenAccOne, hInertZero, hHighWidth]
                    exact Nat.add_lt_add_left (Nat.succ_pos predHigh) leftAcc.length
                | zero =>
                    have accOneEq :
                        (composePath (composePath leftAcc oneCellFHigh) inertPath).length
                          = leftAcc.length := by
                      rw [lenAccOne, hHighWidth, hInertZero]; rfl
                    cases hMidWidth : oneCellGMid.length with
                    | succ predMid =>
                        -- Case 5: position-4 right contexts differ — fire backward.
                        refine Or.inr (Or.inl (OrientedAtomStep.hereBackward
                          (SpineAtomSwap.swap generatorLeft generatorRight leftAcc
                            inertPath rightAcc rest)
                          ⟨[leftAcc.length, rightAcc.length,
                              keying.keyOf generatorLeft, leftAcc.length],
                            rightAcc.length,
                            (composePath (composePath inertPath oneCellGMid)
                              rightAcc).length,
                            keying.keyOf generatorRight :: spineTraceVector keying rest,
                            keying.keyOf generatorLeft :: spineTraceVector keying rest,
                            (congrArg (fun headEntry => headEntry :: rightAcc.length ::
                              keying.keyOf generatorRight :: leftAcc.length ::
                              (composePath (composePath inertPath oneCellGMid)
                                rightAcc).length ::
                              keying.keyOf generatorLeft :: spineTraceVector keying rest)
                              headEntryTwoEq).trans
                              (congrArg (fun keyEntry => leftAcc.length ::
                                rightAcc.length :: keyEntry :: leftAcc.length ::
                                (composePath (composePath inertPath oneCellGMid)
                                  rightAcc).length ::
                                keying.keyOf generatorLeft ::
                                spineTraceVector keying rest) hKeysEq.symm),
                            (congrArg (fun rightCtxEntry => leftAcc.length ::
                              rightCtxEntry :: keying.keyOf generatorLeft ::
                              (composePath (composePath leftAcc oneCellFHigh)
                                inertPath).length ::
                              rightAcc.length :: keying.keyOf generatorRight ::
                              spineTraceVector keying rest) rightCtxOneEq).trans
                              (congrArg (fun accEntry => leftAcc.length ::
                                rightAcc.length :: keying.keyOf generatorLeft :: accEntry
                                :: rightAcc.length :: keying.keyOf generatorRight ::
                                spineTraceVector keying rest) accOneEq),
                            rfl, ?_⟩))
                        rw [lenRightCtxTwo, hInertZero, hMidWidth, Nat.zero_add,
                          Nat.succ_add]
                        exact Nat.lt_succ_of_le (Nat.le_add_left rightAcc.length predMid)
                    | zero =>
                        -- Case 6: all five widths zero, keys equal — the same-fiber
                        -- scalar tie.  The boundary paths are all `nil`, the fiber
                        -- injectivity identifies the generators, and the two lists
                        -- coincide.
                        refine Or.inr (Or.inr ?_)
                        have composeNilRight : ∀ {startMode endMode : signature.graph.Mode}
                            (path : ModalityPath signature.graph startMode endMode),
                            composePath path (ModalityPath.nil endMode) = path :=
                          fun path => composePath_identityPath_right path
                        cases oneCellFMid with
                        | cons _ _ => exact Nat.noConfusion hMidZero
                        | nil _ =>
                            cases inertPath with
                            | cons _ _ => exact Nat.noConfusion hInertZero
                            | nil _ =>
                                cases oneCellGLow with
                                | cons _ _ => exact Nat.noConfusion hLowWidth
                                | nil _ =>
                                    cases oneCellFHigh with
                                    | cons _ _ => exact Nat.noConfusion hHighWidth
                                    | nil _ =>
                                        cases oneCellGMid with
                                        | cons _ _ => exact Nat.noConfusion hMidWidth
                                        | nil _ =>
                                            cases keying.keyOf_injectiveOnFiber
                                              generatorLeft generatorRight hKeysEq
                                            have leftCtxCollapse :
                                                composePath (composePath leftAcc
                                                    (ModalityPath.nil swapSourceMode))
                                                  (ModalityPath.nil swapSourceMode)
                                                  = leftAcc :=
                                              (congrArg (fun innerPath => composePath
                                                  innerPath
                                                  (ModalityPath.nil swapSourceMode))
                                                (composeNilRight leftAcc)).trans
                                                (composeNilRight leftAcc)
                                            rw [leftCtxCollapse]
                                            rfl

end FX1Poly.Polygraph
