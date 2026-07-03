import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision

/-! # mode-3 — the partner-scan semantics kit (the extract→view reconstruction's foundation)

`extractDiagram`'s partner field records, for each boundary index, the FIRST other in-range
index sharing its union-find component (`findPartnerScan`, defaulting to the index itself when
its component is a boundary singleton).  Reconstructing the connectivity VIEW from an extract
equality needs the scan's semantics as theorems:

  * `findPartnerScan_root_ofFound` — soundness: a scan result differing from the exclude was
    FOUND, so its boundary node shares the scanned root;
  * `findPartnerScan_neExclude_ofTarget` — completeness: any scanned candidate other than the
    exclude sharing the root forces the scan to find SOMETHING;
  * ★ `findPartnerScan_excludeAgree` — the exclude-agreement trichotomy: two scans over the
    same list at the same root with different excludes either land on each other's exclude or
    agree — the first passing candidate serves both scans unless it IS one of the excludes.
    This is what makes the boundary same-component relation recoverable from the partner map
    without materializing "first element of the component".

The next brick consumes this kit: the per-state characterization of `matchingSameComponent`
as a Boolean function of the extracted partner list, and the reconstruction
`MatchingConnectivityViewSim` from `extractDiagram` equality.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Boolean plumbing (hand-rolled; core equivalents hide behind iffs or leak) -/

private theorem andFalse_eq_false : (flag : Bool) → (flag && false) = false
  | true => rfl
  | false => rfl

private theorem bneEqTrue_ofBeqFalse {leftValue rightValue : Nat}
    (beqFalse : (leftValue == rightValue) = false) : (leftValue != rightValue) = true := by
  show (!(leftValue == rightValue)) = true
  rw [beqFalse]
  rfl

private theorem bneEqFalse_ofBeqTrue {leftValue rightValue : Nat}
    (beqTrue : (leftValue == rightValue) = true) : (leftValue != rightValue) = false := by
  show (!(leftValue == rightValue)) = false
  rw [beqTrue]
  rfl

private theorem ne_ofBneTrue {leftValue rightValue : Nat}
    (bneTrue : (leftValue != rightValue) = true) : leftValue ≠ rightValue := fun valuesEq => by
  have selfBne : (rightValue != rightValue) = false := by
    show (!(rightValue == rightValue)) = false
    have selfBeq : (rightValue == rightValue) = true := decide_eq_true rfl
    rw [selfBeq]
    rfl
  rw [valuesEq, selfBne] at bneTrue
  exact Bool.noConfusion bneTrue

private theorem eq_ofBneFalse {leftValue rightValue : Nat}
    (bneFalse : (leftValue != rightValue) = false) : leftValue = rightValue := by
  cases hBeq : (leftValue == rightValue) with
  | true => exact of_decide_eq_true hBeq
  | false =>
      have bneTrue : (leftValue != rightValue) = true := bneEqTrue_ofBeqFalse hBeq
      rw [bneFalse] at bneTrue
      exact Bool.noConfusion bneTrue

/-! ## The scan's one-step unfold -/

/-- The definitional cons unfold of `findPartnerScan`, as a rewrite rule. -/
theorem findPartnerScan_cons (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (rootHere excludeIndex candidate : Nat) (rest : List Nat) :
    findPartnerScan links boundaryNodes rootHere excludeIndex (candidate :: rest)
      = if candidate != excludeIndex
            && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere
        then candidate
        else findPartnerScan links boundaryNodes rootHere excludeIndex rest := rfl

/-! ## Soundness: a found partner shares the scanned root -/

/-- **Scan soundness**: a scan result differing from the exclude was found by the root test,
so its boundary node's root IS the scanned root. -/
theorem findPartnerScan_root_ofFound (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (rootHere excludeIndex : Nat) : (scanned : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex scanned ≠ excludeIndex →
    unionFindRootOf links (natListGetAt boundaryNodes
        (findPartnerScan links boundaryNodes rootHere excludeIndex scanned))
      = rootHere
  | [], foundNe => absurd rfl foundNe
  | candidate :: rest, foundNe => by
      rw [findPartnerScan_cons] at foundNe ⊢
      cases hNe : (candidate != excludeIndex) with
      | false =>
          rw [hNe] at foundNe
          exact findPartnerScan_root_ofFound links boundaryNodes rootHere excludeIndex rest
            foundNe
      | true =>
          cases hRoot : (unionFindRootOf links (natListGetAt boundaryNodes candidate)
              == rootHere) with
          | false =>
              rw [hNe, hRoot] at foundNe
              exact findPartnerScan_root_ofFound links boundaryNodes rootHere excludeIndex
                rest foundNe
          | true => exact of_decide_eq_true hRoot

/-! ## Completeness: a valid target forces a find -/

/-- **Scan completeness**: when the scanned list contains a candidate other than the exclude
whose boundary node shares the scanned root, the scan result differs from the exclude. -/
theorem findPartnerScan_neExclude_ofTarget (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) :
    (scanned : List Nat) → (target : Nat) → target ∈ scanned → target ≠ excludeIndex →
    unionFindRootOf links (natListGetAt boundaryNodes target) = rootHere →
    findPartnerScan links boundaryNodes rootHere excludeIndex scanned ≠ excludeIndex
  | [], _, targetMem, _, _ => nomatch targetMem
  | candidate :: rest, target, targetMem, targetNe, targetRoot => by
      rw [findPartnerScan_cons]
      cases hNe : (candidate != excludeIndex) with
      | false =>
          cases targetMem with
          | head => exact absurd (eq_ofBneFalse hNe) targetNe
          | tail _ memRest =>
              exact findPartnerScan_neExclude_ofTarget links boundaryNodes rootHere
                excludeIndex rest target memRest targetNe targetRoot
      | true =>
          cases hRoot : (unionFindRootOf links (natListGetAt boundaryNodes candidate)
              == rootHere) with
          | true => exact ne_ofBneTrue hNe
          | false =>
              cases targetMem with
              | head =>
                  have rootBeq : (unionFindRootOf links
                      (natListGetAt boundaryNodes candidate) == rootHere) = true :=
                    decide_eq_true targetRoot
                  rw [hRoot] at rootBeq
                  exact Bool.noConfusion rootBeq
              | tail _ memRest =>
                  exact findPartnerScan_neExclude_ofTarget links boundaryNodes rootHere
                    excludeIndex rest target memRest targetNe targetRoot

/-! ## The exclude-agreement trichotomy -/

/-- ★ **Exclude agreement**: two scans over the same list at the same root with different
excludes, both finding something, either land on each other's exclude or AGREE — the first
passing candidate serves both scans unless it is one of the excludes. -/
theorem findPartnerScan_excludeAgree (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (rootHere firstExclude secondExclude : Nat) : (scanned : List Nat) →
    findPartnerScan links boundaryNodes rootHere firstExclude scanned ≠ firstExclude →
    findPartnerScan links boundaryNodes rootHere secondExclude scanned ≠ secondExclude →
    findPartnerScan links boundaryNodes rootHere firstExclude scanned = secondExclude
      ∨ findPartnerScan links boundaryNodes rootHere secondExclude scanned = firstExclude
      ∨ findPartnerScan links boundaryNodes rootHere firstExclude scanned
          = findPartnerScan links boundaryNodes rootHere secondExclude scanned
  | [], firstFound, _ => absurd rfl firstFound
  | candidate :: rest, firstFound, secondFound => by
      rw [findPartnerScan_cons links boundaryNodes rootHere firstExclude candidate rest]
        at firstFound
      rw [findPartnerScan_cons links boundaryNodes rootHere secondExclude candidate rest]
        at secondFound
      rw [findPartnerScan_cons links boundaryNodes rootHere firstExclude candidate rest,
        findPartnerScan_cons links boundaryNodes rootHere secondExclude candidate rest]
      cases hRoot : (unionFindRootOf links (natListGetAt boundaryNodes candidate)
          == rootHere) with
      | false =>
          rw [hRoot, andFalse_eq_false (candidate != firstExclude)] at firstFound
          rw [hRoot, andFalse_eq_false (candidate != secondExclude)] at secondFound
          rw [andFalse_eq_false (candidate != firstExclude),
            andFalse_eq_false (candidate != secondExclude)]
          exact findPartnerScan_excludeAgree links boundaryNodes rootHere firstExclude
            secondExclude rest firstFound secondFound
      | true =>
          cases hEqF : (candidate == firstExclude) with
          | true =>
              have bneF : (candidate != firstExclude) = false := bneEqFalse_ofBeqTrue hEqF
              rw [hRoot, bneF] at firstFound
              rw [bneF]
              cases hEqS : (candidate == secondExclude) with
              | true =>
                  have bneS : (candidate != secondExclude) = false :=
                    bneEqFalse_ofBeqTrue hEqS
                  rw [hRoot, bneS] at secondFound
                  rw [bneS]
                  exact findPartnerScan_excludeAgree links boundaryNodes rootHere
                    firstExclude secondExclude rest firstFound secondFound
              | false =>
                  have bneS : (candidate != secondExclude) = true := bneEqTrue_ofBeqFalse hEqS
                  rw [bneS]
                  exact Or.inr (Or.inl (of_decide_eq_true hEqF))
          | false =>
              have bneF : (candidate != firstExclude) = true := bneEqTrue_ofBeqFalse hEqF
              rw [bneF]
              cases hEqS : (candidate == secondExclude) with
              | true => exact Or.inl (of_decide_eq_true hEqS)
              | false =>
                  have bneS : (candidate != secondExclude) = true := bneEqTrue_ofBeqFalse hEqS
                  rw [bneS]
                  exact Or.inr (Or.inr rfl)

/-! ## Honesty marker -/

/-- **Honesty marker — the partner-scan semantics kit is SHIPPED.**  The cons unfold, scan
soundness (a found partner shares the scanned root), scan completeness (a valid target forces
a find), and the exclude-agreement trichotomy (two same-root scans with different excludes
land on each other's exclude or agree).  NOT yet covered: the per-state Boolean
characterization of `matchingSameComponent` in terms of the extracted partner list and the
reconstruction of `MatchingConnectivityViewSim` from `extractDiagram` equality — the next
MODE3-C brick.  `= true`. -/
def fxMode_hasMatchingPartnerScanKit : Bool := true

end FX1Poly.Polygraph
