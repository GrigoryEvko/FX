import FX1Poly.OmegacE.AbsorptionConfluence

/-! # FX1Poly/OmegacE/AbsorptionLocalConfluence
    — local + global confluence of the two-rule absorption system

The confluence capstone, assembled from the building blocks in `AbsorptionConfluence` (decomposition, the
`[v,s,v]` critical-pair join, the disjoint-commute helper):

* `absorptionJoinableWhenLeftShorter` — when the left redex is the shorter prefix, the two `[s,s]`-reducts are
  joinable.  `listPrefixSplit` after `rcases`-ing the two rule shapes (4 combos), then the overlap `mid`
  trichotomy: `[]` (same position — matched ⟹ equal reducts, mismatched ⟹ `v=s` absurd); `[m]` (one-cell
  overlap — the `[v,s,v]` critical pair joins via `absorptionCriticalPairJoinLeftRight`, the `[s,v,s]` overlap
  has both reducts equal to `[s,s,s]`, matched combos absurd); `m::m2::mid'` (disjoint ⟹ `absorptionJoinableDisjoint`).
* `absorptionHasLocalConfluence` — decompose both reducts of a common source, then `Nat.le_total` dispatches
  the eight leaves to `absorptionJoinableWhenLeftShorter` (or its `.symm`).
* `absorptionHasConfluence` — `newman` on the local confluence plus the shipped `absorptionSystem_isTerminating`.
  This makes the absorption system the FIRST fully-CONFLUENT two-rule presentation with genuine inter-rule
  critical pairs (the Newman demonstration).  Only the decidable word problem (a two-rule `WordReducer`)
  remains to close the system.

## Zero-axiom verification

All three theorems verified `#print axioms`-clean in scratch before landing.  The disjoint cons-cons leaves bridge
the injection's cons-form reduct to the disjoint helper's append-form via `← doubleConsAppend` + `← listAppendAssoc`
(no `simp`).  Per-decl gated in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- When the left redex is the shorter prefix, the two `[s,s]`-reducts are joinable.  Prefix-split, rcases
the two rule shapes (4 combos), then the overlap `mid` trichotomy: `[]` (same position — matched ⟹ equal
reducts, mismatched ⟹ `v=s` absurd); `[m]` (one-cell overlap — `[v,s,v]` critical pair joins via the
shipped lemma, `[s,v,s]` reducts both `[s,s,s]`, matched ⟹ absurd); `m::m2::mid'` (disjoint ⟹ the
commute helper). -/
theorem absorptionJoinableWhenLeftShorter {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) (distinct : vanishingCell ≠ survivingCell)
    (leftA rightA leftB rightB pairA pairB : List (OmegacECell dimension))
    (hPairA : pairA = [vanishingCell, survivingCell] ∨ pairA = [survivingCell, vanishingCell])
    (hPairB : pairB = [vanishingCell, survivingCell] ∨ pairB = [survivingCell, vanishingCell])
    (hEq : leftA ++ pairA ++ rightA = leftB ++ pairB ++ rightB)
    (hLen : leftA.length ≤ leftB.length) :
    OmegacEWord.Joinable (absorptionSystem vanishingCell survivingCell)
      ⟨leftA ++ [survivingCell, survivingCell] ++ rightA⟩
      ⟨leftB ++ [survivingCell, survivingCell] ++ rightB⟩ := by
  have notVS : vanishingCell = survivingCell → False := distinct
  have notSV : survivingCell = vanishingCell → False := fun h => distinct h.symm
  rcases hPairA with hA | hA <;> rcases hPairB with hB | hB <;> subst hA <;> subst hB <;>
    rw [listAppendAssoc, listAppendAssoc] at hEq
  -- (L,L): pairA = pairB = [v,s]
  · obtain ⟨mid, hMid, hRest⟩ :=
      listPrefixSplit leftA leftB ([vanishingCell, survivingCell] ++ rightA)
        ([vanishingCell, survivingCell] ++ rightB) hEq hLen
    rw [doubleConsAppend, doubleConsAppend] at hRest
    cases mid with
    | nil =>
        rw [List.nil_append] at hRest
        injection hRest with _ hRest1
        injection hRest1 with _ hRights
        subst hRights; subst hMid
        apply joinable_of_wordEq; apply congrArg OmegacEWord.mk; rw [listAppendNil]
    | cons m midTail =>
        cases midTail with
        | nil =>
            rw [List.cons_append, List.nil_append] at hRest
            injection hRest with _hm hRest1
            injection hRest1 with hsv _
            exact absurd hsv notSV
        | cons m2 mid' =>
            rw [List.cons_append, List.cons_append] at hRest
            injection hRest with hm1 hRest1
            injection hRest1 with hm2 hRights
            subst hm1; subst hm2; subst hRights; subst hMid
            rw [← doubleConsAppend vanishingCell survivingCell rightB,
                ← listAppendAssoc mid' [vanishingCell, survivingCell] rightB,
                ← doubleConsAppend vanishingCell survivingCell mid',
                ← listAppendAssoc leftA [vanishingCell, survivingCell] mid']
            exact absorptionJoinableDisjoint vanishingCell survivingCell leftA mid' rightB
              [vanishingCell, survivingCell] [vanishingCell, survivingCell] (Or.inl rfl) (Or.inl rfl)
  -- (L,R): pairA = [v,s], pairB = [s,v]  — the genuine [v,s,v] critical pair
  · obtain ⟨mid, hMid, hRest⟩ :=
      listPrefixSplit leftA leftB ([vanishingCell, survivingCell] ++ rightA)
        ([survivingCell, vanishingCell] ++ rightB) hEq hLen
    rw [doubleConsAppend, doubleConsAppend] at hRest
    cases mid with
    | nil =>
        rw [List.nil_append] at hRest
        injection hRest with hvs _
        exact absurd hvs notVS
    | cons m midTail =>
        cases midTail with
        | nil =>
            rw [List.cons_append, List.nil_append] at hRest
            injection hRest with hm hRest1
            injection hRest1 with _ hRA
            subst hm; subst hMid; subst hRA
            have e1 :
                (⟨leftA ++ [survivingCell, survivingCell] ++ (vanishingCell :: rightB)⟩
                  : OmegacEWord dimension)
                = ⟨leftA ++ [survivingCell, survivingCell, vanishingCell] ++ rightB⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc leftA [survivingCell, survivingCell] (vanishingCell :: rightB),
                  doubleConsAppend,
                  listAppendAssoc leftA [survivingCell, survivingCell, vanishingCell] rightB,
                  tripleConsAppend]
            have e2 :
                (⟨(leftA ++ [vanishingCell]) ++ [survivingCell, survivingCell] ++ rightB⟩
                  : OmegacEWord dimension)
                = ⟨leftA ++ [vanishingCell, survivingCell, survivingCell] ++ rightB⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc (leftA ++ [vanishingCell]) [survivingCell, survivingCell] rightB,
                  listAppendAssoc leftA [vanishingCell]
                    ([survivingCell, survivingCell] ++ rightB),
                  singleConsAppend, doubleConsAppend,
                  listAppendAssoc leftA [vanishingCell, survivingCell, survivingCell] rightB,
                  tripleConsAppend]
            rw [e1, e2]
            exact absorptionCriticalPairJoinLeftRight vanishingCell survivingCell leftA rightB
        | cons m2 mid' =>
            rw [List.cons_append, List.cons_append] at hRest
            injection hRest with hm1 hRest1
            injection hRest1 with hm2 hRights
            subst hm1; subst hm2; subst hRights; subst hMid
            rw [← doubleConsAppend survivingCell vanishingCell rightB,
                ← listAppendAssoc mid' [survivingCell, vanishingCell] rightB,
                ← doubleConsAppend vanishingCell survivingCell mid',
                ← listAppendAssoc leftA [vanishingCell, survivingCell] mid']
            exact absorptionJoinableDisjoint vanishingCell survivingCell leftA mid' rightB
              [vanishingCell, survivingCell] [survivingCell, vanishingCell] (Or.inl rfl) (Or.inr rfl)
  -- (R,L): pairA = [s,v], pairB = [v,s]  — the [s,v,s] overlap, both reducts [s,s,s]
  · obtain ⟨mid, hMid, hRest⟩ :=
      listPrefixSplit leftA leftB ([survivingCell, vanishingCell] ++ rightA)
        ([vanishingCell, survivingCell] ++ rightB) hEq hLen
    rw [doubleConsAppend, doubleConsAppend] at hRest
    cases mid with
    | nil =>
        rw [List.nil_append] at hRest
        injection hRest with hsv _
        exact absurd hsv notSV
    | cons m midTail =>
        cases midTail with
        | nil =>
            rw [List.cons_append, List.nil_append] at hRest
            injection hRest with hm hRest1
            injection hRest1 with _ hRA
            subst hm; subst hMid; subst hRA
            apply joinable_of_wordEq; apply congrArg OmegacEWord.mk
            rw [listAppendAssoc leftA [survivingCell, survivingCell] (survivingCell :: rightB),
                doubleConsAppend,
                listAppendAssoc (leftA ++ [survivingCell]) [survivingCell, survivingCell] rightB,
                listAppendAssoc leftA [survivingCell] ([survivingCell, survivingCell] ++ rightB),
                singleConsAppend, doubleConsAppend]
        | cons m2 mid' =>
            rw [List.cons_append, List.cons_append] at hRest
            injection hRest with hm1 hRest1
            injection hRest1 with hm2 hRights
            subst hm1; subst hm2; subst hRights; subst hMid
            rw [← doubleConsAppend vanishingCell survivingCell rightB,
                ← listAppendAssoc mid' [vanishingCell, survivingCell] rightB,
                ← doubleConsAppend survivingCell vanishingCell mid',
                ← listAppendAssoc leftA [survivingCell, vanishingCell] mid']
            exact absorptionJoinableDisjoint vanishingCell survivingCell leftA mid' rightB
              [survivingCell, vanishingCell] [vanishingCell, survivingCell] (Or.inr rfl) (Or.inl rfl)
  -- (R,R): pairA = pairB = [s,v]
  · obtain ⟨mid, hMid, hRest⟩ :=
      listPrefixSplit leftA leftB ([survivingCell, vanishingCell] ++ rightA)
        ([survivingCell, vanishingCell] ++ rightB) hEq hLen
    rw [doubleConsAppend, doubleConsAppend] at hRest
    cases mid with
    | nil =>
        rw [List.nil_append] at hRest
        injection hRest with _ hRest1
        injection hRest1 with _ hRights
        subst hRights; subst hMid
        apply joinable_of_wordEq; apply congrArg OmegacEWord.mk; rw [listAppendNil]
    | cons m midTail =>
        cases midTail with
        | nil =>
            rw [List.cons_append, List.nil_append] at hRest
            injection hRest with _hm hRest1
            injection hRest1 with hvs _
            exact absurd hvs notVS
        | cons m2 mid' =>
            rw [List.cons_append, List.cons_append] at hRest
            injection hRest with hm1 hRest1
            injection hRest1 with hm2 hRights
            subst hm1; subst hm2; subst hRights; subst hMid
            rw [← doubleConsAppend survivingCell vanishingCell rightB,
                ← listAppendAssoc mid' [survivingCell, vanishingCell] rightB,
                ← doubleConsAppend survivingCell vanishingCell mid',
                ← listAppendAssoc leftA [survivingCell, vanishingCell] mid']
            exact absorptionJoinableDisjoint vanishingCell survivingCell leftA mid' rightB
              [survivingCell, vanishingCell] [survivingCell, vanishingCell] (Or.inr rfl) (Or.inr rfl)

/-- **The absorption system is locally confluent** (requires `v ≠ s`). -/
theorem absorptionHasLocalConfluence {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) (distinct : vanishingCell ≠ survivingCell) :
    HasLocalConfluence (absorptionSystem vanishingCell survivingCell) := by
  intro sourceWord firstReduct secondReduct step1 step2
  obtain ⟨leftA, rightA, hTgtA, hSrcA⟩ :=
    absorptionRewriteOneStep_decomposition vanishingCell survivingCell step1
  obtain ⟨leftB, rightB, hTgtB, hSrcB⟩ :=
    absorptionRewriteOneStep_decomposition vanishingCell survivingCell step2
  have hFirst : firstReduct = ⟨leftA ++ [survivingCell, survivingCell] ++ rightA⟩ := by rw [← hTgtA]
  have hSecond : secondReduct = ⟨leftB ++ [survivingCell, survivingCell] ++ rightB⟩ := by rw [← hTgtB]
  rw [hFirst, hSecond]
  -- extract the two source pairs + the common source equality
  rcases hSrcA with hsa | hsa <;> rcases hSrcB with hsb | hsb
  all_goals
    rcases Nat.le_total leftA.length leftB.length with hle | hle
  -- For each of the 8 leaves, hsa/hsb give the concrete source forms; build hEq and dispatch.
  · exact absorptionJoinableWhenLeftShorter vanishingCell survivingCell distinct
      leftA rightA leftB rightB _ _ (Or.inl rfl) (Or.inl rfl) (hsa.symm.trans hsb) hle
  · exact (absorptionJoinableWhenLeftShorter vanishingCell survivingCell distinct
      leftB rightB leftA rightA _ _ (Or.inl rfl) (Or.inl rfl) (hsb.symm.trans hsa) hle).symm
  · exact absorptionJoinableWhenLeftShorter vanishingCell survivingCell distinct
      leftA rightA leftB rightB _ _ (Or.inl rfl) (Or.inr rfl) (hsa.symm.trans hsb) hle
  · exact (absorptionJoinableWhenLeftShorter vanishingCell survivingCell distinct
      leftB rightB leftA rightA _ _ (Or.inr rfl) (Or.inl rfl) (hsb.symm.trans hsa) hle).symm
  · exact absorptionJoinableWhenLeftShorter vanishingCell survivingCell distinct
      leftA rightA leftB rightB _ _ (Or.inr rfl) (Or.inl rfl) (hsa.symm.trans hsb) hle
  · exact (absorptionJoinableWhenLeftShorter vanishingCell survivingCell distinct
      leftB rightB leftA rightA _ _ (Or.inl rfl) (Or.inr rfl) (hsb.symm.trans hsa) hle).symm
  · exact absorptionJoinableWhenLeftShorter vanishingCell survivingCell distinct
      leftA rightA leftB rightB _ _ (Or.inr rfl) (Or.inr rfl) (hsa.symm.trans hsb) hle
  · exact (absorptionJoinableWhenLeftShorter vanishingCell survivingCell distinct
      leftB rightB leftA rightA _ _ (Or.inr rfl) (Or.inr rfl) (hsb.symm.trans hsa) hle).symm

/-- **The absorption system is CONFLUENT** (requires `v ≠ s`) — newman on local confluence + termination. -/
theorem absorptionHasConfluence {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) (distinct : vanishingCell ≠ survivingCell) :
    HasConfluence (absorptionSystem vanishingCell survivingCell) :=
  newman (absorptionHasLocalConfluence vanishingCell survivingCell distinct)
    (absorptionSystem_isTerminating vanishingCell survivingCell distinct)

end FX1Poly.OmegacE
