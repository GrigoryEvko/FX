import FX1Poly.Core.FireRootRedex

/-! # FX1Poly/Core/OneStepReducts
    — the kernel one-step reduct enumeration, with SOUNDNESS (COST-3 brick 2)

The reduct enumeration over the 198-generator table — the substrate the
worst-case cost bound (`costBound`, the next brick) folds over.  A term's
one-step reducts are exactly: the root reduct when the term is a β/ι
redex (`fireRootRedex`), plus every reassembly of the cell with ONE child
stepped (the congruence positions, mutual over the children spine).

  * `RawTerm.oneStepReducts` / `RawTermChildren.oneStepChildrenReducts` —
    the mutual enumeration (root match + per-position child maps).
  * ★ SOUNDNESS — every listed element is a genuine `Step` (root via
    `fireRootRedex_sound`, congruence via `Step.cong` over the mutual
    `StepChildren` soundness).
  * Generic hand-rolled membership INVERSION lemmas (`listMemAppendInv` /
    `listMemMapInv`) — core `List.mem_append`/`mem_map` are unaudited for
    axioms, so they are rolled by list induction with explicit
    `List.Mem` constructors (the COST-1 discipline, now generic).
  * Non-vacuity: the identity-β fixture's enumeration computes to
    exactly the singleton β-reduct, by kernel evaluation.

COMPLETENESS (every `Step` is listed — the direction the cost bound's
soundness consumes) is the next brick: the congruence half is the mirror
induction with FORWARD membership lemmas; the root half needs the
fireRootRedex completeness counterpart (each β/ι `Step` constructor fires
the extractor).

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open Foundation

/-! ## Generic membership inversion (hand-rolled, explicit `List.Mem`) -/

/-- Membership in an append comes from one of the sides (hand-rolled by
list induction; the core lemma's axiom status is unaudited). -/
theorem listMemAppendInv {α : Type} {element : α} :
    ∀ (firstList secondList : List α), element ∈ firstList ++ secondList →
      element ∈ firstList ∨ element ∈ secondList
  | [], _, memSecond => Or.inr memSecond
  | listHead :: firstRest, secondList, memBoth => by
      cases memBoth with
      | head => exact Or.inl (List.Mem.head firstRest)
      | tail _ memRest =>
          rcases listMemAppendInv firstRest secondList memRest with inFirst | inSecond
          · exact Or.inl (List.Mem.tail listHead inFirst)
          · exact Or.inr inSecond

/-- Membership in a map comes from a source element (hand-rolled). -/
theorem listMemMapInv {α β : Type} (mapped : α → β) {element : β} :
    ∀ (sourceList : List α), element ∈ sourceList.map mapped →
      ∃ source, source ∈ sourceList ∧ mapped source = element
  | [], memEmpty => nomatch memEmpty
  | listHead :: rest, memMapped => by
      cases memMapped with
      | head => exact ⟨listHead, List.Mem.head rest, rfl⟩
      | tail _ memRest =>
          obtain ⟨source, memSource, mappedEq⟩ := listMemMapInv mapped rest memRest
          exact ⟨source, List.Mem.tail listHead memSource, mappedEq⟩

/-! ## The enumeration -/

mutual
  /-- **All one-step reducts of a kernel term**: the root β/ι reduct when
  the cell is a root redex (`fireRootRedex`), plus every reassembly with
  one child stepped. -/
  def RawTerm.oneStepReducts : {scope : Nat} → RawTerm scope → List (RawTerm scope)
    | _, .mkGen generator payload children =>
        (match RawTerm.fireRootRedex generator payload children with
          | none => []
          | some rootReduct => [rootReduct])
        ++ (RawTermChildren.oneStepChildrenReducts children).map
            (fun steppedChildren => RawTerm.mkGen generator payload steppedChildren)

  /-- All one-position-stepped variants of a children spine: step the head
  (tail fixed) or step somewhere in the tail (head fixed). -/
  def RawTermChildren.oneStepChildrenReducts :
      {binderShifts : List Nat} → {parentScope : Nat} →
        RawTermChildren binderShifts parentScope →
        List (RawTermChildren binderShifts parentScope)
    | _, _, .childNil => []
    | _, _, .childCons head rest =>
        (RawTerm.oneStepReducts head).map
          (fun steppedHead => RawTermChildren.childCons steppedHead rest)
        ++ (RawTermChildren.oneStepChildrenReducts rest).map
            (fun steppedRest => RawTermChildren.childCons head steppedRest)
end

/-! ## ★ Soundness — every listed reduct is a genuine Step -/

mutual
  /-- ★ **Enumeration soundness**: every member of `oneStepReducts` is a
  genuine `Step` — the root part by `fireRootRedex_sound`, the mapped
  part by `Step.cong` over the spine soundness. -/
  theorem RawTerm.oneStepReducts_sound :
      ∀ {scope : Nat} (term : RawTerm scope) {reduct : RawTerm scope},
        reduct ∈ RawTerm.oneStepReducts term → Step term reduct
    | _, .mkGen generator payload children, reduct, memReduct => by
        rcases listMemAppendInv _ _ memReduct with memRoot | memMapped
        · split at memRoot
          · exact nomatch memRoot
          · next rootReduct fireEq =>
              cases memRoot with
              | head => exact RawTerm.fireRootRedex_sound fireEq
              | tail _ memEmpty => exact nomatch memEmpty
        · obtain ⟨steppedChildren, memChildren, reassembled⟩ :=
            listMemMapInv _ _ memMapped
          exact reassembled ▸ Step.cong generator payload
            (RawTermChildren.oneStepChildrenReducts_sound children memChildren)

  /-- Spine soundness: every listed children variant is a genuine
  `StepChildren` (head position via `here`, tail via `there`). -/
  theorem RawTermChildren.oneStepChildrenReducts_sound :
      ∀ {binderShifts : List Nat} {parentScope : Nat}
        (children : RawTermChildren binderShifts parentScope)
        {steppedSpine : RawTermChildren binderShifts parentScope},
        steppedSpine ∈ RawTermChildren.oneStepChildrenReducts children →
        StepChildren children steppedSpine
    | _, _, .childNil, _, memEmpty => nomatch memEmpty
    | _, _, .childCons head rest, _, memSpine => by
        rcases listMemAppendInv _ _ memSpine with memHead | memRest
        · obtain ⟨steppedHead, memStepped, reassembled⟩ := listMemMapInv _ _ memHead
          exact reassembled ▸ StepChildren.here rest
            (RawTerm.oneStepReducts_sound head memStepped)
        · obtain ⟨steppedRest, memStepped, reassembled⟩ := listMemMapInv _ _ memRest
          exact reassembled ▸ StepChildren.there head
            (RawTermChildren.oneStepChildrenReducts_sound rest memStepped)
end

/-! ## Non-vacuity — the enumeration computes -/

/-- The identity-β fixture `(λ. var 0) unit` at scope 0. -/
def identityBetaFixture : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_lam ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons
            (.mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil)
            .childNil)))
      (.childCons (.mkGen .gen_unit () .childNil) .childNil))

/-- **The enumeration computes**: the identity-β fixture has EXACTLY one
one-step reduct — the β-reduct `unit` — by kernel evaluation over the
generator table (root fires; every child is normal so the congruence
half is empty). -/
theorem identityBetaFixture_oneStepReducts :
    RawTerm.oneStepReducts identityBetaFixture
      = [.mkGen .gen_unit () .childNil] := rfl

end FX1Poly.Core
