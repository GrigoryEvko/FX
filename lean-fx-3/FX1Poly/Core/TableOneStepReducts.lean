import FX1Poly.Core.IotaTableHonesty

/-! # TableOneStepReducts — IOTA-T9: the exact table reduct enumeration

The fourth consumer-migration brick: the one-step reduct enumeration
re-based onto the table walk — and STRENGTHENED.  The bespoke
`RawTerm.oneStepReducts` ships soundness only (its completeness was
deferred to a future brick); the table enumeration ships BOTH directions,
because the table substrate already holds the freed-subject inversion
(IOTA-T7) and root-firing determinism (IOTA-T5):

  * soundness — every listed term is a genuine `StepOverTable` step;
  * **completeness (well-formed tables)** — every `StepOverTable` step
    is listed: a root firing must agree with the walk's firing by
    determinism, and a child congruence is listed by the spine
    induction.

Together: `oneStepReductsOverTable` is the EXACT reduct set of the
table relation — the substrate the worst-case cost bound folds over,
now with the missing half of its spec.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableOneStepReducts.lean`. -/

namespace FX1Poly.Core

/-! ## Forward membership helpers (hand-rolled, explicit `List.Mem`) -/

/-- Membership in the right part of an append (hand-rolled; the core
lemma's axiom status is unaudited). -/
theorem listMemAppendRight {entryType : Type} {entry : entryType}
    {backEntries : List entryType} :
    (frontEntries : List entryType) → entry ∈ backEntries →
    entry ∈ frontEntries ++ backEntries
  | [], isMember => isMember
  | frontHead :: frontRest, isMember =>
      .tail frontHead (listMemAppendRight frontRest isMember)

/-- Mapped membership (hand-rolled). -/
theorem listMemMapForward {sourceType targetType : Type}
    (mapped : sourceType → targetType) {source : sourceType} :
    {sourceList : List sourceType} → source ∈ sourceList →
    mapped source ∈ sourceList.map mapped
  | _, .head rest => .head (rest.map mapped)
  | _, .tail listHead memRest =>
      .tail (mapped listHead) (listMemMapForward mapped memRest)

/-! ## The enumeration -/

mutual

/-- **All one-step table reducts**: the walk's root reduct when some row
fires, plus every reassembly of the cell with ONE child stepped. -/
def oneStepReductsOverTable (table : List IotaRuleDesc) {scope : Nat}
    (term : RawTerm scope) : List (RawTerm scope) :=
  match term with
  | .mkGen generator payload children =>
      (match fireTableRedexOver table generator payload children with
        | none => []
        | some rootReduct => [rootReduct])
      ++ (oneStepChildrenReductsOverTable table children).map
          (fun steppedChildren =>
            RawTerm.mkGen generator payload steppedChildren)

/-- All one-position-stepped variants of a children spine: step the head
(tail fixed) or step somewhere in the tail (head fixed). -/
def oneStepChildrenReductsOverTable (table : List IotaRuleDesc)
    {binderShifts : List Nat} {parentScope : Nat}
    (children : RawTermChildren binderShifts parentScope) :
    List (RawTermChildren binderShifts parentScope) :=
  match binderShifts, children with
  | _, .childNil => []
  | _, .childCons head rest =>
      (oneStepReductsOverTable table head).map
        (fun steppedHead => RawTermChildren.childCons steppedHead rest)
      ++ (oneStepChildrenReductsOverTable table rest).map
          (fun steppedRest => RawTermChildren.childCons head steppedRest)

end

/-! ## Soundness -/

mutual

/-- ★ **Enumeration soundness**: every listed term is a genuine table
step — the root part by the walk soundness, the mapped part by
congruence over the spine soundness. -/
theorem oneStepReductsOverTable_sound {table : List IotaRuleDesc} :
    ∀ {scope : Nat} (term : RawTerm scope) {reduct : RawTerm scope},
      reduct ∈ oneStepReductsOverTable table term →
      StepOverTable table term reduct
  | _, .mkGen generator payload children, reduct, memReduct => by
      rcases listMemAppendInv _ _ memReduct with memRoot | memMapped
      · split at memRoot
        · exact nomatch memRoot
        · next rootReduct fireEq =>
            cases memRoot with
            | head =>
                exact fireTableRedexOver_sound table (fun _ isRow => isRow)
                  fireEq
            | tail _ memEmpty => exact nomatch memEmpty
      · obtain ⟨steppedChildren, memChildren, reassembled⟩ :=
          listMemMapInv _ _ memMapped
        exact reassembled ▸ StepOverTable.cong generator payload
          (oneStepChildrenReductsOverTable_sound children memChildren)

/-- Spine soundness: every listed children variant is a genuine
`StepOverTableChildren`. -/
theorem oneStepChildrenReductsOverTable_sound {table : List IotaRuleDesc} :
    ∀ {binderShifts : List Nat} {parentScope : Nat}
      (children : RawTermChildren binderShifts parentScope)
      {steppedSpine : RawTermChildren binderShifts parentScope},
      steppedSpine ∈ oneStepChildrenReductsOverTable table children →
      StepOverTableChildren table children steppedSpine
  | _, _, .childNil, _, memEmpty => nomatch memEmpty
  | _, _, .childCons head rest, _, memSpine => by
      rcases listMemAppendInv _ _ memSpine with memHead | memRest
      · obtain ⟨steppedHead, memStepped, reassembled⟩ :=
          listMemMapInv _ _ memHead
        exact reassembled ▸ StepOverTableChildren.here rest
          (oneStepReductsOverTable_sound head memStepped)
      · obtain ⟨steppedRest, memStepped, reassembled⟩ :=
          listMemMapInv _ _ memRest
        exact reassembled ▸ StepOverTableChildren.there head
          (oneStepChildrenReductsOverTable_sound rest memStepped)

end

/-! ## ★ Completeness — the half the bespoke enumeration deferred -/

mutual

/-- ★ **Enumeration completeness over a well-formed table**: every table
step is listed.  A root firing must produce the SAME reduct as the
walk's firing (T5 root determinism), so it sits in the root singleton; a
child congruence is listed through the spine induction and the map. -/
theorem oneStepReductsOverTable_complete {table : List IotaRuleDesc}
    (tableIsWf : WfIotaTable table) :
    ∀ {scope : Nat} {term reduct : RawTerm scope},
      StepOverTable table term reduct →
      reduct ∈ oneStepReductsOverTable table term
  | scope, .mkGen generator payload children, reduct, tableStep => by
      dsimp only [oneStepReductsOverTable]
      cases tableStep.invertOrCong rfl with
      | inl rootFiring =>
          obtain ⟨rule, isRow, elimPayload, spine, cellEq, fires⟩ :=
            rootFiring
          have atRoot : rule.fireAtRoot? generator payload children
              = some reduct :=
            rule.firesOn?_toFireAtRootAtCell cellEq fires
          have walkFires := fireTableRedexOver_complete atRoot table isRow
          match walkEq : fireTableRedexOver table generator payload
              children with
          | none =>
              rw [walkEq] at walkFires
              exact Bool.noConfusion walkFires
          | some walkReduct =>
              obtain ⟨walkRule, walkIsRow, walkRuleFires⟩ :=
                fireTableRedexOver_someInversion table walkEq
              have reductsAgree : walkReduct = reduct :=
                tableIsWf.rootFiringDeterministic walkIsRow isRow
                  walkRuleFires atRoot
              rw [reductsAgree]
              exact .head _
      | inr congShape =>
          obtain ⟨steppedChildren, reductShape, childrenStep⟩ := congShape
          subst reductShape
          exact listMemAppendRight _
            (listMemMapForward _
              (oneStepChildrenReductsOverTable_complete tableIsWf
                childrenStep))

/-- Spine completeness: every children step is listed (head position in
the left map, tail position in the right map). -/
theorem oneStepChildrenReductsOverTable_complete {table : List IotaRuleDesc}
    (tableIsWf : WfIotaTable table) :
    ∀ {binderShifts : List Nat} {parentScope : Nat}
      {children steppedSpine : RawTermChildren binderShifts parentScope},
      StepOverTableChildren table children steppedSpine →
      steppedSpine ∈ oneStepChildrenReductsOverTable table children
  | _, _, _, _, .here rest headStep => by
      dsimp only [oneStepChildrenReductsOverTable]
      exact listMemAppendLeft _
        (listMemMapForward _
          (oneStepReductsOverTable_complete tableIsWf headStep))
  | _, _, _, _, .there head restStep => by
      dsimp only [oneStepChildrenReductsOverTable]
      exact listMemAppendRight _
        (listMemMapForward _
          (oneStepChildrenReductsOverTable_complete tableIsWf restStep))

end

/-! ## The canonical 21-row instantiation -/

/-- The canonical exact reduct enumeration. -/
def StepTable.oneStepReducts {scope : Nat} (term : RawTerm scope) :
    List (RawTerm scope) :=
  oneStepReductsOverTable iotaRuleTable term

/-- Canonical soundness. -/
theorem StepTable.oneStepReducts_sound {scope : Nat}
    {term reduct : RawTerm scope}
    (memReduct : reduct ∈ StepTable.oneStepReducts term) :
    StepTable term reduct :=
  oneStepReductsOverTable_sound term memReduct

/-- ★ Canonical completeness — certificates by the shipped pins.  The
canonical enumeration is EXACT: `reduct ∈ oneStepReducts term ↔
StepTable term reduct`. -/
theorem StepTable.oneStepReducts_complete {scope : Nat}
    {term reduct : RawTerm scope} (tableStep : StepTable term reduct) :
    reduct ∈ StepTable.oneStepReducts term :=
  oneStepReductsOverTable_complete iotaRuleTable_isWf tableStep

/-- **The enumeration computes**: the identity-β fixture has exactly the
β-reduct, through the table walk. -/
theorem identityBetaFixture_tableOneStepReducts :
    StepTable.oneStepReducts
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons (.mkGen .gen_unit () .childNil)
              (.childCons
                (.mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1)
                  .childNil)
                .childNil)))
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)))
      = [.mkGen .gen_unit () .childNil] := rfl

end FX1Poly.Core
