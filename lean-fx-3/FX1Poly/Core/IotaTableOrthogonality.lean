import FX1Poly.Core.TableFireRoot

/-! # FX1Poly/Core/IotaTableOrthogonality — IOTA-T5: the orthogonality certificate

The kernel's whole β+ι fragment is an ORTHOGONAL rewrite system by
construction: every rule is a two-level left-linear pattern (eliminator
root + one constructor in one slot), and the rule keys
`(elimGenerator, primarySlot, primaryHead)` are pairwise distinct with
each eliminator using a single primary slot.  This file ships:

  * the decidable well-formedness checkers (`allRootKeysDistinct`,
    `allElimDetermineSlot`, `elimRootsAvoidScrutineeHeads`) and the
    bundled `WfIotaTable` predicate, with the canonical 21-row table's
    certificates closing by `rfl` — the permanent audit guard that
    re-decides on every new row;
  * the generic ROOT-DETERMINISM theorem: in a key-distinct,
    slot-coherent table, the first matching row's reduct is the ONLY
    reduct (`fireTableRedexOver_firstMatchIsCanonical`), so any two
    root firings of the same cell agree
    (`fireTableRedexOver_rootDeterministic`).  This is the
    generator-injectivity / sources-disjoint content that collapses the
    quadratic `cd_lemma` SameRoot/SourcesDisjoint arm matrix to ONE
    theorem.

## Zero-axiom verification

Own `listForall` Bool fold with its membership lemma (no `List.all`
simp dependence), `dite` over `DecidableEq` (enum / Nat / product — no
wildcard), `List.Mem` casing to distinguish a row from the list head
(no `DecidableEq IotaRuleDesc`, which the function-carrying descriptor
lacks), and the firing substrate's head-pinning.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated
per declaration in `FX1PolyAudit/AuditIotaTableOrthogonality.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## A controlled Bool fold over lists -/

/-- Every element satisfies `predicate` — own fold so the reduction and
its membership lemma stay under our control. -/
def listForall {elementType : Type} (predicate : elementType → Bool) :
    List elementType → Bool
  | [] => true
  | element :: rest => predicate element && listForall predicate rest

/-- Membership extraction from `listForall` — via `List.Mem` casing, so
no `DecidableEq` on the element type is needed. -/
theorem listForall_mem {elementType : Type} {predicate : elementType → Bool} :
    (entries : List elementType) → listForall predicate entries = true →
    {element : elementType} → element ∈ entries → predicate element = true
  | [], _, _, isMember => by cases isMember
  | head :: rest, allHold, element, isMember => by
      dsimp only [listForall] at allHold
      obtain ⟨headHolds, restHold⟩ := andEqTrueSplit allHold
      cases isMember with
      | head => exact headHolds
      | tail _ isInRest => exact listForall_mem rest restHold isInRest

/-! ## Row keys -/

/-- The primary scrutinee slot of a row (the single slot of its
left-linear pattern). -/
def IotaRuleDesc.primarySlot? (rule : IotaRuleDesc) : Option Nat :=
  rule.scrutinees.head?.map ScrutineeSpec.slot

/-- The primary scrutinee head of a row (the constructor required at the
primary slot). -/
def IotaRuleDesc.primaryHead? (rule : IotaRuleDesc) : Option Generator :=
  rule.scrutinees.head?.map ScrutineeSpec.head

/-- The root key: the data that uniquely identifies a left-linear root
pattern — eliminator head, primary slot, primary constructor head. -/
def IotaRuleDesc.rootKey (rule : IotaRuleDesc) :
    Generator × Option Nat × Option Generator :=
  (rule.elimGenerator, rule.primarySlot?, rule.primaryHead?)

/-! ## The decidable well-formedness checkers -/

/-- Two rows have distinct root keys. -/
def rowKeysDiffer (firstRule secondRule : IotaRuleDesc) : Bool :=
  if firstRule.rootKey = secondRule.rootKey then false else true

/-- All root keys in the table are pairwise distinct. -/
def allRootKeysDistinct : List IotaRuleDesc → Bool
  | [] => true
  | rule :: restRows =>
      listForall (rowKeysDiffer rule) restRows && allRootKeysDistinct restRows

/-- Two rows with the same eliminator use the same primary slot. -/
def elimDeterminesSlot (firstRule secondRule : IotaRuleDesc) : Bool :=
  if firstRule.elimGenerator = secondRule.elimGenerator then
    (if firstRule.primarySlot? = secondRule.primarySlot? then true else false)
  else true

/-- Every same-eliminator pair agrees on the primary slot. -/
def allElimDetermineSlot : List IotaRuleDesc → Bool
  | [] => true
  | rule :: restRows =>
      listForall (elimDeterminesSlot rule) restRows
        && allElimDetermineSlot restRows

/-- No eliminator root is itself a declared scrutinee head — the
elim-root ∩ scrutinee-head disjointness (a scrutinee is always a
constructor, never an eliminator). -/
def elimRootsAvoidScrutineeHeads (elimRoots : List Generator)
    (rule : IotaRuleDesc) : Bool :=
  listForall
    (fun scrutineeSpec =>
      listForall (fun elimRoot =>
        if scrutineeSpec.head = elimRoot then false else true) elimRoots)
    rule.scrutinees

/-- The elim-root list of a table. -/
def tableElimRoots (table : List IotaRuleDesc) : List Generator :=
  table.map IotaRuleDesc.elimGenerator

/-- Every row's scrutinee heads avoid every eliminator root. -/
def allElimRootsAvoidScrutineeHeads (table : List IotaRuleDesc) : Bool :=
  listForall (elimRootsAvoidScrutineeHeads (tableElimRoots table)) table

/-- Every row has a primary scrutinee (a non-empty left-linear pattern);
empty-pattern rows fire on every cell of their eliminator and would break
orthogonality even with distinct keys. -/
def allRowsHavePrimaryScrutinee (table : List IotaRuleDesc) : Bool :=
  listForall (fun rule => rule.primarySlot?.isSome) table

/-- ★ The decidable well-formed-orthogonal-table predicate: pairwise
distinct keys, same-eliminator-same-slot coherence, and elim/scrutinee
head disjointness.  Re-decides on every new row — the permanent guard. -/
structure WfIotaTable (table : List IotaRuleDesc) : Prop where
  keysAreDistinct : allRootKeysDistinct table = true
  elimDeterminesSlots : allElimDetermineSlot table = true
  elimRootsAvoidHeads : allElimRootsAvoidScrutineeHeads table = true
  rowsHavePrimaryScrutinee : allRowsHavePrimaryScrutinee table = true

/-! ## The canonical-table certificate (the audit guard) -/

/-- ★ The canonical 21-row table is a well-formed orthogonal table —
every check closes by `rfl`-decidable enumeration. -/
theorem iotaRuleTable_isWf : WfIotaTable iotaRuleTable :=
  { keysAreDistinct := rfl
    elimDeterminesSlots := rfl
    elimRootsAvoidHeads := rfl
    rowsHavePrimaryScrutinee := rfl }

/-! ## Head pinning: a firing row forces its primary slot's head -/

/-- A passing scrutinee-spec test forces the spine slot to hold a cell
whose head is exactly the declared head (the payload/children are
surfaced as witnesses). -/
theorem IotaRuleDesc.scrutineeSpecFires_slotHoldsHead {rule : IotaRuleDesc}
    {scope : Nat}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {spec : ScrutineeSpec}
    (specFires : rule.scrutineeSpecFires spine spec = true) :
    ∃ (matchedPayload : spec.head.payload scope)
      (matchedChildren : RawTermChildren spec.head.binderShifts scope),
      (scopedChildAt? spine.toScopedChildren spec.slot).bind
          ScopedChild.atShiftZero?
        = some (.mkGen spec.head matchedPayload matchedChildren) := by
  match slotLookup : (scopedChildAt? spine.toScopedChildren spec.slot).bind
      ScopedChild.atShiftZero? with
  | none =>
      exfalso
      dsimp only [IotaRuleDesc.scrutineeSpecFires] at specFires
      rw [slotLookup] at specFires
      exact Bool.noConfusion specFires
  | some (.mkGen slotGenerator slotPayload slotChildren) =>
      have isDeclaredHead : slotGenerator = spec.head :=
        rule.scrutineeSpecFires_extractsHead specFires slotLookup
      subst isDeclaredHead
      exact ⟨slotPayload, slotChildren, rfl⟩

/-- A root firing forces the cell's primary slot to hold the row's
primary head — stated about the raw children `c` for the FIRST scrutinee
spec (the eliminator coercion vanishes after the head is fixed; the
first spec's firing is the `.1` of the pattern conjunction, so this
holds for any non-empty scrutinee list, matching `primaryHead?`). -/
theorem IotaRuleDesc.fireAtRoot?_pinsPrimaryHead {rule : IotaRuleDesc}
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope} {primarySpec : ScrutineeSpec}
    {restSpecs : List ScrutineeSpec}
    (specShape : rule.scrutinees = primarySpec :: restSpecs)
    (fire : rule.fireAtRoot? generator payload children = some reduct) :
    ∃ (matchedPayload : primarySpec.head.payload scope)
      (matchedChildren : RawTermChildren primarySpec.head.binderShifts scope),
      (scopedChildAt? children.toScopedChildren primarySpec.slot).bind
          ScopedChild.atShiftZero?
        = some (.mkGen primarySpec.head matchedPayload matchedChildren) := by
  dsimp only [IotaRuleDesc.fireAtRoot?] at fire
  by_cases isElimHead : generator = rule.elimGenerator
  case pos =>
      subst isElimHead
      rw [dif_pos rfl] at fire
      have allFire := rule.firesOn?_some_scrutineesFire fire
      rw [specShape] at allFire
      dsimp only [IotaRuleDesc.scrutineesFire] at allFire
      have specFires : rule.scrutineeSpecFires children primarySpec = true :=
        (andEqTrueSplit allFire).1
      exact rule.scrutineeSpecFires_slotHoldsHead specFires
  case neg =>
      rw [dif_neg isElimHead] at fire
      injection fire

/-- A root firing pins the eliminator head: the cell's generator IS the
row's eliminator. -/
theorem IotaRuleDesc.fireAtRoot?_pinsElim {rule : IotaRuleDesc}
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fire : rule.fireAtRoot? generator payload children = some reduct) :
    generator = rule.elimGenerator := by
  dsimp only [IotaRuleDesc.fireAtRoot?] at fire
  by_cases isElimHead : generator = rule.elimGenerator
  case pos => exact isElimHead
  case neg =>
      rw [dif_neg isElimHead] at fire
      injection fire

/-- A row whose primary slot is present has a non-empty (cons-shaped)
scrutinee list whose head is the primary spec — the clean extraction the
determinism theorem consumes (non-emptiness comes from the well-formed
table's `allRowsHavePrimaryScrutinee`, NOT from the firing). -/
theorem IotaRuleDesc.consScrutineesOfPrimarySome {rule : IotaRuleDesc}
    (primaryPresent : rule.primarySlot?.isSome = true) :
    ∃ (primarySpec : ScrutineeSpec) (restSpecs : List ScrutineeSpec),
      rule.scrutinees = primarySpec :: restSpecs
      ∧ rule.primarySlot? = some primarySpec.slot
      ∧ rule.primaryHead? = some primarySpec.head := by
  dsimp only [IotaRuleDesc.primarySlot?] at primaryPresent
  cases scrutineesShape : rule.scrutinees with
  | cons primarySpec restSpecs =>
      refine ⟨primarySpec, restSpecs, rfl, ?_, ?_⟩
      · dsimp only [IotaRuleDesc.primarySlot?]
        rw [scrutineesShape]
        rfl
      · dsimp only [IotaRuleDesc.primaryHead?]
        rw [scrutineesShape]
        rfl
  | nil =>
      rw [scrutineesShape] at primaryPresent
      exact Bool.noConfusion primaryPresent

/-! ## Pairwise extraction from the distinctness checkers -/

/-- Key distinctness forces VALUE equality: two member rows with the
same root key are the same row (a duplicated value would already
violate pairwise distinctness). -/
theorem allRootKeysDistinct_memUnique :
    (table : List IotaRuleDesc) → allRootKeysDistinct table = true →
    {firstRule secondRule : IotaRuleDesc} →
    firstRule ∈ table → secondRule ∈ table →
    firstRule.rootKey = secondRule.rootKey →
    firstRule = secondRule
  | [], _, _, _, firstIsRow, _, _ => by cases firstIsRow
  | headRule :: restRows, distinct, firstRule, secondRule,
      firstIsRow, secondIsRow, keysAgree => by
      dsimp only [allRootKeysDistinct] at distinct
      obtain ⟨headDiffers, restDistinct⟩ := andEqTrueSplit distinct
      cases firstIsRow with
      | head =>
          cases secondIsRow with
          | head => rfl
          | tail _ secondInRest =>
              exfalso
              have differs :=
                listForall_mem restRows headDiffers secondInRest
              dsimp only [rowKeysDiffer] at differs
              rw [if_pos keysAgree] at differs
              exact Bool.noConfusion differs
      | tail _ firstInRest =>
          cases secondIsRow with
          | head =>
              exfalso
              have differs :=
                listForall_mem restRows headDiffers firstInRest
              dsimp only [rowKeysDiffer] at differs
              rw [if_pos keysAgree.symm] at differs
              exact Bool.noConfusion differs
          | tail _ secondInRest =>
              exact allRootKeysDistinct_memUnique restRows restDistinct
                firstInRest secondInRest keysAgree

/-- Slot coherence, pairwise: two member rows on the same eliminator
agree on the primary slot. -/
theorem allElimDetermineSlot_pairwise :
    (table : List IotaRuleDesc) → allElimDetermineSlot table = true →
    {firstRule secondRule : IotaRuleDesc} →
    firstRule ∈ table → secondRule ∈ table →
    firstRule.elimGenerator = secondRule.elimGenerator →
    firstRule.primarySlot? = secondRule.primarySlot?
  | [], _, _, _, firstIsRow, _, _ => by cases firstIsRow
  | headRule :: restRows, coherent, firstRule, secondRule,
      firstIsRow, secondIsRow, sameElim => by
      dsimp only [allElimDetermineSlot] at coherent
      obtain ⟨headCoheres, restCoherent⟩ := andEqTrueSplit coherent
      cases firstIsRow with
      | head =>
          cases secondIsRow with
          | head => rfl
          | tail _ secondInRest =>
              have coheres :=
                listForall_mem restRows headCoheres secondInRest
              dsimp only [elimDeterminesSlot] at coheres
              rw [if_pos sameElim] at coheres
              by_cases slotsAgree :
                  headRule.primarySlot? = secondRule.primarySlot?
              case pos => exact slotsAgree
              case neg =>
                  rw [if_neg slotsAgree] at coheres
                  exact Bool.noConfusion coheres
      | tail _ firstInRest =>
          cases secondIsRow with
          | head =>
              have coheres :=
                listForall_mem restRows headCoheres firstInRest
              dsimp only [elimDeterminesSlot] at coheres
              rw [if_pos sameElim.symm] at coheres
              by_cases slotsAgree :
                  headRule.primarySlot? = firstRule.primarySlot?
              case pos => exact slotsAgree.symm
              case neg =>
                  rw [if_neg slotsAgree] at coheres
                  exact Bool.noConfusion coheres
          | tail _ secondInRest =>
              exact allElimDetermineSlot_pairwise restRows restCoherent
                firstInRest secondInRest sameElim

/-! ## Root determinism — the keystone

Two co-firing member rows of a well-formed table share the cell's
eliminator (head pin), hence the primary slot (slot coherence), hence
the slot's constructor head (the firing forces it), hence the whole
root KEY — which key-distinctness only permits for the SAME row, whose
`firesOn?` is a function.  This is the generator-injectivity /
sources-disjoint content that collapses the quadratic `cd_lemma`
SameRoot/SourcesDisjoint arm matrix to ONE theorem. -/

/-- ★ **Root-firing determinism**: any two rows of a well-formed table
that both fire on the same raw cell produce the SAME reduct. -/
theorem WfIotaTable.rootFiringDeterministic {table : List IotaRuleDesc}
    (tableIsWf : WfIotaTable table)
    {firstRule secondRule : IotaRuleDesc}
    (firstIsRow : firstRule ∈ table) (secondIsRow : secondRule ∈ table)
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {firstReduct secondReduct : RawTerm scope}
    (firstFire :
      firstRule.fireAtRoot? generator payload children = some firstReduct)
    (secondFire :
      secondRule.fireAtRoot? generator payload children
        = some secondReduct) :
    firstReduct = secondReduct := by
  -- both rows eliminate the cell's head
  have elimsAgree :
      firstRule.elimGenerator = secondRule.elimGenerator :=
    (firstRule.fireAtRoot?_pinsElim firstFire).symm.trans
      (secondRule.fireAtRoot?_pinsElim secondFire)
  -- both rows have a primary scrutinee
  obtain ⟨firstSpec, firstRest, firstShape, firstSlotEq, firstHeadEq⟩ :=
    firstRule.consScrutineesOfPrimarySome
      (listForall_mem table tableIsWf.rowsHavePrimaryScrutinee firstIsRow)
  obtain ⟨secondSpec, secondRest, secondShape, secondSlotEq,
      secondHeadEq⟩ :=
    secondRule.consScrutineesOfPrimarySome
      (listForall_mem table tableIsWf.rowsHavePrimaryScrutinee
        secondIsRow)
  -- same eliminator forces the same primary slot
  have primarySlotsAgree :
      firstRule.primarySlot? = secondRule.primarySlot? :=
    allElimDetermineSlot_pairwise table tableIsWf.elimDeterminesSlots
      firstIsRow secondIsRow elimsAgree
  have slotsAgree : firstSpec.slot = secondSpec.slot :=
    Option.some.inj
      (firstSlotEq.symm.trans (primarySlotsAgree.trans secondSlotEq))
  -- both firings pin the SAME slot's constructor head
  obtain ⟨firstPayload, firstChildren, firstLookup⟩ :=
    firstRule.fireAtRoot?_pinsPrimaryHead firstShape firstFire
  obtain ⟨secondPayload, secondChildren, secondLookup⟩ :=
    secondRule.fireAtRoot?_pinsPrimaryHead secondShape secondFire
  rw [slotsAgree] at firstLookup
  have cellsAgree :=
    Option.some.inj (firstLookup.symm.trans secondLookup)
  have headsAgree : firstSpec.head = secondSpec.head :=
    congrArg
      (fun cell => match cell with
        | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
      cellsAgree
  -- the whole root keys agree
  have keysAgree : firstRule.rootKey = secondRule.rootKey := by
    show (firstRule.elimGenerator, firstRule.primarySlot?,
        firstRule.primaryHead?)
      = (secondRule.elimGenerator, secondRule.primarySlot?,
        secondRule.primaryHead?)
    rw [elimsAgree, primarySlotsAgree, firstHeadEq, secondHeadEq,
      headsAgree]
  -- distinct keys force the same row; firesOn? is a function
  have rulesAgree : firstRule = secondRule :=
    allRootKeysDistinct_memUnique table tableIsWf.keysAreDistinct
      firstIsRow secondIsRow keysAgree
  subst rulesAgree
  exact Option.some.inj (firstFire.symm.trans secondFire)

/-- The table walk's result is canonical: whatever reduct the walk
returns equals ANY member row's firing reduct — row order is
irrelevant in a well-formed table. -/
theorem WfIotaTable.fireTableRedexOver_eq_ofRowFires
    {table : List IotaRuleDesc} (tableIsWf : WfIotaTable table)
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {firingRule : IotaRuleDesc} (firingIsRow : firingRule ∈ table)
    {reduct : RawTerm scope}
    (rowFire :
      firingRule.fireAtRoot? generator payload children = some reduct) :
    (rows : List IotaRuleDesc) →
    (rowsAreInTable : ∀ rule, rule ∈ rows → rule ∈ table) →
    {walkReduct : RawTerm scope} →
    fireTableRedexOver rows generator payload children = some walkReduct →
    walkReduct = reduct
  | [], _, _, walkEq => by
      dsimp only [fireTableRedexOver] at walkEq
      injection walkEq
  | headRule :: restRows, rowsAreInTable, walkReduct, walkEq => by
      dsimp only [fireTableRedexOver] at walkEq
      match headFireEq : headRule.fireAtRoot? generator payload children with
      | some headReduct =>
          rw [headFireEq] at walkEq
          obtain rfl := Option.some.inj walkEq
          exact tableIsWf.rootFiringDeterministic
            (rowsAreInTable headRule (.head _)) firingIsRow
            headFireEq rowFire
      | none =>
          rw [headFireEq] at walkEq
          exact tableIsWf.fireTableRedexOver_eq_ofRowFires firingIsRow
            rowFire restRows
            (fun rule isInRest => rowsAreInTable rule (.tail _ isInRest))
            walkEq

/-- A row's `fireAtRoot?` at its OWN eliminator is exactly its
`firesOn?` (the generator-equality transport vanishes at `rfl`) — the
lift the T6 root-overlap consumer uses to route `tableRedex` firings
through the determinism theorem. -/
theorem IotaRuleDesc.fireAtRoot?_atOwnElim (rule : IotaRuleDesc)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    rule.fireAtRoot? rule.elimGenerator elimPayload spine
      = rule.firesOn? elimPayload spine := by
  dsimp only [IotaRuleDesc.fireAtRoot?]
  rw [dif_pos rfl]

end FX1Poly.Core
